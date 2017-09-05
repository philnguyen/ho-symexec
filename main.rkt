#lang racket/base

(require racket/match
         racket/set
         racket/syntax
         racket/list
         redex
         "helper.rkt")

(define-extended-language λs λ0
  
  ;; Syntax
  [#|Expressions|# e ::= v x (e e ...) (if0 e e e)]
  [#|Literals   |# v ::= n o (λ (x) e) (• ℓ)]
  [#|Primitives |# o ::= p add1 car cdr cons]
  [#|Predicates |# p ::= integer? procedure? pair? zero?]
  [#|Integers   |# n ::= integer]
  [#|Hole Labels|# ℓ ::= any]
  [#|Variables  |# x ::= variable-not-otherwise-mentioned]
  
  ;; Semantics presented in Calculus of explicit substitutions,
  ;; which is basically reduction-semantics with environments instead of substitution.
  ;;
  ;; Some non-standard things:
  ;; - Path-condition (φ) maps each symbolic name (ℓ) to an abstract value (U) that is its upperbound
  ;; - Call history (Ξ) remembers application contexts (arguments × path-condition) for each function
  ;;   up to renaming of symbolic names
  ;; - Continuations/contexts/stacks (ℰ) are chunked at function boundaries and allocated in
  ;;   continuation store (σₖ) to abstract the state space
  [#|States        |# ς  ::= (E φ σ σₖ Ξ)]
  [#|Environments  |# ρ  ::= (side-condition (name ρ  any) (hash? (term ρ)))] ; x → α
  [#|Value Stores  |# σ  ::= (side-condition (name σ  any) (hash? (term σ)))] ; α → ℘(V)
  [#|Stack Stores  |# σₖ ::= (side-condition (name σₖ any) (hash? (term σₖ)))] ; αₖ → ℘(ℰ)
  [#|Path. cond.   |# φ  ::= (side-condition (name φ any) (hash? (term φ)))] ; ℓ → U
  [#|Call History  |# Ξ  ::= (side-condition (name Ξ  any) (hash? (term Ξ)))] ; V → ℘(V… × φ)
  [#|Closures      |# E  ::= A (e ρ) (E E ...) (if0 E E E) (rt αₖ m E)]
  [#|Eval. Contexts|# ℰ  ::= hole (V ... ℰ E ...) (if0 ℰ E E) (rt αₖ m ℰ)]
  [#|Answers       |# A  ::= V (err any)]
  [#|Absrt. Values |# U  ::= n o (Pair α α) (Clo x e ρ) (● any)] ; concrete + abstract values
  [#|Values        |# V  ::= U (• ℓ)]                            ; concrete + asbtract + symbolic values
  [#|Renamings     |# m  ::= ([ℓ ↔ ℓ] ...)] ; renaming betweeen caller ↔ callee
  [#|Value Addrs   |# α  ::= any]
  [#|Stack Addrs   |# αₖ ::= any] ; ≃ (V × V… × φ)
  )

(define-syntax-rule (ev e) (apply-reduction-relation* -> (term (inj e)) #:cache-all? #t))
(define-syntax-rule (viz e) (traces -> (term (inj e))))

(define (uk? x) (or (redex-match? λs (● _) x) (redex-match? λs (• _) x)))

(define-metafunction λs
  inj : e -> ς
  [(inj e) ((e ,(hash)) ,(hash) ,(hash) ,(hash) ,(hash))])

(define ->
  ;; Main reduction relation on states
  (reduction-relation
   λs #:domain ς
   ;; Intra-procedural rules
   [--> ((in-hole ℰ E_1) φ_1 σ_1 σₖ Ξ)
        ((in-hole ℰ E_2) φ_2 σ_2 σₖ Ξ)
        (computed-name (term any_name))
        (where {_ ... (any_name (E_2 φ_2 σ_2)) _ ...}
               ,(apply-reduction-relation/tag-with-names ->v (term (E_1 φ_1 σ_1))))]
   
   ;; Apply Lambda
   ;; Before application, look up `Ξ` to see if an identical application
   ;; (up to renaming of symbolic values) has happened
   [--> ((in-hole ℰ ((Clo x e ρ) V)) φ   σ   σₖ   Ξ  )
        ((rt αₖ m (e ρ_1))           φ_1 σ_1 σₖ_1 Ξ_1)
        App-Clo
        ;; (fairly) standard
        (where α  (alloc x V φ))
        (where ρ_1 (ext ρ [x ↦ α]))
        ;; figure-out abstract stack-address by inspecting history of calls to (Clo ...)
        (where (αₖ m Ξ_1 (V_1) φ_1) (allocₖ Ξ (Clo x e ρ) (V) φ))
        (where σ_1 (⊔ σ [α ↦ V_1]))
        (where σₖ_1 (⊔ σₖ [αₖ ↦ ℰ]))]

   ;; Returning
   ;; Rename if neccesary
   [--> ((rt αₖ m   V  ) φ   σ σₖ Ξ)
        ((in-hole ℰ V_1) φ_1 σ σₖ Ξ)
        Rt
        (where V_1 (rename-V (invert m) V))
        (where φ_1 (rename-φ (invert m) φ))
        (judgment-holds (lookup σₖ αₖ ℰ))]
   ))

(define ->v
  ;; Factored out intra-procedural reduction rules
  (reduction-relation
   λs #:domain (E φ σ)
   ;; Simple cases
   [--> ((e ρ) φ   σ)
        (E     φ_1 σ)
        Simp
        (judgment-holds (->₁ e ρ φ σ E φ_1))]

   ;; Conditionals
   [--> ((if0 V E _) φ   σ)
        (E           φ_1 σ)
        If-T
        (judgment-holds (δ σ φ zero? (V) 0 φ_1 _))]
   [--> ((if0 V _ E) φ  σ)
        (E           φ_1 σ)
        If-F
        (judgment-holds (δ σ φ zero? (V) 1 φ_1 _))]

   ;; Primitive applications
   [--> ((o V ...) φ   σ  )
        (A         φ_1 σ_1)
        App-Prim
        (judgment-holds (δ σ φ o (V ...) A φ_1 σ_1))]

   ;; Erroneous application
   [--> ((V _ ...)                  φ   σ)
        ((err "apply non-function") φ_1 σ)
        App-Err
        (judgment-holds (δ σ φ procedure? (V) 1 φ_1 _))]

   ;; Symbolic function application
   [--> (((• ℓ) V) φ   σ)
        ((• ℓ_1)   φ_1 σ)
        App-Opq
        (judgment-holds (δ σ φ procedure? ((• ℓ)) 0 φ_1 _))
        (where ℓ_1 (gen-ℓ ℓ V))]
   [--> (((• ℓ) V)         φ   σ)
        ((• ℓ) (V (• ℓ_1)) φ_2 σ)
        App-Havoc
        (judgment-holds (δ σ φ   procedure? ((• ℓ)) 0 φ_1 _))
        (judgment-holds (δ σ φ_1 procedure? (V)     0 φ_2 _))
        (where ℓ_1 (gen-ℓ arg ℓ V))]
   ))

(define-judgment-form λs
  ;; Simple reduction:
  ;; - distribute environment into sub-expressions
  ;; - look up variables
  ;; - evaluate literals
  #:contract (->₁ e ρ φ σ E φ)
  #:mode     (->₁ I I I I O O)
  [-------------------------------------------------------------"Num"
   (->₁ n _ φ _ n φ)]
  [-------------------------------------------------------------"Op"
   (->₁ o _ φ _ o φ)]
  [-------------------------------------------------------------"Lam"
   (->₁ (λ (x) e) ρ φ _ (Clo x e ρ) φ)]
  [-------------------------------------------------------------"Sym"
   (->₁ (• ℓ) _ φ _ (• ℓ) (ext φ [ℓ ↦ (● ,(set))]))]
  [(lookup σ ,(hash-ref (term ρ) (term x)) V)
   -------------------------------------------------------------"Var"
   (->₁ x ρ φ σ V φ)]
  [(->₁ e   ρ φ   σ E   φ_0)
   (->₁ e_1 ρ φ_0 σ E_1 φ_1)
   -------------------------------------------------------------"App-1"
   (->₁ (e e_1) ρ φ σ (E E_1) φ_1)]
  [(->₁ e   ρ φ   σ E   φ_0)
   (->₁ e_1 ρ φ_0 σ E_1 φ_1)
   (->₁ e_2 ρ φ_1 σ E_2 φ_2)
   -------------------------------------------------------------"App-2"
   (->₁ (e e_1 e_2) ρ φ σ (E E_1 E_2) φ_2)]
  [(->₁ e   ρ φ   σ E   φ_0)
   (->₁ e_1 ρ φ_0 σ E_1 φ_1)
   (->₁ e_2 ρ φ_1 σ E_2 φ_2)
   -------------------------------------------------------------"If"
   (->₁ (if0 e e_1 e_2) ρ φ σ (if0 E E_1 E_2) φ_2)])


(define-metafunction λs
  alloc : x V φ -> α
  [(alloc x V φ)
   ;; TODO this does not guarantee termination
   ,(format-symbol "~a_~a" (term x) (intern (term x) (term V)))])

(define-metafunction λs
  allocₖ : Ξ V (V ...) φ -> (αₖ m Ξ (V ...) φ)
  ;; If identical application has happened, return old application plus renaming information
  [(allocₖ Ξ V_f (V_x ...) φ)
   (,(format-symbol "κ_~a" (intern 'κ (term (V_f V_x0 ... φ_0)))) m Ξ (V_x0 ...) φ_0)
   (judgment-holds (lookup Ξ V_f ((V_x0 ...) φ_0)))
   (judgment-holds (unify (V_x ... φ) (V_x0 ... φ_0) m))]
  ;; If application is new, add to `Ξ`
  [(allocₖ Ξ V_f (V_x ...) φ)
   (,(format-symbol "κ_~a" (intern 'κ (term (V_f V_x ... φ)))) () (⊔ Ξ [V_f ↦ ((V_x ...) φ)]) (V_x ...) φ)])

(define-judgment-form λs
  ;; Unification of argument sequences and path-conditions
  #:contract (unify (V ... φ) (V ... φ) m)
  #:mode     (unify I         I         O)
  [(unify-V* () (V_1 ...) (V_2 ...) m)
   (unify-φ? m φ_1 φ_2)
   -------------------------------------------------------------
   (unify (V_1 ... φ_1) (V_2 ... φ_2) m)])

(define-judgment-form λs
  ;; Unification of value sequences
  #:contract (unify-V* m (V ...) (V ...) m)
  #:mode     (unify-V* I I       I       O)
  [(unify-V* m () () m)]
  [(unify-V m V_1 V_2 m_1)
   (unify-V* m_1 (V_1* ...) (V_2* ...) m_2)
   -------------------------------------------------------------
   (unify-V* m (V_1 V_1* ...) (V_2 V_2* ...) m_2)])

(define-judgment-form λs
  ;; Unification of values
  #:contract (unify-V m V V m)
  #:mode     (unify-V I I I O)
  [(unify-V m V V m)]
  [(where {_ ... [ℓ_1 ↔ ℓ_2] _ ...} m)
   -------------------------------------------------------------
   (unify-V m (• ℓ_1) (• ℓ_2) m)]
  [(side-condition ,(not (equal? (term ℓ_1) (term ℓ_2)))) ; avoid duplicating trivial case
   (where {[ℓ_1* ↔ ℓ_2*] ...} m)
   (side-condition ,(not (member (term ℓ_1) (term (ℓ_1* ...)))))
   (side-condition ,(not (member (term ℓ_2) (term (ℓ_2* ...)))))
   -------------------------------------------------------------
   (unify-V m (• ℓ_1) (• ℓ_2) m)])

(define-relation λs
  ;; Check if `φ_1` restricted to `{ℓ_1 ...}` and `φ_2` restricted to {ℓ_2 ...} are identical
  ;; up to renaming {[ℓ_1 ↔ ℓ_2] ...}
  unify-φ? ⊆ m × φ × φ
  [(unify-φ? () φ_1 φ_2)]
  [(unify-φ? ((ℓ_1 ↔ ℓ_2) any ...) φ_1 φ_2)
   (unify-φ? (any ...) φ_1 φ_2)
   (where U ,(hash-ref (term φ_1) (term ℓ_1)))
   (where U ,(hash-ref (term φ_2) (term ℓ_2)))])

(define-metafunction λs
  rename-V : m V -> V
  [(rename-V {_ ... [ℓ_1 ↔ ℓ_2] _ ...} (• ℓ_1)) (• ℓ_2)]
  [(rename-V _ V) V])

(define-metafunction λs
  rename-φ : m φ -> φ
  [(rename-φ () φ) φ]
  [(rename-φ {[ℓ_1 ↔ ℓ_2] any ...} φ)
   (rename-φ {any ...} ,(hash-set (term φ) (term ℓ_2) (hash-ref (term φ) (term ℓ_1))))])

(define-metafunction λs
  invert : m -> m
  [(invert {[ℓ_1 ↔ ℓ_2] ...}) {[ℓ_2 ↔ ℓ_1] ...}])

(define-judgment-form λs
  ;; Implementation of primitive operations
  #:contract (δ σ φ o (V ...) A φ σ)
  #:mode     (δ I I I I       O O O)
  ;; Predicates on concrete
  [(δ σ φ integer? (n) 0 φ σ)]
  [(side-condition ,(not (integer? (term V))))
   (side-condition ,(not (uk? (term V))))
   -------------------------------------------------------------
   (δ σ φ integer? (V) 1 φ σ)]
  [(δ σ φ procedure? ((Clo _ ...)) 0 φ σ)]
  [(δ σ φ procedure? (o) 0 φ σ)]
  [(side-condition ,(not (redex-match? λs (Clo _ ...) (term V))))
   (side-condition ,(not (redex-match? λs o (term V))))
   (side-condition ,(not (uk? (term V))))
   -------------------------------------------------------------
   (δ σ φ procedure? (V) 1 φ σ)]
  [(δ σ φ pair? ((Pair _ _)) 0 φ σ)]
  [(side-condition ,(not (uk? (term V))))
   -------------------------------------------------------------
   (δ σ φ pair? (V) 1 φ σ)]
  [(δ σ φ zero? (0) 0 φ σ)]
  [(side-condition ,(not (equal? 0 (term V))))
   (side-condition ,(not (uk? (term V))))
   -------------------------------------------------------------
   (δ σ φ zero? (V) 1 φ σ)]
  
  ;; Predicates on abstracts
  [(side-condition ,(set-member? (term any) (term p)))
   -------------------------------------------------------------
   (δ σ φ p ((● any)) 0 φ σ)]
  [(side-condition ,(not (set-member? (term any) (term p))))
   ;; could be better, just sloppy
   -------------------------------------------------------------
   (δ σ φ p ((● any)) 1 φ σ)]
  [(side-condition ,(not (set-member? (term any) (term p))))
   ;; could be better, just sloppy
   -------------------------------------------------------------
   (δ σ φ p ((● any)) 0 φ σ)]
  
  ;; Predicates on symbolic
  [(where U ,(hash-ref (term φ) (term ℓ)))
   (δ σ φ p (U) n φ σ)
   (where φ_1 ,(if (equal? (term n) 0)
                   (term (ext φ [ℓ ↦ (refine-U U p)]))
                   (term φ)))
   -------------------------------------------------------------
   (δ σ φ p ((• ℓ)) n φ_1 σ)]

  ;; add1
  [(δ σ φ integer? (V) 0 φ_1 σ)
   -------------------------------------------------------------
   (δ σ φ add1 (V) (● ,{set 'integer?}) φ_1 σ)]
  [(δ σ φ integer? (V) 1 φ_1 σ)
   -------------------------------------------------------------
   (δ σ φ add1 (V) (err "add1 to non-int") φ_1 σ)]

  ;; cons
  [;; didn't accumulate enough context for allocation
   (where α_1 ,(format-symbol "car_~a" (intern 'cons (term ()))))
   (where α_2 ,(format-symbol "cdr_~a" (intern 'cons (term ()))))
   (where σ_1 (⊔ σ [α_1 ↦ V_1] [α_2 ↦ V_2]))
   -------------------------------------------------------------
   (δ σ φ cons (V_1 V_2) (Pair α_1 α_2) φ σ_1)]

  ;; car
  [(lookup σ α V)
   -------------------------------------------------------------
   (δ σ φ car ((Pair α _)) V φ σ)]
  [(δ σ φ pair? ((• ℓ)) 0 φ_1 σ)
   (where (Pair α _) ,(hash-ref (term φ) (term ℓ) #f))
   (lookup σ α V)
   -------------------------------------------------------------
   (δ σ φ car ((• ℓ)) V φ σ)]
  [(δ σ φ pair? ((• ℓ)) 0 φ_1 σ)
   (where (● _) ,(hash-ref (term φ) (term ℓ) #f))
   (where (σ_1 φ_2 ℓ_1 _) (refine-pair σ φ_1 ℓ))
   -------------------------------------------------------------
   (δ σ φ car ((• ℓ)) (• ℓ_1) φ_2 σ_1)]

  ;; cdr
  [(lookup σ α V)
   -------------------------------------------------------------
   (δ σ φ cdr ((Pair _ α)) V φ σ)]
  [(δ σ φ pair? ((• ℓ)) 0 φ_1 σ)
   (where (Pair _ α) ,(hash-ref (term φ) (term ℓ) #f))
   (lookup σ α V)
   -------------------------------------------------------------
   (δ σ φ cdr ((• ℓ)) V φ σ)]
  [(δ σ φ pair? ((• ℓ)) 0 φ_1 σ)
   (where (● _) ,(hash-ref (term φ) (term ℓ) #f))
   (where (σ_1 φ_2 _ ℓ_2) (refine-pair σ φ_1 ℓ))
   -------------------------------------------------------------
   (δ σ φ cdr ((• ℓ)) (• ℓ_2) φ_2 σ_1)]
  )

(define-metafunction λs
  ;; Generate readable symbolic name
  gen-ℓ : any ... -> ℓ
  [(gen-ℓ any ...) ,(format-symbol "ℓ_~a" (intern 'ℓ (term (any ...))))])

(define-metafunction λs
  refine-pair : σ φ ℓ -> (σ φ ℓ ℓ)
  [(refine-pair σ φ ℓ)
   (σ_1 φ_1 ℓ_1 ℓ_2)
   (where α_1 ,(format-symbol "α_~a" (intern 'α (term (ℓ car)))))
   (where α_2 ,(format-symbol "α_~a" (intern 'α (term (ℓ cdr)))))
   (where ℓ_1 (gen-ℓ ℓ car))
   (where ℓ_2 (gen-ℓ ℓ cdr))
   (where φ_1 (ext φ [ℓ ↦ (Pair α_1 α_2)] [ℓ_1 ↦ (● ,(set))] [ℓ_2 ↦ (● ,(set))]))
   (where σ_1 (⊔ σ [α_1 ↦ ℓ_1] [α_2 ↦ ℓ_2]))])

(define-metafunction λs
  refine-U : U p -> U
  [(refine-U _ zero?) 0]
  [(refine-U (● any) p) (● ,(set-add (term any) (term p)))]
  [(refine-U U _) U])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Macros
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction λs
  -let : ([x e]) e -> e
  [(-let ([x e_x]) e) ((λ (x) e) e_x)])

(define-metafunction λs
  -let* : ([x e] ...) e -> e
  [(-let* () e) e]
  [(-let* ([x e_x] any ...) e) (-let ([x e_x]) (-let* (any ...) e))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-term p1
  (-let* ([x (• ℓ_1)]
          [f (λ (z) (if0 (integer? z) (add1 z) z))])
         (f x)))
;; (viz p1)
;; (ev p1)

(define-term Ω
  ((λ (x) (x x)) (λ (y) (y y))))
;; (viz Ω)
;; (ev Ω)

(define-term length
  (-let* ([Y (λ (f) ((λ (x) (f (λ (v) ((x x) v))))
                     (λ (y) (f (λ (u) ((y y) u))))))]
          [len
           (Y (λ (rec)
                (λ (l)
                  (if0 (pair? l)
                       (add1 (rec (cdr l)))
                       0))))])
         (len (• ℓ))))
;; (viz length)
;; (ev length)

(define-term mk-list
  (-let* ([Y (λ (f) ((λ (x) (f (λ (v) ((x x) v))))
                     (λ (y) (f (λ (u) ((y y) u))))))]
          [mk
           (Y (λ (rec)
                (λ (n)
                  (if0 n
                       0
                       (cons n (rec (add1 n)))))))])
         (mk (• ℓ))))
;; (viz mk-list)
;; (ev mk-list)
