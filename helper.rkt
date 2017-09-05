#lang racket/base

(provide (all-defined-out))
(require racket/match
         racket/list
         racket/set
         redex)

(define-language λ0)

(define-metafunction λ0
  ⊔ : any [any ↦ any] ... -> any
  [(⊔ any_map any_pair ...)
   ,(for/fold ([m (term any_map)])
              ([pair (in-list (term (any_pair ...)))])

      ;; hack to widen integers
      (define (⊔₁ vs)
        (define int?
          (match-lambda
            [(? integer?) #t]
            [`(● ,s) #:when (set-member? s 'integer?) #t]
            [_ #f]))
        (define (ext) (set-add vs v))
        (cond
          [(int? v)
           (define old-ints (for/set ([v (in-set vs)] #:when (int? v)) v))
           (define (widen) (set-add (set-subtract vs old-ints) `(● ,(set 'integer?))))
           (cond [(set-empty? old-ints) (ext)]
                 [(= 1 (set-count old-ints)) (if (equal? (set-first old-ints) v) (ext) (widen))]
                 [else (widen)])]
          [else (ext)]))
      
      (match-define `(,k ↦ ,v) pair)
      (hash-update m k ⊔₁ set))])

(define-metafunction λ0
  ext : any [any ↦ any] ... -> any
  [(ext any_map any_pair ...)
   ,(for/fold ([m (term any_map)])
              ([pair (in-list (term (any_pair ...)))])
      (match-define `(,k ↦ ,v) pair)
      (hash-set m k v))])

(define-judgment-form λ0
  #:contract (lookup any any any)
  #:mode     (lookup I   I   O  )
  [(side-condition ,(hash? (term any_map)))
   (where {_ ... any_val _ ...} ,(set->list (hash-ref (term any_map) (term any_key) set)))
   -------------------------------------------------------------
   (lookup any_map any_key any_val)])



;; Intern anything as integers.
;; Intended for use in pretty printings to shorten things
(define intern
  (let ([cache (make-hash)])
    (λ (tag data)
      (define cache-by-tag (hash-ref! cache tag make-hash))
      (hash-ref! cache-by-tag data (λ () (hash-count cache-by-tag))))))
