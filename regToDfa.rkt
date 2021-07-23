#lang racket
(require parser-tools/lex
         parser-tools/yacc)
(require "declarations.rkt")
(require "utilities.rkt")

(define (nullable? node)
  (cond [(Epsilon? node) #t]
          [(Literal? node) #f]
          [(Then? node) (and (nullable? (Then-t1 node))
                             (nullable? (Then-t2 node)))]
          [(Or? node) (or (nullable? (Or-t1 node)))
                      (nullable? (Or-t2 node))]
          [(Star? node) #t]))


(define (buildNullable t)
  (define (helper node)
    (cond [(Epsilon? node) (cons (Epsilon-n node) #t)]
          [(Literal? node) (cons (Literal-n node) #f)]
          [(Then? node) (cons (Then-n node) (and (cdr (helper (Then-t1 node)))
                                                 (cdr (helper (Then-t2 node)))))]
          [(Or? node) (cons (Or-n node) (or (cdr (helper (Or-t1 node)))
                                                 (cdr (helper (Or-t2 node)))))]
          [(Star? node) (cons (Star-n node) #t)]))
  (cond [(Epsilon? t) (list (helper t))]
        [(Literal? t) (list (helper t))]
        [(Then? t) (append* (list (buildNullable (Then-t1 t))
                                   (list (helper t))
                                   (buildNullable (Then-t2 t))))]
        [(Or? t) (append* (list (buildNullable (Or-t1 t))
                                 (list (helper t))
                                 (buildNullable (Or-t2 t))))]
        [(Star? t) (append* (list (buildNullable (Star-t t)) (list (helper t))))]))

(define (firstpos t)
  (cond [(Epsilon? t) '()]
        [(Literal? t) (list (Literal-n t))]
        [(Then? t) (if (nullable? (Then-t1 t)) (append (firstpos (Then-t1 t))
                                                       (firstpos (Then-t2 t)))
                       (firstpos (Then-t1 t)))]
        [(Or? t) (append (firstpos (Or-t1 t)) (firstpos (Or-t2 t)))]
        [(Star? t) (firstpos (Star-t t))]))


(define (buildFirst t)
  (cond [(Epsilon? t) (list (cons (Epsilon-n t) (firstpos t)))]
        [(Literal? t) (list (cons (Literal-n t) (firstpos t)))]
        [(Then? t) (append* (list (buildFirst (Then-t1 t))
                                  (list (cons (Then-n t) (firstpos t)))
                                  (buildFirst (Then-t2 t))))]
        [(Or? t) (append* (list (buildFirst (Or-t1 t))
                                  (list (cons (Or-n t) (firstpos t)))
                                  (buildFirst (Or-t2 t))))]
        [(Star? t) (append* (list (buildFirst (Star-t t))
                                  (list (cons (Star-n t) (firstpos t)))))]))

(define (lastpos t)
  (cond [(Epsilon? t) '()]
        [(Literal? t) (list (Literal-n t))]
        [(Then? t) (if (nullable? (Then-t2 t)) (append (lastpos (Then-t1 t))
                                                       (lastpos (Then-t2 t)))
                       (lastpos (Then-t2 t)))]
        [(Or? t) (append (lastpos (Or-t1 t)) (lastpos (Or-t2 t)))]
        [(Star? t) (lastpos (Star-t t))]))


(define (buildLast t)
  (cond [(Epsilon? t) (list (cons (Epsilon-n t) (lastpos t)))]
        [(Literal? t) (list (cons (Literal-n t) (lastpos t)))]
        [(Then? t) (append* (list (buildLast (Then-t1 t))
                                  (list (cons (Then-n t) (lastpos t)))
                                  (buildLast (Then-t2 t))))]
        [(Or? t) (append* (list (buildLast (Or-t1 t))
                                  (list (cons (Or-n t) (lastpos t)))
                                  (buildLast (Or-t2 t))))]
        [(Star? t) (append* (list (buildLast (Star-t t))
                                  (list (cons (Star-n t) (lastpos t)))))]))

(define (refiner m)
    
    (define (x-in-list x l)
      (cond [(null? l) #f]
            [(= x (car l)) #t]
            [else (x-in-list x (cdr l))]))
    
    (define (refine-sublist a b)
      (cond [(null? a) b]
            [(x-in-list (car a) b) (refine-sublist (cdr a) b)]
            [else (refine-sublist (cdr a) (append b (list (car a))))]))
    
    (define (helper l m)
      (define (tail-rec l m ans)
        (cond [(null? m) (cons l ans)]
              [(equal? (car l) (caar m)) (tail-rec (cons (car l) (sort (refine-sublist (cdr l) (cdr (car m))) <)) (cdr m) ans)]
              [else (tail-rec l (cdr m) (append ans (list (car m))))]))
      (tail-rec l m '()))

    (define (pos-in-list pos m)
      (cond [(null? m) #f]
            [(= pos (caar m)) #t]
            [else (pos-in-list pos (cdr m))]))

    (cond [(null? m) '()]
          [else (helper (car m) (refiner (cdr m)))]))


(define (buildFollow t)
  
  (define (helper t)
    (cond [(Then? t) (map (lambda (x) (cons x (firstpos (Then-t2 t)))) (lastpos (Then-t1 t)))]
          [(Star? t) (map (lambda (x) (cons x (firstpos (Star-t t)))) (lastpos (Star-t t)))]))
  
  (define (combiner t)
    (cond [(Epsilon? t) '()]
          [(Literal? t) '()]
          [(Then? t) (append* (list (combiner (Then-t1 t)) (helper t) (combiner (Then-t2 t))))]
          [(Star? t) (append (helper t) (combiner (Star-t t)))]
          [(Or? t) (append* (list (combiner (Or-t1 t)) (combiner (Or-t2 t))))]))
  (refiner (combiner t)))


(define (buildGraph reg)
  (define t (maketree reg))
  (define greennode (firstpos t))
  (define nodes '())
  (define transitions '())
  (define red-nodes '())
  (define follow (buildFollow t))

  (define (element-at-pos pos)
    (define (helper t)
      (cond [(Epsilon? t) (if (= (Epsilon-n t) pos) (list "@") '())]
            [(Literal? t) (if (= (Literal-n t) pos) (list (Literal-c t)) '())]
            [(Then? t) (append (helper (Then-t1 t)) (helper (Then-t2 t)))]
            [(Star? t) (helper (Star-t t))]
            [(Or? t) (append (helper (Or-t1 t)) (helper (Or-t2 t)))]))
    (car (helper t)))
  
  (define (sort-node-list l)
    (define modify-list-1 (map (lambda (n) (list (element-at-pos n) n)) l))

    (define (add-to-ans l ans)
      (cond [(null? ans) (list l)]
            [(equal? (car l) (caar ans)) (cons (append (car ans) (cdr l)) (cdr ans))]
            [else (cons (car ans) (add-to-ans l (cdr ans)))]))
    
    (define (helper l lst ans)
      (cond [(null? lst) (add-to-ans l ans)]
            [else (helper (car lst) (cdr lst) (add-to-ans l ans))]))
    (helper (car modify-list-1) (cdr modify-list-1) '()))

  (define (followpos pos)
    (define my-list follow)
    (define (helper lst)
      (cond [(null? lst) '()]
            [(= pos (caar lst)) (cdar lst)]
            [else (helper (cdr lst))]))
    (helper my-list))

  (define (transition sorted-node)
    (refiner (map (lambda (lst) (cons (car lst) (remove-duplicates (append* (map (lambda (x) (followpos x)) (cdr lst)))))) sorted-node)))

  (define (a-in-list a lst)
    (cond [(null? lst) #f]
          [(equal? (car lst) a) #t]
          [else (a-in-list a (cdr lst))]))

  (define (helper node)
    (let* [(sorted-node-list (cons node (transition (sort-node-list node))))
           (transition-node-list (flatten (map (lambda (x) (if (null? (cdr x)) (begin (set! red-nodes (cons (car sorted-node-list) red-nodes)) '())
                                                               (Trans (car sorted-node-list) (car x) (cdr x)))) (cdr sorted-node-list))))]
      (cond [(a-in-list node nodes) '()]
            [else (begin (set! transitions (append transition-node-list transitions))
                         (set! nodes (cons node nodes))
                         (map (lambda (x) (helper (Trans-final x))) transition-node-list)
                         '())])))
  (define (symbols lst)
    (define l (cons "#" (map (lambda (x) (element-at-pos (car x))) lst)))
    (define (helper lst)
      (cond [(null? lst) '()]
            [(or (equal? (car lst) "@") (a-in-list (car lst) (cdr lst))) (helper (cdr lst))]
            [else (cons (car lst) (helper (cdr lst)))]))
    (helper l))
  
  (begin (helper greennode)
         (Graph greennode nodes transitions (remove-duplicates red-nodes) (symbols follow))))