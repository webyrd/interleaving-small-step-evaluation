(load "mk/mk-vicare.scm")
(load "mk/mk.scm")
(load "mk/test-check.scm")


(define empty-env '())


(define (evalo expr val)
  (step*o `((eval-expo ,expr ,empty-env ,val) ,'halt)))



(define (eval-exampleso in/out*)
  (fresh (s*)
    (eval-examples-auxo in/out* s*)
    (step-states*o s*)))

(define (eval-examples-auxo in/out* s*)
  (conde
    ((== '() in/out*)
     (== '() s*))
    ((fresh (d in out res)
       (== `((,in ,out ) . ,d) in/out*)
       (== `(((eval-expo ,in ,empty-env ,out) ,'halt) . ,res) s*)
       (eval-examples-auxo d res)))))



(define step*o
  (lambda (s)
    (conde
      ((== s 'halt))
      ((fresh (s^)
         (=/= s 'halt)
         (stepo s s^)
         (step*o s^))))))

(define step-states*o
  (lambda (s*)
    (conde
      ((== '() s*))
      ((fresh (a d s*^)
         (== `(,a . ,d) s*)
         (step-states*-auxo s* s*^)
         (step-states*o s*^))))))

(define step-states*-auxo
  (lambda (s* s*^)
    (conde
      ((== '() s*)
       (== '() s*^))
      ((fresh (a d)
         (== `(,a . ,d) s*)
         (fresh (a^)
           (stepo a a^)
           (conde
             ((== a^ 'halt)
              (step-states*-auxo d s*^))
             ((=/= a^ 'halt)
              (fresh (d^)          
                (== `(,a^ . ,d^) s*^)
                (step-states*-auxo d d^))))))))))


(define stepo
  (lambda (s s^)
    (fresh (c k)
      (== `(,c ,k) s) ; control and continuation (control of the interpreter, not of the program being interpreted)      
      (conde

        ((fresh (v1 e2 e3 env val s)
           (== `(match-nat-aux ,v1 ,e2 ,e3 ,env ,val ,s) c)
           (conde
             [(== 'Z v1)
              (== `((eval-expo ,e2 ,env ,val) ,k) s^)]
             [(fresh (d)
                (== `(S ,d) v1)
                (== `((eval-expo ,e3 ,`((,s . (val . ,d)) . ,env) ,val) ,k) s^))])))

        ((fresh (v1 e2 e3 env val s1 s2)
           (== `(match-list-aux ,v1 ,e2 ,e3 ,env ,val ,s1 ,s2) c)
           (conde
             [(== '() v1)
              (== `((eval-expo ,e2 ,env ,val) ,k) s^)]
             [(fresh (a d)
                (== `(,a . ,d) v1)
                (=/= a 'closure)
                (== `((eval-expo ,e3 ,`((,s1 . (val . ,a)) (,s2 . (val  . ,d)) . ,env) ,val) ,k) s^))])))
        
        ((fresh (x env t)
           (== `(lookupo ,x ,env ,t) c)
           (fresh (y b rest)
             (== `((,y . ,b) . ,rest) env)
             (conde
               ((== x y)
                (== k s^)
                (conde
                  ((== `(val . ,t) b))
                  ((fresh (lam-expr)
                     (== `(rec . ,lam-expr) b)
                     (== `(closure ,lam-expr ,env) t)))))
               ((=/= x y)
                (== `((lookupo ,x ,rest ,t) ,k) s^))))))

        ((fresh (x env)
           (== `(not-in-envo ,x ,env) c)
           (conde
             ((== empty-env env)
              (== k s^))
             ((fresh (y b rest)
                (== `((,y . ,b) . ,rest) env)
                (=/= y x)
                (== `((not-in-envo ,x ,rest) ,k) s^))))))

        ((fresh (los)
           (== `(list-of-symbolso ,los) c)
           (conde
             ((== '() los)
              (== k s^))
             ((fresh (a d)
                (== `(,a . ,d) los)
                (symbolo a)
                (== `((list-of-symbolso ,d) ,k) s^))))))

        ((fresh (expr env val)
           (== `(eval-listo ,expr ,env ,val) c)
           (conde
             ((== '() expr)
              (== '() val)
              (== k s^))
             ((fresh (a d v-a v-d)
                (== `(,a . ,d) expr)
                (== `(,v-a . ,v-d) val)
                (== `((eval-expo ,a ,env ,v-a)
                      ((eval-listo ,d ,env ,v-d) ,k))
                    s^))))))

        ((fresh (x* a* env out)
           (== `(ext-env*o ,x* ,a* ,env ,out) c)
           (conde
             ((== '() x*) (== '() a*) (== env out)
              (== k s^))
             ((fresh (x a dx* da* env2)
                (== `(,x . ,dx*) x*)
                (== `(,a . ,da*) a*)
                (== `((,x . (val . ,a)) . ,env) env2)
                (symbolo x)
                (== `((ext-env*o ,dx* ,da* ,env2 ,out) ,k) s^))))))
        
        ((fresh (expr env val)
           (== `(eval-expo ,expr ,env ,val) c)
           (conde
             ((symbolo expr)
              (== `((lookupo ,expr ,env ,val) ,k) s^))
             
             ;; ((fresh (e1 e2 v1 v2)
             ;;    (== `(cons ,e1 ,e2) expr)
             ;;    (== `(,v1 . ,v2) val)                
             ;;    (== `((not-in-envo ,'cons ,env)
             ;;          ((eval-expo ,e1 ,env ,v1)
             ;;           ((eval-expo ,e2 ,env ,v2) ,k)))
             ;;        s^)))
    
             ((fresh (e v)
                (== `(S ,e) expr)
                (== `(S ,v) val)
                (== `((not-in-envo ,'S ,env)
                      ((eval-expo ,e ,env ,v) ,k))
                    s^)))

             ((== 'Z expr)
              (== 'Z val)
              (== `((not-in-envo ,'Z ,env) ,k) s^))

             ;; ((== '(quote ()) expr)
             ;;  (== '() val)
             ;;  (== `((not-in-envo ,'quote ,env) ,k) s^))
    
             ((fresh (rator x* rands body env2 a* res)
                (== `(,rator . ,rands) expr)
                (== `((eval-expo ,rator ,env ,`(closure (lambda ,x* ,body) ,env2))
                      ((eval-listo ,rands ,env ,a*)
                       ((ext-env*o ,x* ,a* ,env2 ,res)
                        ((eval-expo ,body ,res ,val)
                         ,k))))
                 s^)))

             ((fresh (p-name x body letrec-body)
                (== `(letrec ((,p-name (lambda ,x ,body)))
                       ,letrec-body)
                    expr)
                (== `((list-of-symbolso ,x)
                      ((not-in-envo ,'letrec ,env)
                       ((eval-expo ,letrec-body
                                   ,`((,p-name . (rec . (lambda ,x ,body))) . ,env)
                                   ,val)
                        ,k)))
                    s^)))

             ((fresh (e1 e2 e3 v1 s)
                (== `(match ,e1
                       (Z ,e2)
                       ((S ,s) ,e3)) expr)
                (symbolo s)
                (== `((not-in-envo ,'match ,env)
                      ((eval-expo ,e1 ,env ,v1)
                       ((match-nat-aux ,v1 ,e2 ,e3 ,env ,val ,s)
                        ,k)))
                    s^)))

             ;; ((fresh (e1 e2 e3 v1 s1 s2)
             ;;    (== `(match ,e1
             ;;           ('() ,e2)
             ;;           ((cons ,s1 ,s2) ,e3)) expr)
             ;;    (symbolo s1)
             ;;    (symbolo s2)
             ;;    (== `((not-in-envo ,'match ,env)
             ;;          ((eval-expo ,e1 ,env ,v1)
             ;;           ((match-list-aux ,v1 ,e2 ,e3 ,env ,val ,s1 ,s2)
             ;;            ,k)))
             ;;        s^)))

             ;; ((fresh (e1 e2 e3 e4 v1 v2)
             ;;    (== `(if (= ,e1 ,e2)
             ;;             ,e3
             ;;             ,e4) expr)
             ;;    (== `((not-in-envo ,'if ,env)
             ;;          ((eval-expo ,e1 ,env ,v1)
             ;;           ((eval-expo ,e2 ,env ,v2)
             ;;            ((if-aux ,v1 ,v2 ,e3 ,e4 ,env ,val)
             ;;             ,k))))
             ;;        s^)))
    
             )))))))



;;; new helpers
(define (match-nat-aux v1 e2 e3 env val s)  
  (conde
    [(== 'Z v1)
     (eval-expo e2 env val)]
    [(fresh (d)
       (== `(S ,d) v1)
       (eval-expo e3 `((,s . (val . ,d)) . ,env) val))]))

(define (match-list-aux v1 e2 e3 env val s1 s2)
  (conde
    [(== '() v1)
     (eval-expo e2 env val)]
    [(fresh (a d)
       (== `(,a . ,d) v1)
       (=/= a 'closure)
       (eval-expo e3 `((,s1 . (val . ,a)) (,s2 . (val  . ,d)) . ,env) val))]))

(define (if-aux v1 v2 e3 e4 env val)
  (conde
    [(== v1 v2)
     (eval-expo e3 env val)]
    [(=/= v1 v2)
     (eval-expo e4 env val)]))





(define (lookupo x env t)
  (fresh (y b rest)
    (== `((,y . ,b) . ,rest) env)
    (conde
      ((== x y)
       (conde
         ((== `(val . ,t) b))
         ((fresh (lam-expr)
            (== `(rec . ,lam-expr) b)
            (== `(closure ,lam-expr ,env) t)))))
      ((=/= x y)
       (lookupo x rest t)))))

(define (not-in-envo x env)
  (conde
    ((== empty-env env))
    ((fresh (y b rest)
       (== `((,y . ,b) . ,rest) env)
       (=/= y x)
       (not-in-envo x rest)))))

(define (list-of-symbolso los)
  (conde
    ((== '() los))
    ((fresh (a d)
       (== `(,a . ,d) los)
       (symbolo a)
       (list-of-symbolso d)))))

(define (eval-listo expr env val)
  (conde
    ((== '() expr)
     (== '() val))
    ((fresh (a d v-a v-d)
       (== `(,a . ,d) expr)
       (== `(,v-a . ,v-d) val)
       (eval-expo a env v-a)
       (eval-listo d env v-d)))))

(define (ext-env*o x* a* env out)
  (conde
    ((== '() x*) (== '() a*) (== env out))
    ((fresh (x a dx* da* env2)
       (== `(,x . ,dx*) x*)
       (== `(,a . ,da*) a*)
       (== `((,x . (val . ,a)) . ,env) env2)
       (symbolo x)
       (ext-env*o dx* da* env2 out)))))

#|
(define (evalo expr val)
  (eval-expo expr empty-env val))
|#

(define (eval-expo expr env val)
  (conde
    ((symbolo expr) (lookupo expr env val))

    ((fresh (e1 e2 v1 v2)
       (== `(cons ,e1 ,e2) expr)
       (== `(,v1 . ,v2) val)
       (not-in-envo 'cons env)
       (eval-expo e1 env v1)
       (eval-expo e2 env v2)))
    
    ((fresh (e v)
       (== `(S ,e) expr)
       (== `(S ,v) val)
       (not-in-envo 'S env)
       (eval-expo e env v)))

    ((== 'Z expr)
     (== 'Z val)
     (not-in-envo 'Z env))

    ((== '(quote ()) expr)
     (== '() val)
     (not-in-envo 'quote env))
    
    ((fresh (rator x* rands body env2 a* res)
       (== `(,rator . ,rands) expr)
       (eval-expo rator env `(closure (lambda ,x* ,body) ,env2))
       (eval-listo rands env a*)
       (ext-env*o x* a* env2 res)
       (eval-expo body res val)))

    ((fresh (p-name x body letrec-body)
       (== `(letrec ((,p-name (lambda ,x ,body)))
              ,letrec-body)
           expr)
       (list-of-symbolso x)
       (not-in-envo 'letrec env)
       (eval-expo letrec-body
                  `((,p-name . (rec . (lambda ,x ,body))) . ,env)
                  val)))

    ((fresh (e1 e2 e3 v1 s)
       (== `(match ,e1
              (Z ,e2)
              ((S ,s) ,e3)) expr)
       (symbolo s)
       (not-in-envo 'match env)
       (eval-expo e1 env v1)
       (conde
         [(== 'Z v1)
          (eval-expo e2 env val)]
         [(fresh (d)
            (== `(S ,d) v1)
            (eval-expo e3 `((,s . (val . ,d)) . ,env) val))])))

    ((fresh (e1 e2 e3 v1 s1 s2)
       (== `(match ,e1
              ('() ,e2)
              ((cons ,s1 ,s2) ,e3)) expr)
       (symbolo s1)
       (symbolo s2)
       (not-in-envo 'match env)
       (eval-expo e1 env v1)
       (conde
         [(== '() v1)
          (eval-expo e2 env val)]
         [(fresh (a d)
            (== `(,a . ,d) v1)
            (=/= a 'closure)
            (eval-expo e3 `((,s1 . (val . ,a)) (,s2 . (val  . ,d)) . ,env) val))])))

    ((fresh (e1 e2 e3 e4 v1 v2)
       (== `(if (= ,e1 ,e2)
                ,e3
                ,e4) expr)
       (not-in-envo 'if env)
       (eval-expo e1 env v1)
       (eval-expo e2 env v2)
       (conde
         [(== v1 v2)
          (eval-expo e3 env val)]
         [(=/= v1 v2)
          (eval-expo e4 env val)])
       ))
    
    ))



(time (test "nat_iseven-eval-exampleso"
        (let ([example (lambda (q in out)
                         (list `(letrec ((iseven (lambda (n)
                                                   ,q)))
                                  (iseven ,in))
                               out))])
          (run 1 (q)

            ;; (== q '(match n
            ;;          [Z (S Z)]
            ;;          [(S n2) (match n2
            ;;                    [Z Z]
            ;;                    [(S n3) (iseven n3)])]))
            
            ; examples from Osera and Zdancewic
            (eval-exampleso
             (list (example q 'Z '(S Z))
                   (example q '(S Z) 'Z)
                   (example q '(S (S Z)) '(S Z))
                   (example q '(S (S (S Z))) 'Z)
                   (example q '(S (S (S (S Z)))) '(S Z))))))
        '(((match n
             (Z (S n))
             ((S _.0)
              (match _.0
                (Z _.0)
                ((S _.1) (iseven _.1)))))
           (=/= ((_.0 iseven)) ((_.0 match)) ((_.1 iseven))) (sym _.0 _.1)))))



(time (test "nat_iseven"
        (let ([example (lambda (q in out)
                         (evalo `(letrec ((iseven (lambda (n)
                                                    ,q)))
                                   (iseven ,in))
                                out))])
          (run 1 (q)
               ;(== q '(match n
                        ;[Z (S Z)]
                        ;[(S n2) (match n2
                                  ;[Z Z]
                                  ;[(S n3) (iseven n3)])]))
               ; examples from Osera and Zdancewic
               (example q 'Z '(S Z))
               (example q '(S Z) 'Z)
               (example q '(S (S Z)) '(S Z))
               (example q '(S (S (S Z))) 'Z)
               (example q '(S (S (S (S Z)))) '(S Z))
               ))
        '(((match n
             (Z (S n))
             ((S _.0)
              (match _.0
                (Z _.0)
                ((S _.1) (iseven _.1)))))
           (=/= ((_.0 iseven)) ((_.0 match)) ((_.1 iseven))) (sym _.0 _.1)))))
;; without types, but with introduction and elimination
;;
;; > (load "advanced-synth-untyped.scm")
;; Testing "nat_iseven"
;; running stats for (test "nat_iseven" (let ((example (lambda (q in out) (evalo `(letrec ((iseven (lambda (n) ,q))) (iseven ,in)) out)))) (run 1 (q) (example q 'Z '(S Z)) (example q '(S Z) 'Z) (example q '(S (S Z)) '(S Z)) (example q '(S (S (S Z))) 'Z) (example q '(S (S (S (S Z)))) '(S Z)))) '(((match n (Z (S n)) ((S _.0) (match _.0 (Z _.0) ((S _.1) (iseven _.1))))) (=/= ((_.0 iseven)) ((_.0 match)) ((_.1 iseven))) (sym _.0 _.1)))):
;;     2 collections
;;     31 ms elapsed cpu time, including 2 ms collecting
;;     32 ms elapsed real time, including 2 ms collecting
;;     17390000 bytes allocated

;; without types or introduction/elimination
;;
;; > (load "advanced-synth-untyped2.scm")
;; Testing "nat_iseven"
;; running stats for (test "nat_iseven" (let ((example (lambda (q in out) (evalo `(letrec ((iseven (lambda (n) ,q))) (iseven ,in)) out)))) (run 1 (q) (example q 'Z '(S Z)) (example q '(S Z) 'Z) (example q '(S (S Z)) '(S Z)) (example q '(S (S (S Z))) 'Z) (example q '(S (S (S (S Z)))) '(S Z)))) '(((match n (Z (S n)) ((S _.0) (match _.0 (Z _.0) ((S _.1) (iseven _.1))))) (=/= ((_.0 iseven)) ((_.0 match)) ((_.1 iseven))) (sym _.0 _.1)))):
;;     2 collections
;;     33 ms elapsed cpu time, including 2 ms collecting
;;     34 ms elapsed real time, including 2 ms collecting
;;     18691296 bytes allocated




(time (test "nat_max"
        (let ([example (lambda (q in1 in2 out)
                         (evalo `(letrec ((max (lambda (n1 n2)
                                                 ,q)))
                                   (max ,in1 ,in2))
                                out))])
          (run 1 (q)
               ;(== q '(match n1
                        ;[Z n2]
                        ;[(S n3)
                         ;(match n2
                           ;[Z n1]
                           ;[(S n4) (S (max n3 n4))])]))

               ; examples from Osera and Zdancewic
               (example q 'Z 'Z 'Z)
               (example q 'Z '(S Z) '(S Z))
               (example q 'Z '(S (S Z)) '(S (S Z)))

               (example q '(S Z) 'Z '(S Z))
               (example q '(S Z) '(S Z) '(S Z))
               (example q '(S Z) '(S (S Z)) '(S (S Z)))

               (example q '(S (S Z)) 'Z '(S (S Z)))
               (example q '(S (S Z)) '(S Z) '(S (S Z)))
               (example q '(S (S Z)) '(S (S Z)) '(S (S Z)))

               ; additional examples we need
               (example q '(S (S (S (S (S Z))))) '(S (S (S (S Z)))) '(S (S (S (S (S Z))))))
               (example q '(S (S (S (S (S (S (S Z))))))) '(S (S (S (S (S Z))))) '(S (S (S (S (S (S (S Z))))))))
               (example q '(S (S (S (S (S Z))))) '(S (S (S (S (S (S (S Z))))))) '(S (S (S (S (S (S (S Z))))))))

               ))
        '(((match n1 (Z n2) ((S _.0) (S (match n2 (Z _.0) ((S _.1) (match _.0 (Z _.1) ((S _.2) (S (match _.1 (Z _.2) ((S _.3) (max _.3 _.2))))))))))) (=/= ((_.0 S)) ((_.0 _.1)) ((_.0 match)) ((_.0 max)) ((_.0 n2)) ((_.1 S)) ((_.1 _.2)) ((_.1 match)) ((_.1 max)) ((_.2 S)) ((_.2 _.3)) ((_.2 match)) ((_.2 max)) ((_.3 max))) (sym _.0 _.1 _.2 _.3)))
        ))

;; without types, but with introduction and elimination
;;
;; Testing "nat_max"
;; running stats for (test "nat_max" (let ((example (lambda (q in1 in2 out) (evalo `(letrec ((max (lambda (n1 n2) ,q))) (max ,in1 ,in2)) out)))) (run 1 (q) (example q 'Z 'Z 'Z) (example q 'Z '(S Z) '(S Z)) (example q 'Z '(S (S Z)) '(S (S Z))) (example q '(S Z) 'Z '(S Z)) (example q '(S Z) '(S Z) '(S Z)) (example q '(S Z) '(S (S Z)) '(S (S Z))) (example q '(S (S Z)) 'Z '(S (S Z))) (example q '(S (S Z)) '(S Z) '(S (S Z))) (example q '(S (S Z)) '(S (S Z)) '(S (S Z))) (example q '(S (S (S (S (S Z))))) '(S (S (S (S Z)))) '(S (S (S (S (S Z)))))) (example q '(S (S (S (S (S (S (S Z))))))) '(S (S (S (S (S Z))))) '(S (S (S (S (S (S (S Z)))))))) (example q '(S (S (S (S (S Z))))) '(S (S (S (S (S (S (S Z))))))) '(S (S (S (S (S (S (S Z)))))))))) '(((match n1 (Z n2) ((S _.0) (S (match n2 (Z _.0) ((S _.1) (match _.0 (Z _.1) ((S _.2) (S (match _.1 (Z _.2) ((S _.3) (max _.3 _.2))))))))))) (=/= ((_.0 S)) ((_.0 _.1)) ((_.0 match)) ((_.0 max)) ((_.0 n2)) ((_.1 S)) ((_.1 _.2)) ((_.1 match)) ((_.1 max)) ((_.2 S)) ((_.2 _.3)) ((_.2 match)) ((_.2 max)) ((_.3 max))) (sym _.0 _.1 _.2 _.3)))):
;;     212 collections
;;     9646 ms elapsed cpu time, including 1479 ms collecting
;;     9650 ms elapsed real time, including 1480 ms collecting
;;     1782521984 bytes allocated


;; without types or introduction/elimination
;;
;; Testing "nat_max"
;; running stats for (test "nat_max" (let ((example (lambda (q in1 in2 out) (evalo `(letrec ((max (lambda (n1 n2) ,q))) (max ,in1 ,in2)) out)))) (run 1 (q) (example q 'Z 'Z 'Z) (example q 'Z '(S Z) '(S Z)) (example q 'Z '(S (S Z)) '(S (S Z))) (example q '(S Z) 'Z '(S Z)) (example q '(S Z) '(S Z) '(S Z)) (example q '(S Z) '(S (S Z)) '(S (S Z))) (example q '(S (S Z)) 'Z '(S (S Z))) (example q '(S (S Z)) '(S Z) '(S (S Z))) (example q '(S (S Z)) '(S (S Z)) '(S (S Z))) (example q '(S (S (S (S (S Z))))) '(S (S (S (S Z)))) '(S (S (S (S (S Z)))))) (example q '(S (S (S (S (S (S (S Z))))))) '(S (S (S (S (S Z))))) '(S (S (S (S (S (S (S Z)))))))) (example q '(S (S (S (S (S Z))))) '(S (S (S (S (S (S (S Z))))))) '(S (S (S (S (S (S (S Z)))))))))) '(((match n1 (Z n2) ((S _.0) (S (match n2 (Z _.0) ((S _.1) (match _.0 (Z _.1) ((S _.2) (S (match _.1 (Z _.2) ((S _.3) (max _.3 _.2))))))))))) (=/= ((_.0 S)) ((_.0 _.1)) ((_.0 match)) ((_.0 max)) ((_.0 n2)) ((_.1 S)) ((_.1 _.2)) ((_.1 match)) ((_.1 max)) ((_.2 S)) ((_.2 _.3)) ((_.2 match)) ((_.2 max)) ((_.3 max))) (sym _.0 _.1 _.2 _.3)))):
;;     756 collections
;;     39085 ms elapsed cpu time, including 7936 ms collecting
;;     39103 ms elapsed real time, including 7943 ms collecting
;;     6336025664 bytes allocated



;; we haven't been able to get past list_append since we removed types

#|
(time (test "list_append"
        (let ([example
                (lambda (q in1 in2 out)
                  (evalo `(letrec ((append (lambda (l1 l2)
                                             ,q)))
                            (append ,in1 ,in2)) out))])
          (run 1 (q)
               ;(== q '(match l1
                        ;['() l2]
                        ;[(cons a d) (cons a (append d l2))]))
               (example q ''() ''() '())
               (example q ''() '(cons Z '()) '(Z))
               (example q '(cons Z '()) ''() '(Z))
               (example q '(cons Z '()) '(cons Z '()) '(Z Z))
               (example q '(cons (S Z) (cons Z '())) ''() '((S Z) Z))
               (example q '(cons (S Z) (cons Z '())) '(cons Z '()) '((S Z) Z Z))

               ; additional examples we need
               (absento 'S q)
               (example q '(cons (S Z)
                                 (cons (S (S Z))
                                       (cons (S (S (S Z)))
                                             (cons (S (S (S (S Z))))
                                                   '())))) 
                        '(cons Z '())
                        '((S Z) (S (S Z)) (S (S (S Z))) (S (S (S (S Z)))) Z))
               (example q '(cons (S Z)
                                 (cons (S (S Z))
                                       (cons (S (S (S Z))) (cons (S (S (S (S (S Z))))) '())))) '(cons Z '()) '((S Z) (S (S Z)) (S (S (S Z))) (S (S (S (S (S Z))))) Z))
               ;(example q '(cons (S Z) (cons Z (cons Z (cons Z (cons Z (cons Z (cons (S Z) (cons Z (cons Z (cons (S (S (S Z))) (cons (S (S (S (S Z)))) (cons (S (S (S (S (S Z))))) '())))))))))))) '(cons Z '()) '((S Z) Z Z Z Z Z (S Z) Z Z (S (S (S Z))) (S (S (S (S Z)))) (S (S (S (S (S Z))))) Z))
               ;(example q '(cons (S Z) (cons Z (cons Z (cons Z (cons Z (cons Z (cons (S Z) (cons Z (cons Z (cons (S (S (S Z))) (cons (S (S (S Z))) (cons (S (S (S (S (S Z))))) '())))))))))))) ''(cons Z '()) '((S Z) Z Z Z Z Z (S Z) Z Z (S (S (S Z))) (S (S (S Z))) (S (S (S (S (S Z))))) Z))
               ;(example q ''() '(cons Z (cons (S Z) '())) '(Z (S Z)))
               ;(example q '(cons Z (cons (S Z) (cons (S (S Z)) '()))) '(cons (S (S (S Z))) (cons (S (S (S (S Z)))) '())) '(Z (S Z) (S (S Z)) (S (S (S Z))) (S (S (S (S Z))))))
               ))
        '(((match l
             ('() s)
             ((cons _.0 _.1) (cons _.0 (append _.1 s))))
           (=/= ((_.0 S)) ((_.0 _.1)) ((_.0 append)) ((_.0 cons)) ((_.0 s)) ((_.1 S)) ((_.1 append)) ((_.1 cons)) ((_.1 s))) (sym _.0 _.1)))))

(time (test "list_drop"
        (let ([example (lambda (q l num out)
                         (evalo
                           `(letrec ((list_drop (lambda (l n)
                                                  ,q)))
                              (list_drop ,l ,num))
                           out))])
          (run 1 (q)
               ;(== q '(match n
                       ;[Z l]
                       ;[(S n2) (match l
                                 ;['() '()]
                                 ;[(cons a d) (list_drop d n2)])]))

               ; examples from Osera and Zdancewic
               (example q ''() 'Z '())
               (example q ''() '(S Z) '())
               (example q '(cons Z '()) 'Z '(Z))
               (example q '(cons Z '()) '(S Z) '())
               (example q '(cons (S Z) '()) 'Z '((S Z)))
               (example q '(cons (S Z) '()) '(S Z) '())
               (example q '(cons (S Z) (cons Z '())) 'Z '((S Z) Z))
               (example q '(cons (S Z) (cons Z '())) '(S Z) '(Z))
               (example q '(cons Z (cons (S Z) '())) 'Z '(Z (S Z)))
               (example q '(cons Z (cons (S Z) '())) '(S Z) '((S Z)))

               ; extra examples we need
               (example q '(cons Z (cons Z (cons Z (cons Z (cons Z '()))))) '(S (S (S Z))) '(Z Z))
               (example q '(cons Z (cons Z (cons Z (cons Z (cons Z '()))))) '(S (S Z)) '(Z Z Z))
               (example q '(cons Z (cons Z (cons Z '()))) '(S (S Z)) '(Z))
               (example q '(cons Z (cons Z (cons Z '()))) '(S Z) '(Z Z))
               ))
        ; weird but a correct answer.
        '(((match l ('() l) ((cons _.0 _.1) (match n (Z l) ((S _.2) (match _.2 (Z _.1) ((S _.3) (list_drop _.1 _.2))))))) (=/= ((_.0 _.1)) ((_.0 l)) ((_.0 list_drop)) ((_.0 match)) ((_.0 n)) ((_.1 _.2)) ((_.1 _.3)) ((_.1 l)) ((_.1 list_drop)) ((_.1 match)) ((_.1 n)) ((_.2 _.3)) ((_.2 list_drop)) ((_.2 match)) ((_.3 list_drop))) (sym _.0 _.1 _.2 _.3)))))

(time (test "list_hd"
        (let ([example (lambda (q l out)
                         (evalo `(letrec ([list_hd (lambda (l)
                                                     ,q)])
                                   (list_hd ,l))
                                out))])
          (run 1 (q)
               (example q ''() 'Z)
               (example q '(cons Z '()) 'Z)
               (example q '(cons (S Z) '()) '(S Z))))
        '(((match l ('() Z) ((cons _.0 _.1) _.0)) (sym _.0 _.1)))))

(time (test "list_inc"
        (let ([example (lambda (q l out)
                         (evalo `(letrec ([map (lambda (l f)
                                                 (match l
                                                   ['() '()]
                                                   [(cons a d) (cons (f a) (map d f))]))])
                                   (letrec ([list_inc (lambda (l)
                                                        ,q)])
                                     (list_inc ,l)))
                                out))])
          (run 1 (q)
               ;(== q `(letrec ([inc (lambda (n) : ((number) -> number)
                                      ;(S n))])
                        ;(map l inc)))
               ; examples from Osera and Zdancewic

               (example q ''() '())
               (example q '(cons (S Z) (cons (S (S Z)) '())) '((S (S Z)) (S (S (S Z)))))
               (example q '(cons Z (cons Z '())) '((S Z) (S Z)))
               (example q '(cons (S (S (S Z))) (cons (S (S (S (S Z)))) (cons (S (S (S (S (S Z))))) '()))) '((S (S (S (S Z)))) (S (S (S (S (S Z))))) (S (S (S (S (S (S Z))))))))

               ; doesn't choose to use map... not sure how to force? Could provide inc function ourselves, but that's not a fair comparison.

               ))
        '(((match l ('() l) ((cons _.0 _.1) (cons (S _.0) (list_inc _.1)))) (=/= ((_.0 S)) ((_.0 _.1)) ((_.0 cons)) ((_.0 list_inc)) ((_.1 S)) ((_.1 cons)) ((_.1 list_inc))) (sym _.0 _.1)))))


(time (test "list_length"
        (let ([example (lambda (q l out)
                         (evalo `(letrec ([list_length (lambda (l)
                                                         ,q)])
                                   (list_length ,l))
                                out))])
          (run 1 (q)
               (example q ''() 'Z)
               (example q '(cons Z '()) '(S Z))
               (example q '(cons Z (cons Z '())) '(S (S Z)))
               ))
        '(((match l ('() Z) ((cons _.0 _.1) (S (list_length _.1)))) (=/= ((_.0 S)) ((_.0 _.1)) ((_.0 list_length)) ((_.1 S)) ((_.1 list_length))) (sym _.0 _.1)))))


(time (test "list_map"
        (let ([example (lambda (q l f out)
                         (evalo
                           `(letrec ([zero (lambda (n)
                                             Z)])
                              (letrec ([inc (lambda (n)
                                              (S n))])
                                (letrec ([map (lambda (l f)
                                                ,q)])
                                  (map ,l ,f))))
                           out))])
          (run 1 (q)
               ;(== q '(match l
                        ;['() '()]
                        ;[(cons a d) (cons (f a) (map d f))]))
               (example q ''() 'inc '())
               (example q '(cons Z '()) 'inc '((S Z)))

               ; example reordered; before the reordering, didn't get an answer back
               ; after 15 minutes.
               (example q '(cons Z '()) 'zero '(Z))

               (example q '(cons Z (cons Z '())) 'inc '((S Z) (S Z)))
               (example q '(cons (S Z) '()) 'inc '((S (S Z))))
               (example q '(cons (S Z) (cons (S Z) '())) 'inc '((S (S Z)) (S (S Z))))

               (example q ''() 'zero '())
               (example q '(cons Z (cons Z '())) 'zero '(Z Z))
               ))
        '(((match l
             ('() l)
             ((cons _.0 _.1) (cons (f _.0) (map _.1 f))))
           (=/= ((_.0 _.1)) ((_.0 cons)) ((_.0 f)) ((_.0 map)) ((_.1 cons)) ((_.1 f)) ((_.1 map))) (sym _.0 _.1)))))

(time (test "list_nth"
        (let ([example (lambda (q l n out)
                         (evalo
                           `(letrec ([list_nth (lambda (l n)
                                                 ,q)])
                              (list_nth ,l ,n))
                           out))])
          (run 1 (q)
               (example q ''() 'Z 'Z)
               (example q ''() '(S Z) 'Z)

               (example q '(cons (S (S Z)) '()) 'Z '(S (S Z)))
               (example q '(cons (S (S Z)) '()) '(S Z) 'Z)

               (example q '(cons (S Z) (cons (S (S Z)) '())) 'Z '(S Z))
               (example q '(cons (S Z) (cons (S (S Z)) '())) '(S Z) '(S (S Z)))

               (example q '(cons (S Z) '()) 'Z '(S Z))
               (example q '(cons (S Z) '()) '(S Z) 'Z)

               (example q '(cons (S (S Z)) (cons (S Z) '())) 'Z '(S (S Z)))
               (example q '(cons (S (S Z)) (cons (S Z) '())) '(S Z) '(S Z))

               (example q '(cons (S (S (S Z))) (cons (S (S Z)) (cons (S Z) '()))) 'Z '(S (S (S Z))))
               (example q '(cons (S (S (S Z))) (cons (S (S Z)) (cons (S Z) '()))) '(S Z) '(S (S Z)))
               (example q '(cons (S (S (S Z))) (cons (S (S Z)) (cons (S Z) '()))) '(S (S Z)) '(S Z))
               ))
        '(((match l
             ('() Z)
             ((cons _.0 _.1) (match n
                               (Z _.0)
                               ((S _.2) (list_nth _.1 _.2)))))
           (=/= ((_.0 _.1)) ((_.0 list_nth)) ((_.0 match)) ((_.0 n)) ((_.1 _.2)) ((_.1 list_nth)) ((_.1 match)) ((_.1 n)) ((_.2 list_nth))) (sym _.0 _.1 _.2)))))


(time (test "list_pairwise_swap"
        (let ([example (lambda (q l out)
                         (evalo
                           `(letrec ([list_pairwise_swap (lambda (l)
                                                           ,q)])
                              (list_pairwise_swap ,l))
                           out))])
          (run 1 (q)
               ;(== q '(match l
                        ;['() '()]
                        ;[(cons n1 l2) (match (list_pairwise_swap l2)
                                      ;['() (match l2
                                             ;['() '()]
                                             ;[(cons n2 l3) (cons n2 (cons n1 (list_pairwise_swap l3)))])]
                                      ;[(cons n2 l3) '()])]))
               (example q ''() '())
               (example q '(cons Z '()) '())
               (example q '(cons (S Z) '()) '())
               (example q '(cons Z (cons (S Z) '())) '((S Z) Z))
               (example q '(cons (S Z) (cons Z '())) '(Z (S Z)))
               (example q '(cons (S Z) (cons Z (cons (S Z) '()))) '())
               (example q '(cons Z (cons (S Z) (cons Z (cons (S Z) '())))) '((S Z) Z (S Z) Z))

               ; extra examples we need
               (example q '(cons Z (cons (S Z) (cons Z (cons (S Z) (cons Z (cons (S (S Z)) '())))))) '((S Z) Z (S Z) Z (S (S Z)) Z))
               (example q '(cons (S (S Z)) (cons (S Z) (cons Z (cons (S Z) (cons (S (S Z)) (cons Z '())))))) '((S Z) (S (S Z)) (S Z) Z Z (S (S Z))))
               ))

        ; correct, but overlarge result. Does an extra couple matches deep.
        '(((match l
             ('() l)
             ((cons _.0 _.1) (match _.1
                               ('() _.1)
                               ((cons _.2 _.3) (match _.3
                                                 ('() (cons _.2 (cons _.0 _.3)))
                                                 ((cons _.4 _.5) (match _.5 ('() _.5) ((cons _.6 _.7) (cons _.2 (cons _.0 (list_pairwise_swap _.3)))))))))))
           (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 cons)) ((_.0 list_pairwise_swap)) ((_.0 match)) ((_.1 cons)) ((_.1 list_pairwise_swap)) ((_.1 match)) ((_.2 _.3)) ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 cons)) ((_.2 list_pairwise_swap)) ((_.2 match)) ((_.3 _.4)) ((_.3 _.5)) ((_.3 _.6)) ((_.3 _.7)) ((_.3 cons)) ((_.3 list_pairwise_swap)) ((_.3 match)) ((_.4 _.5)) ((_.4 cons)) ((_.4 list_pairwise_swap)) ((_.4 match)) ((_.5 cons)) ((_.5 list_pairwise_swap)) ((_.5 match)) ((_.6 cons)) ((_.6 list_pairwise_swap)) ((_.7 cons)) ((_.7 list_pairwise_swap))) (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7)))))



; broken - takes 300 seconds to produce a wrong answer.
;(time (test "list_rev_append"
        ;(let ([example (lambda (q l out)
                         ;(evalo
                           ;`(letrec ([append (lambda (l1 l2) : ((list list) -> list)
                                               ;(match l1
                                                 ;['() l2]
                                                 ;[(cons x l1) (cons x (append l1 l2))]))])
                             ;(letrec ([list_rev_append (lambda (l1) : ((list) -> list)
                                                        ;,q)])
                              ;(list_rev_append ,l)))
                           ;out))])
          ;(run 1 (q)
               ;;(== q '(match l1
                        ;;['() '()]
                        ;;[(cons n1 l2) (append (list_rev_append l2) (cons n1 '()))]))
               ;(example q ''() '())
               ;(example q '(cons Z '()) '(Z))
               ;(example q '(cons (S Z) '()) '((S Z)))
               ;(example q '(cons Z (cons (S Z) '())) '((S Z) Z))
               ;(example q '(cons Z (cons Z (cons (S Z) '()))) '((S Z) Z Z))

               ;; additional examples we need
               ;(absento 'S q)
               ;(example q
                        ;'(cons Z (cons (S Z) (cons (S (S Z)) (cons (S (S (S Z))) (cons (S (S (S (S Z)))) (cons (S (S (S (S (S Z))))) '()))))))
                        ;'((S (S (S (S (S Z))))) (S (S (S (S Z)))) (S (S (S Z))) (S (S Z)) (S Z) Z))
               ;))
        ;'??))



; broken - produces wrong, overspecialized, answer
;(time (test "list_rev_fold"
        ;(let ([example (lambda (q l out)
                         ;(evalo
                           ;`(letrec ([fold (lambda (l f acc) : ((list ((list number) -> list) list) -> list)
                                               ;(match l
                                                 ;['() acc]
                                                 ;[(cons x l) (fold l f (f acc x))]))])
                              ;(letrec ([list_rev_fold (lambda (l1) : ((list) -> list)
                                                          ;,q)])
                                ;(list_rev_fold ,l)))
                           ;out))])
          ;(run 1 (q)
               ;;(== q '(letrec ([f (lambda (l n) : ((list number) -> list)
                                    ;;(cons n l))])
                        ;;(fold l1 f '())))
               ;(example q ''() '())
               ;(example q '(cons Z '()) '(Z))
               ;(example q '(cons (S Z) '()) '((S Z)))
               ;(example q '(cons Z (cons (S Z) '())) '((S Z) Z))
               ;(example q '(cons Z (cons Z (cons (S Z) '()))) '((S Z) Z Z))

               ;; additional examples we need
               ;(absento 'S q)
               ;(example q
                        ;'(cons Z (cons (S Z) (cons (S (S Z)) (cons (S (S (S Z))) (cons (S (S (S (S Z)))) (cons (S (S (S (S (S Z))))) '()))))))
                        ;'((S (S (S (S (S Z))))) (S (S (S (S Z)))) (S (S (S Z))) (S (S Z)) (S Z) Z))
               ;))
        ;'??))

; broken - produces wrong, overspecialized, answer
;(time (test "list_rev_snoc"
        ;(let ([example (lambda (q l out)
                         ;(evalo
                           ;`(letrec ([snoc (lambda (l n) : ((list number) -> list)
                                             ;(match l
                                               ;['() (cons n '())]
                                               ;[(cons x xs) (cons x (snoc xs n))]))])
                                ;(letrec ([list_rev_snoc (lambda (l1) : ((list) -> list)
                                                            ;,q)])
                                  ;(list_rev_snoc ,l)))
                           ;out))])
          ;(run 1 (q)
               ;;(== q '(match l1
                        ;;['() '()]
                        ;;[(cons n1 l2) (snoc (list_rev_snoc l2) n1)]))
               ;(example q ''() '())
               ;(example q '(cons Z '()) '(Z))
               ;(example q '(cons (S Z) '()) '((S Z)))
               ;(example q '(cons Z (cons (S Z) '())) '((S Z) Z))
               ;(example q '(cons Z (cons Z (cons (S Z) '()))) '((S Z) Z Z))

               ;; additional examples we need
               ;(absento 'S q)
               ;(example q
                        ;'(cons Z (cons (S Z) (cons (S (S Z)) (cons (S (S (S Z))) (cons (S (S (S (S Z)))) (cons (S (S (S (S (S Z))))) '()))))))
                        ;'((S (S (S (S (S Z))))) (S (S (S (S Z)))) (S (S (S Z))) (S (S Z)) (S Z) Z))
               ;))
        ;'??))


; broken - doesn't return after significant running time
;(time (test "list_rev_tailcall"
        ;(let ([example (lambda (q l1 l2 out)
                         ;(evalo
                           ;`(letrec ([list_rev_tailcall (lambda (l1 l2) : ((list list) -> list)
                                                          ;,q)])
                              ;(list_rev_tailcall ,l1 ,l2))
                           ;out))])
          ;(run 1 (q)
               ;;(== q '(match l1
                        ;;['() l2]
                        ;;[(cons n1 l3) (list_rev_tailcall l3 (cons n1 l2))]))
               ;(example q ''() ''() '())
               ;(example q ''() '(cons Z '()) '(Z))
               ;(example q ''() '(cons (S Z) '()) '((S Z)))
               ;(example q ''() '(cons (S Z) (cons Z '())) '((S Z) Z))
               ;(example q '(cons Z '()) ''() '(Z))
               ;(example q '(cons (S Z) '()) ''() '((S Z)))
               ;(example q '(cons (S Z) '()) '(cons Z '()) '((S Z) Z))
               ;(example q '(cons Z (cons (S Z) '())) ''() '((S Z) Z))
               ;))
        ;'??))




(time (test "list_snoc"
        (let ([example (lambda (q l n out)
                         (evalo
                           `(letrec ([list_snoc (lambda (l1 n1)
                                                  ,q)])
                              (list_snoc ,l ,n))
                           out))])
          (run 1 (q)
               (example q ''() 'Z '(Z))
               (example q ''() '(S Z) '((S Z)))
               (example q '(cons Z '()) 'Z '(Z Z))
               (example q '(cons Z '()) '(S Z) '(Z (S Z)))
               (example q '(cons (S Z) (cons Z '())) 'Z '((S Z) Z Z))
               (example q '(cons (S Z) (cons Z '())) '(S Z) '((S Z) Z (S Z)))
               (example q '(cons (S (S Z)) (cons (S Z) (cons Z '()))) 'Z '((S (S Z)) (S Z) Z Z))
               (example q '(cons (S (S Z)) (cons (S Z) (cons Z '()))) '(S Z) '((S (S Z)) (S Z) Z (S Z)))
               ))
        '(((match l1 ('() (cons n1 l1)) ((cons _.0 _.1) (cons _.0 (list_snoc _.1 n1)))) (=/= ((_.0 _.1)) ((_.0 cons)) ((_.0 list_snoc)) ((_.0 n1)) ((_.1 cons)) ((_.1 list_snoc)) ((_.1 n1))) (sym _.0 _.1)))))




(time (test "list_stutter"
        (let ([example (lambda (q l out)
                         (evalo
                           `(letrec ([list_stutter (lambda (l)
                                                     ,q)])
                              (list_stutter ,l))
                           out))])
          (run 1 (q)
               (example q ''() '())
               (example q '(cons Z '()) '(Z Z))
               (example q '(cons (S Z) (cons Z '())) '((S Z) (S Z) Z Z))

               ; additional examples we need
               (example q '(cons (S (S Z)) (cons (S Z) (cons Z '()))) '((S (S Z)) (S (S Z)) (S Z) (S Z) Z Z))
               ))
        '(((match l ('() l) ((cons _.0 _.1) (cons _.0 (cons _.0 (list_stutter _.1))))) (=/= ((_.0 _.1)) ((_.0 cons)) ((_.0 list_stutter)) ((_.1 cons)) ((_.1 list_stutter))) (sym _.0 _.1)))))


; doesn't come back after significant runtime.
;(time (test "list_sum"
        ;(let ([example (lambda (q l out)
                         ;(evalo
                           ;`(letrec ([fold (lambda (l f acc) : ((list ((number number) -> number) number) -> number)
                                               ;(match l
                                                 ;['() acc]
                                                 ;[(cons x l) (fold l f (f acc x))]))])
                              ;(letrec ([add (lambda (n1 n2) : ((number number) -> number)
                                              ;(match n1
                                                ;[Z n2]
                                                ;[(S n3) (S (add n2 n3))]))])
                                ;(letrec ([list_sum (lambda (l) : ((list) -> number)
                                                     ;,q)])
                                  ;(list_sum ,l))))
                           ;out))])
          ;(run 1 (q)
               ;;(== q '(fold l add Z))
               ;(absento 'S q)
               ;(example q ''() 'Z)
               ;(example q '(cons (S Z) '()) '(S Z))
               ;(example q '(cons (S (S Z)) (cons (S Z) '())) '(S (S (S Z))))
               ;(example q '(cons (S Z) (cons (S Z) (cons (S Z) (cons (S (S Z)) '())))) '(S (S (S (S (S Z))))))
               ;))
        ;'??))

; doesn't come back after significant runtime.
;(time (test "list_take"
        ;(let ([example (lambda (q n l out)
                         ;(evalo
                           ;`(letrec ([list_take (lambda (n1 l1) : ((number list) -> list)
                                                  ;,q)])
                              ;(list_take ,n ,l))
                           ;out))])
          ;(run 1 (q)
               ;;(== q '(match n1
                        ;;[Z '()]
                        ;;[(S n2) (match l1
                                  ;;['() '()]
                                  ;;[(cons n3 l2) (cons n3 (list_take n2 l2))])]))
               ;(example q 'Z ''() '())
               ;(example q 'Z '(cons (S Z) '()) '())
               ;(example q 'Z '(cons Z (cons (S Z) '())) '())
               ;(example q 'Z '(cons (S Z) (cons Z (cons (S Z) '()))) '())
               ;(example q '(S Z) ''() '())
               ;(example q '(S Z) '(cons (S Z) '()) '((S Z)))
               ;(example q '(S Z) '(cons Z (cons (S Z) '())) '(Z))
               ;(example q '(S Z) '(cons (S Z) (cons Z (cons (S Z) '()))) '((S Z)))
               ;(example q '(S (S Z)) ''() '())
               ;(example q '(S (S Z)) '(cons (S Z) '()) '((S Z)))
               ;(example q '(S (S Z)) '(cons Z (cons (S Z) '())) '(Z (S Z)))
               ;(example q '(S (S Z)) '(cons (S Z) (cons Z (cons (S Z) '()))) '((S Z) Z))
               ;))
        ;'??))


(time (test "list_tl"
        (let ([example (lambda (q l out)
                         (evalo
                           `(letrec ([list_tl (lambda (l)
                                                ,q)])
                              (list_tl ,l))
                           out))])
          (run 1 (q)
               (example q ''() '())
               (example q '(cons Z '()) '())
               (example q '(cons Z (cons Z '())) '(Z))
               ))
        '(((match l ('() l) ((cons _.0 _.1) _.1)) (=/= ((_.0 _.1))) (sym _.0 _.1)))))

|#

