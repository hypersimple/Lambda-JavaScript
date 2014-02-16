
;; Yue Chen, Bochao Shen
;; Northeastern University

;; Code for Project "The Essence of JavaScript";
;; based on the paper "The Essence of JavaScript";

;; -----------------------------------------------------------------------------

#lang racket
(require redex)

;; Syntax and context definition of λ_JS from Paper on Page 2 ~ Page 10.
(define-language λ_JS
  (l natural)             ;Locations
  (σ ((l v) ...))         ;Store
  (c number string #t #f undefined null)                
  ;arithmetic addition.
  (v c 
     (λ (x ...) e)        ;Functions
     (obj [string v] ...) ;Objects
     l)                   ;Locations as value
  
  (e x
     v
     (obj [string e] ...) ;
     (let ([x e]) e)      ;let expression
     (e e ...)            ;Function application
     (get-field e e)      ;e[e]
     (update-field e e e) ;e[e]=e
     (delete-field e e)   ;delete e[e]
     (set! e e)           ;set the value of location l
     (ref e)              ;ref e
     (deref e)            ;deref e
     (+ e e)              ;arithmetic-addition
     (block e e ...)
     )
  
  (E hole
     (obj [string v] ... [string E] [string e] ...)
     (let ([x E]) e)
     (v ... E e ...)
     (get-field E e)
     (get-field v E)
     (update-field E e e)
     (update-field v E e)
     (update-field v v E)
     (delete-field E e)
     (delete-field v E)
     (ref E)
     (deref E)
     (set! E e)
     (set! v E)
     (+ E e)
     (+ v E)
     (block v ... E e ...))    
  
  (x variable-not-otherwise-mentioned))


;; eval-λJS returns the evaluation results of expression e
(define-metafunction λ_JS
  eval-λJS : e -> v
  [(eval-λJS e) (result ,(apply-reduction-relation* ->λ_JS (term (() e))))])


;; extract the result of the reduction result
(define-metafunction λ_JS
  result : any -> any
  [(result [(σ v)]) v])


;; Reduction rules
(define ->λ_JS
  (reduction-relation
   λ_JS
   [==> (let ([x v]) e)
        (subst x v e)
        "E-Let"]
   [==> ((λ (x ...) e) v ...)
        (subst* (x v) ... e)
        "E-App"]
   [==> (get-field (obj [string_1 v_1] ... [string_x v_x] [string_2 v_2] ...)
                   string_x)
        v_x
        "E-GetField"]
   [==> (get-field (obj [string_1 v_1] ...) string_x)
        undefined
        (side-condition 
         (and (not (member (term string_x) (term (string_1 ...))))
              (not (member (term "__proto__") (term (string_1 ...))))))
        "E-GetField-NotFound"]
   [==> (get-field 
         (obj [string_1 v_1] ... ["__proto__" l] [string_2 v_2] ...) 
         string_x)
        (get-field (deref l) string_x)
        (side-condition
         (not (member (term string_x) (term (string_1 ... string_2 ...)))))
        "E-GetField-Proto"]
   [==> (get-field 
         (obj [string_1 v_1] ... ["__proto__" null] [string_2 v_2] ...)
         string_x)
        undefined
        (side-condition 
         (not (member (term string_x) (term (string_1 ... string_2 ...)))))
        "E-GetField-Proto-Null"]                  
   [==> (update-field (obj [string_1 v_1] ... [string_x v_x] [string_2 v_2] ...)
                      string_x
                      v_update)
        (obj [string_1 v_1] ... [string_x v_update] [string_2 v_2] ...)
        "E-UpdateField"]
   [==> (update-field (obj [string_1 v_1] ...) string_x v_x)
        (obj [string_x v_x] [string_1 v_1] ...)
        (side-condition (not (member (term string_x) (term (string_1 ...)))))
        "E-CreateField"]
   [==> (delete-field (obj [string_1 v_1] ... [string_x v_x] [string_2 v_2] ...)
                      string_x)
        (obj [string_1 v_1] ... [string_2 v_2] ...)
        "E-DeleteField"]
   [==> (delete-field (obj [string_1 v_1] ...) string_x)
        (obj [string_1 v_1] ...)
        (side-condition (not (member (term string_x) (term (string_1 ...)))))
        "E-DeleteField-NotFound"]
   [--> (σ_1 (in-hole E (ref v)))
        (σ_2 (in-hole E l))
        (where (l σ_2) (malloc v σ_1))
        "E-Ref"]
   [--> (((l_1 v_1) ... (l_x v_x) (l_2 v_2) ...) (in-hole E (deref l_x)))
        (((l_1 v_1) ... (l_x v_x) (l_2 v_2) ...) (in-hole E v_x))
        "E-Deref"]
   [--> (((l_1 v_1) ... (l_x v_x) (l_2 v_2) ...) 
         (in-hole E (set! l_x v_update)))
        (((l_1 v_1) ... (l_x v_update) (l_2 v_2) ...)
         (in-hole E l_x))
        "E-SetRef"]
   [==> (+ v_1 v_2)
        ,(+ (term v_1) (term v_2))
        "Arithmetic-addition"]
   [==> (block v_1 ... v_final)
        v_final
        "block-expressions"]
   with
   [(--> (σ (in-hole E e_1)) (σ (in-hole E e_2)))
    (==> e_1 e_2)]))


;; returns a new extended store σ with the new added v
(define-metafunction λ_JS
  malloc : v σ -> (l σ)
  [(malloc v_n ((l v) ...))
   (l_n ((l_n v_n) (l v) ...))   
   (where l_n ,(length (term (0 l ...))))])

;; test
(define test-σ-1 (term ()))
(define test-σ-2 (term ((1 (obj ["hello" 1] ["world" 2])))))
(define test-v-1 (term (λ (x y z) 99)))

(define result-σ-1 (term (1 ((1 (λ (x y z) 99))))))
(define result-σ-2 (term (2 ((2 (λ (x y z) 99))
                             (1 (obj ["hello" 1] ["world" 2]))))))

(test-equal (term (malloc ,test-v-1 ,test-σ-1)) result-σ-1)
(test-equal (term (malloc ,test-v-1 ,test-σ-2)) result-σ-2)


;; subsititute the occurrences of variables x ... with values v ... in
;; expression e.
(define-metafunction λ_JS
  subst* : (x v) ... e -> e
  [(subst* (x v) e) (subst x v e)]
  [(subst* (x_1 v_1) (x_2 v_2) ... e)
   (subst x_1 v_1 (subst* (x_2 v_2) ... e))])


;; substitute the occurrences of variable x with value v in expression e
(define-metafunction λ_JS
  subst : x v e -> e
  [(subst x v (obj [string_1 e_1] ...)) 
   (obj [string_1 (subst x v e_1)] ...)]
  
  [(subst x v (let ([x e_a]) e_b)) 
   (let ([x (subst x v e_a)]) e_b)]
  
  [(subst x v (let ([x_old e_a]) e_b))
   (let ([x_new (subst x v e_a)]) (subst x v (subst-var x_old x_new e_b)))
   (where x_new ,(variable-not-in (term (x v e_b)) (term x_old)))]
  
  [(subst x_a v_a (λ (x_1 ... x_a x_2 ...) e))
   (λ (x_1 ... x_a x_2 ...) e)
   (side-condition (not (member (term x_a) (term (x_1 ...)))))]
  
  [(subst x_a v_a (λ (x_1 ...) e))
   (λ (x_new ...) (subst x_a 
                         v_a 
                         (subst-var* (x_1 ...) (x_new ...) e)))
   (where (x_new ...) 
          ,(variables-not-in (term (x_a v_a e)) (term (x_1 ...))))]
  
  [(subst x_a v_a (+ e_l e_r))
   (+ (subst x_a v_a e_l)
      (subst x_a v_a e_r))]
  
  [(subst x_a v_a (block e_1 ...))
   (block (subst x_a v_a e_1) ...)]  
  
  
  [(subst x v x) v]
  
  [(subst x v x_1) x_1]
  
  [(subst x v v_1) v_1]
  
  [(subst x v (e ...)) ((subst x v e) ...)]
  
  [(subst x v (get-field e_1 e_2)) 
   (get-field (subst x v e_1) (subst x v e_2))]
  
  [(subst x v (update-field e_1 e_2 e_3)) 
   (update-field (subst x v e_1) (subst x v e_2) (subst x v e_3))]
  
  [(subst x v (delete-field e_1 e_2))
   (delete-field (subst x v e_1) (subst x v e_2))]
  
  [(subst x v (set! e_1 e_2))
   (set! (subst x v e_1) (subst x v e_2))]
  
  [(subst x v (ref e))
   (ref (subst x v e))]
  
  [(subst x v (deref e))
   (deref (subst x v e))])


;; substitute the occurrences of variables x_o ... with variables x_n ... 
;; in expression e
(define-metafunction λ_JS
  subst-var* : (x ...) (x ...) e -> e
  [(subst-var* (x_o) (x_n) e)
   (subst-var x_o x_n e)]
  [(subst-var* (x_o1 x_o2 ...) (x_n1 x_n2 ...) e)
   (subst-var x_o1 x_n1 (subst-var* (x_o2 ...) (x_n2 ...) e))])


;; substitute the occurrences of variable x_old with variable x_new
(define-metafunction λ_JS
  subst-var : x x e -> e
  [(subst-var x_old x_new (obj [string_1 e_1] ...))
   (obj [string_1 (subst-var x_old x_new e_1)] ...)]
  
  [(subst-var x_old x_new (let ([x e_1]) e_2))
   (let ([(subst-var x_old x_new x) (subst-var x_old x_new e_1)])
     (subst-var x_old x_new e_2))]
  
  [(subst-var x_old x_new (λ (x_1 ...) e))
   (λ (subst-var x_old x_new (x_1 ...)) (subst-var x_old x_new e))]
  
  [(subst-var x_old x_new (e_1 ...))
   ((subst-var x_old x_new e_1) ...)]
  
  [(subst-var x_old x_new (get-field e_1 e_2))
   (get-field (subst-var x_old x_new e_1) (subst-var x_old x_new e_2))]
  
  [(subst-var x_old x_new (update-field e_1 e_2 e_3))
   (update-field (subst-var x_old x_new e_1)
                 (subst-var x_old x_new e_2)
                 (subst-var x_old x_new e_3))]
  
  [(subst-var x_old x_new (delete-field e_1 e_2))
   (delete-field (subst-var x_old x_new e_1)
                 (subst-var x_old x_new e_2))]
  
  [(subst-var x_old x_new (set! e_1 e_2))
   (set! (subst-var x_old x_new e_1)
         (subst-var x_old x_new e_2))]
  
  [(subst-var x_old x_new (ref e))
   (ref (subst-var x_old x_new e))]
  
  [(subst-var x_old x_new (deref e))
   (deref (subst-var x_old x_new e))]
  
  [(subst-var x_old x_new (+ e_l e_r))
   (+ (subst-var x_old x_new e_l)
      (subst-var x_old x_new e_r))]
  
  [(subst-var x_old x_new (block e_1 ...))
   (block (subst-var x_old x_new e_1) ...)]
  
  
  [(subst-var x_old x_new x_old) x_new]
  [(subst-var x_old x_new x_other) x_other]
  [(subst-var x_old x_new v) v])


;; -----------------------------------------------------------------------------


;; Q1. How does λ_JS model JavaScript's feature of operations of objects? 
;;     Especially, how the name of the field can be computed at runtime?

;; A1. (a) The name of the field need not be specified statically. Field names 
;;         can be computed at runtime.

;; Example of λ_JS Model: 
(define ex1-1
  (term (let ([aaa (ref (obj ["x" 500] ["y" 100]))]) 
          (let ([select (λ (name) (get-field (deref aaa) name))])
            (+ (select "x")
               (select "y"))))))

(test-equal (term (eval-λJS ,ex1-1)) (term 600))

;;     (b) A program that looks up a non-existent field does not result in an 
;;         error. JavaScript returns the value 'undefined'.

;; Example of λ_JS Model:
(define ex1-2 
  (term (let ([bbb (ref (obj ["x" 0]))])
          (get-field (deref bbb) "y"))))

(test-equal (term (eval-λJS  ,ex1-2)) (term undefined))

;;     (c) Field update in JavaScript is conventional.

;; Example of λ_JS Model:
(define ex1-3
  (term (let ([ccc (ref (obj ["x" 0]))])
          (update-field (deref ccc) "x" 10))))

(test-equal (term (eval-λJS ,ex1-3)) (term (obj ["x" 10])))

;;     (d) JavaScript lets us delete fields from objects.

;; Example of λ_JS model:
(define ex1-4
  (term (let ([ddd (ref (obj ["x" 7] ["y" 13]))])
          (delete-field (deref ddd) "x"))))

(test-equal (term (eval-λJS ,ex1-4)) (term (obj ["y" 13])))


;; -----------------------------------------------------------------------------


;; Q.2. How does λ_JS model JavaScript's feature of implicit "this"?

;; A.2. The implicit "this" in JavaScript will be desugared into an explicit
;;      argument of functions in λ_JS.

;; JavaScript Code:

;; var ob = {
;;   "x" : 0;
;;   "setX" : function(val) { this.x = val } };

;; //"window" is the name of the global object in Web browser

;; We do the following desugaring process by hand and get:
(define ex2-1
  (term (let ([ob (ref (obj ["x" 0]
                            ["setX" (λ (this val) 
                                      (let ([tmp (deref this)])
                                        (let ([tmp1 (update-field tmp "x" val)])
                                          (set! this tmp1))))]))])
          (let ([window (ref (obj ))])
            (block ((get-field (deref ob) "setX") ob 10)
                   (get-field (deref window) "x"))))))

;; window.x → ... → undefined
(test-equal (term (eval-λJS ,ex2-1)) (term undefined))

;; ob.setX(10);

(define ex2-2
  (term (let ([ob (ref (obj ["x" 0]
                            ["setX" (λ (this val) 
                                      (let ([tmp (deref this)])
                                        (let ([tmp1 (update-field tmp "x" val)])
                                          (set! this tmp1))))]))])
          (let ([window (ref (obj ))])
            (block ((get-field (deref ob) "setX") ob 10)
                   (get-field (deref ob) "x"))))))

;; ob.x → ... → 10
(test-equal (term (eval-λJS ,ex2-2)) (term 10))

;; var f = obj.setX;
;; f(90);

(define ex2-3
  (term (let ([ob (ref (obj ["x" 0]
                            ["setX" (λ (this val) 
                                      (let ([tmp (deref this)])
                                        (let ([tmp1 (update-field tmp "x" val)])
                                          (set! this tmp1))))]))])
          (let ([window (ref (obj ))])
            (let ([f (get-field (deref ob) "setX")])
              (block ((get-field (deref ob) "setX") ob 10)     ;;obj.setX(10)
                     (f window 90)                             ;;f(90)
                     (get-field (deref ob) "x")))))))

;; obj.x → ... → 10
(test-equal (term (eval-λJS ,ex2-3)) (term 10))

(define ex2-4
  (term (let ([ob (ref (obj ["x" 0]
                            ["setX" (λ (this val) 
                                      (let ([tmp (deref this)])
                                        (let ([tmp1 (update-field tmp "x" val)])
                                          (set! this tmp1))))]))])
          (let ([window (ref (obj ))])
            (let ([f (get-field (deref ob) "setX")])
              (block ((get-field (deref ob) "setX") ob 10)     ;;obj.setX(10)
                     (f window 90)                             ;;f(90)
                     (get-field (deref window) "x")))))))

;; window.x → ... → 90 // window.x was created
(test-equal (term (eval-λJS ,ex2-4)) (term 90))


;; -----------------------------------------------------------------------------


;; Q.3. How does λ_JS model the prototype inheritance in JavaScript?
;; A.3. (1) Child objects inherit parent objects' fields by setting the 
;;            field "__proto__" in child objects to be the location of the
;;            parent.
;;      (2) Adding a field in child objects will not affect those fields
;;            in their parent objects.
;;      (3) If a field does not exist in child objects, λ_JS will recursively
;;            look into their parent objects by accessing the "__proto__" field.

;; Example:

;; JavaScript code:
;; var animal = {"length" : 13, "width" : 7};
;; var dog = {"__proto__" : animal, "barks" : true}
;; var lab = {"__proto__" : dog, "length" : 2}

;; lab["width"] → ... → 7

;; λ_JS code:
(define ex3-1
  (term (let ([animal (ref (obj ["length" 13] ["width" 7]))])
          (let ([dog (ref (obj ["__proto__" animal] ["barks" #t]))])
            (let ([lab (ref (obj ["__proto__" dog] ["length" 2]))])
              (get-field (deref lab) "width"))))))

(test-equal (term (eval-λJS ,ex3-1)) (term 7))

;; when we do field update in dog["width"] = 19, we will get
;; dog["width"] → ... → 19
;; animal["width"] → ... → 7 
;; lab["width"] → ... → 19

;; λ_JS code:
(define ex3-2
  (term (let ([animal (ref (obj ["length" 13] ["width" 7]))])
          (let ([dog (ref (obj ["__proto__" animal] ["barks" #t]))])
            (let ([lab (ref (obj ["__proto__" dog] ["length" 2]))])
              (block (set! dog (update-field (deref dog) "width" 19))
                     (get-field (deref dog) "width")))))))

;; dog["width"] → ... → 19
(test-equal (term (eval-λJS ,ex3-2)) (term 19)) 

(define ex3-3
  (term (let ([animal (ref (obj ["length" 13] ["width" 7]))])
          (let ([dog (ref (obj ["__proto__" animal] ["barks" #t]))])
            (let ([lab (ref (obj ["__proto__" dog] ["length" 2]))])
              (block (set! dog (update-field (deref dog) "width" 19))
                     (get-field (deref animal) "width")))))))

;; animal["width"] → ... → 7
(test-equal (term (eval-λJS ,ex3-3)) (term 7))

(define ex3-4
  (term (let ([animal (ref (obj ["length" 13] ["width" 7]))])
          (let ([dog (ref (obj ["__proto__" animal] ["barks" #t]))])
            (let ([lab (ref (obj ["__proto__" dog] ["length" 2]))])
              (block (set! dog (update-field (deref dog) "width" 19))
                     (get-field (deref lab) "width")))))))

;; lab["width"] → ... → 19
(test-equal (term (eval-λJS ,ex3-4)) (term 19))


;; -----------------------------------------------------------------------------


;; Q.4. How does λ_JS model JavaScript's constructor? 

;; To answer this question, we need to deal with the following sub-questions.
;; Q.4.a. How does λ_JS model JavaScrpt's feature that functions are objects
;;        with fields?
;; A.4.a. JavaScript's functions will be desugared into objects in λ_JS with
;;        a distinguished "code" field that refers to the actual function.

;; Q.4.b. How does λ_JS model JavaScript's feature of implicit this?
;; A.4.b. This has been answered in Q.2. 

;; Q.4.c. How does λ_JS model JavaScript's prototype inheritance?
;; A.4.c. This has been answered in Q.3.

;; A.4. Here we use the example of constructor from the paper on Page 8
;;      to illustrate those answers for the above questions.

;; The example of constructor on Page 8:

; function Point(x, y){
;   this.x = x;
;   this.y = y;
; }
; 
; pt = new Point (50, 100)

; Point.prototype.getX = function() {return this.x}
; pt.getX() → ... → pt.__proto__getX() → ... → 50

;; We do the desugaring process by hand and get:

(define ex4
  (term 
   (let ([Point 
          (ref (obj ["code" (λ (this x y) 
                              (let ([tmp0 (deref this)])
                                (let ([tmp1 (update-field tmp0 "x" x)])
                                  (let ([tmp2 (update-field tmp1 "y" y)])
                                    (set! this tmp2)))))]
                    ["prototype" 
                     (ref (obj ["getX" (λ (this) 
                                         (get-field (deref this) "x"))]
                               ["getY" (λ (this) 
                                         (get-field (deref this) "y"))]))]))])
     (let ([constr (deref Point)])
       (let ([pt (ref (obj ["__proto__" (get-field constr "prototype")]))])
         (block ((get-field constr "code") pt 50 100);; pt = new Point(50, 100)
                ((get-field (deref pt) "getX") pt)))))));; pt.getX()

;; pt.getX() → ... → 50
(test-equal (term (eval-λJS ,ex4)) (term 50))
