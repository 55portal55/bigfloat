
;;; arbitrary precision floating point in scheme

;;; Author: Rick Miskowski - www.richardmiskowski.com

;;; Uses Andre van Meulebrouck's implementation of bignum integers found at
;;; http://www.mactech.com/articles/mactech/Vol.08/08.03/BigNums/index.html

(define precision 32) ; number of digits in floating point numbers

(define (number->list n base) ; convert a scheme integer to bignum digits
  (if (< n base)
    (list n)
    (cons (remainder n base) (number->list (quotient n base) base))))

(define (list->number n power base) ; convert bignum digits to scheme integer
  (if (null? n)
    0
    (+ (* power (car n)) (list->number (cdr n) (* power base) base))))

(define (drop-digit n) ; keeps mantissa in precision when operation overflows
  (cdr n))

(define (make-big-float s m e)
  ; create a bigfloat. s is the sign represented as a boolean. #t is negative.
  ; m is the mantissa represented as a bignum. e is the exponent represented
  ; as an integer.
  (let*
    ((len (length m))
     (shift (- precision (length m))))
    (if (big-zero? m)
      (list #f '() 0)
      (if (> shift 0)
        (list s (big-right-shift m shift) e)
        (list s m e)))))

(define precision-error (make-big-float #f '(1) (- precision)))

;;; simple routines to display bigfloat number

(define (display-char ch)
  (display ch))

(define (display-number n) ; only works in base 10
  (if (not (null? n))
    (begin
      (display-char (integer->char (+ (car n) (char->integer #\0))))
      (display-number (cdr n)))))

(define (display-big n) ; only works in base 10
  (if (null? n)
    (display-char #\0)
    (display-number (reverse n))))

(define (display-big-float n)
  (if (car n)
    (display-char #\-))
  (display-big (cadr n))
  (display-char #\e)
  (let
    ((e (cadr (cdr n))))
    (let
      ((s (< e 0)))
      (if s
        (display-char #\-))
      (display-number (reverse (number->list (abs e) base))))))

;;; some primitive bigfloat numbers used as constants

(define ZERO (make-big-float #f '() 0))
(define ONE (make-big-float #f '(1) 1))
(define TWO (make-big-float #f '(2) 1))
(define THREE (make-big-float #f '(3) 1))
(define FOUR (make-big-float #f '(4) 1))

(define (zero-big-float? x) ; test for zero bigfloat
  (big-zero? (cadr x))) ; ignores sign and exponent

(define (=big-float x y) ; test two bigfloats are equal
  (if (eq? x y)
    #t
    (let
      ((xs (car x))
       (xm (cadr x))
       (xe (cadr (cdr x)))
       (ys (car y))
       (ym (cadr y))
       (ye (cadr (cdr y))))
      (and (eq? xs ys)
           (equal? xm ym)
           (= xe ye)))))

;;; The next four routines are the primitive bigfloat arithmetic functions.
;;; They assume operations are performed using positive arguments.
 
(define (+X x y base)
  (if (zero-big-float? x)
    y
    (if (zero-big-float? y)
      x
      (let
        ((xs (car x))
         (xm (cadr x))
         (xe (cadr (cdr x)))
         (ys (car y))
         (ym (cadr y))
         (ye (cadr (cdr y))))
        (if (> xe ye)
          (let
            ((e (- xe ye)))
            (if (>= e precision)
              x
              (let
                ((ym (list-tail ym e)))
                (let
                  ((rm (big-add xm ym base)))
                  (if (> (length rm) precision)
                    (begin
                      (set! rm (drop-digit rm))
                      (set! xe (+ xe 1))))
                  (make-big-float #f rm xe)))))
          (if (> ye xe)
            (let
              ((e (- ye xe)))
              (if (>= e precision)
                y
                (let
                  ((xm (list-tail xm e)))
                  (let
                    ((rm (big-add ym xm base)))
                    (if (> (length rm) precision)
                      (begin
                        (set! rm (drop-digit rm))
                        (set! ye (+ ye 1))))
                    (make-big-float #f rm ye)))))
            (let ; exponents are equal
              ((rm (big-add xm ym base)))
              (if (> (length rm) precision)
                (begin
                  (set! rm (drop-digit rm))
                  (set! xe (+ xe 1))))
              (make-big-float #f rm xe))))))))

(define (-X x y base)
  (if (zero-big-float? x)
    (negate-big-float y)
    (if (zero-big-float? y)
      x
      (let
        ((xs (car x))
         (xm (cadr x))
         (xe (cadr (cdr x)))
         (ys (car y))
         (ym (cadr y))
         (ye (cadr (cdr y))))
        (if (> xe ye)
          (let
            ((e (- xe ye)))
            (if (>= e precision)
              x
              (let
                ((ym (list-tail ym e)))
                (let
                  ((rm (big-sub xm ym base)))
                  (make-big-float #f rm (- xe (- precision (length rm))))))))
          (if (> ye xe)
            (let
              ((e (- ye xe)))
              (if (>= e precision)
                (make-big-float #t ym ye)
                (let
                  ((xm (list-tail xm e)))
                  (let
                    ((rm (big-sub ym xm base)))
                    (make-big-float #t rm (- ye (- precision (length rm))))))))
            (begin ; exponents equal
              (if (big->? xm ym)
                (let
                  ((rm (big-sub xm ym base)))
                  (make-big-float #f rm (- xe (- precision (length rm)))))
                (if (big->? ym xm)
                  (let
                    ((rm (big-sub ym xm base)))
                    (make-big-float #t rm (- ye (- precision (length rm)))))
                  (make-big-float #f '() 0)))))))))) ; zero ???? use ZERO

(define (*X x y base)
  (if (=big-float x ONE)
    y
    (if (=big-float y ONE)
      x
      (let
        ((xs (car x))
         (xm (cadr x))
         (xe (cadr (cdr x)))
         (ys (car y))
         (ym (cadr y))
         (ye (cadr (cdr y))))
        (let
          ((result (big-mul xm ym base))
           (e (+ xe ye)))
          (let
            ((len (length result))
             (lenx (length xm))
             (leny (length ym)))
            (set! e (+ e (- len (+ lenx leny))))
            (if (<= len precision)
              (make-big-float #f result e)
              (make-big-float #f
                         (list-tail result (- len precision)) e))))))))

(define (/X x y base)
  (let
    ((xs (car x))
     (xm (cadr x))
     (xe (cadr (cdr x)))
     (ys (car y))
     (ym (cadr y))
     (ye (cadr (cdr y))))
    (let
      ((shift-x (- precision (length xm))) ; now length always is precision 
       (shift-y (- precision (length ym)))) ; now length always is precision
      (let
        ((xm (big-right-shift xm shift-x))
         (ym2 (big-right-shift ym shift-y)))
        (let
          ((xm (big-right-shift xm precision)))
          (let
            ((result (car (big-div xm ym2 base)))
             (e (- xe ye)))
            (if (> (length result) precision) ; if so will be by one digit
              (make-big-float #f (drop-digit result) (+ e 1))
              (make-big-float #f result e))))))))

(define (negate-big-float x)
  (let
    ((xs (car x))
     (xm (cadr x))
     (xe (cadr (cdr x))))
    (make-big-float (not xs) xm xe)))

(define (abs-big-float x)
  (let
    ((xs (car x))
     (xm (cadr x))
     (xe (cadr (cdr x))))
    (make-big-float #f xm xe))) ; make sign positive

(define (positive-big-float? x)
  (if (big-zero? (cadr x))
    #f ; zero not positive
    (let
      ((xs (car x)))
      (not xs))))

(define (negative-big-float? x)
  (let
    ((xs (car x)))
    xs))

(define (sign-product s1 s2)
  (not (or (and s1 s2) (and (not s1) (not s2)))))

;;; The four bigfloat arithmetic operations.

(define (add-big-float x y base)
  (if (and (positive-big-float? x) (positive-big-float? y))
    (+X x y base)
    (if (and (negative-big-float? x) (positive-big-float? y))
      (-X y (negate-big-float x) base)
      (if (and (positive-big-float? x) (negative-big-float? y))
        (-X x (negate-big-float y) base) 
        (negate-big-float (+X (negate-big-float x) (negate-big-float y) base))))))

(define (subtract-big-float x y base)
  (if (and (positive-big-float? x) (positive-big-float? y))
    (-X x y base)
    (if (and (negative-big-float? x) (positive-big-float? y))
      (negate-big-float (+X (negate-big-float x) y base))
      (if (and (positive-big-float? x) (negative-big-float? y))
        (+X x (negate-big-float y) base) 
        (-X (negate-big-float y) (negate-big-float x) base))))) 

(define (multiply-big-float x y base)
  (let
    ((z (*X x y base)))
    (let
      ((zs (car z))
       (zm (cadr z))
       (ze (cadr (cdr z))))
      (set! zs (sign-product (car x) (car y)))
      (make-big-float zs zm ze))))

(define (divide-big-float x y base)
  (if (zero-big-float? y) ; divide by zero
    ZERO
    (let
      ((z (/X x y base)))
      (let
        ((zs (car z))
         (zm (cadr z))
         (ze (cadr (cdr z))))
        (set! zs (sign-product (car x) (car y)))
        (make-big-float zs zm ze)))))

;;; bigfloat comparison functions

(define (<big-float x y base)
  (let
    ((z (subtract-big-float x y base)))
    (and (car z) (not (zero-big-float? z)))))

(define (<=big-float x y base)
  (let
    ((z (subtract-big-float x y base)))
    (or (car z) (zero-big-float? z))))

(define (>big-float x y base)
  (let
    ((z (subtract-big-float x y base)))
    (and (not (car z)) (not (zero-big-float? z)))))

(define (>=big-float x y base)
  (let
    ((z (subtract-big-float x y base)))
    (or (not (car z)) (zero-big-float? z))))
