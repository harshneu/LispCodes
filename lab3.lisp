; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner

#|

For the following function definitions, find an input for which the
function does not terminate. (Therefore, these functions will not be
admitted by ACL2s -- if you type them in, comment them out later.)

Describe what would happen were you to run this function on your input.

(defunc f (x)
  :input-contract (natp x)
  :output-contract (natp (f x))
  (if (<= x 1)
    0
    (f (+ x 1))))

    ANS : The function would not terminate for x greater than 1.
...

(defunc f(x)
  :input-contract (natp x)
  :output-contract (natp (f x))
  (cond ((<= x 1)  0)
        ((evenp x) 1)
        (t         (f x))))

... ANS : The function would not terminate for odd numbers > 1
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

Without typing them in, look at the following incorrect function
definitions. What is wrong with them?

(defunc f (x)
  :input-contract (natp x)
  :output-contract (integerp (f x))
  (if (equal x 0)
    3
    (- 23 (f (+ f x)))))

... ANS :Inputs to + should be rationals

(defunc f (x)
  :input-contract (natp x)
  :output-contract (integerp (f x))
  (if (equal x 0)
    3
    (- 23 (f x (f x)))))

... ANS : f only takes a single argument as input. (f x (f x)), violates this.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

Without typing them in, find body contract violations for the following
function definitions.

That means: determine an input that satisfies the input contract of f, but
causes the input or output contract of some function in the body of f to be
violated.

Provide the offending input, and state what is wrong.

(defunc f (x)
  :input-contract (natp x)
  :output-contract (integerp (f x))
  (if (equal x 0)
    3
    (* 2 (f (- x 2)))))

... ANS : x = 1

(defunc f (x y)
  :input-contract (and (listp x) (integerp y))
  :output-contract (listp (f x y))
  (if (< y 0)
    x
    (f (rest x) (- y 1))))

... ANS : x = () y= 1

(defunc f (x y)
  :input-contract (and (listp x) (integerp y))
  :output-contract (natp (f x y))
  (if (endp x)
    (+ 1 y)
    (+ 1 (f (rest x) y))))

... ANS : X = () y= -3
|#





(defdata natlist (listof nat))

; max : natcons -> nat
;
; A natcons is a non-empty natlist. This type is not built-in. You
; therefore have to think about how to define your input contract.
;
; Function max returns the largest element of the given natcons.

(defunc max (l)
  :input-contract (and (natlistp l) (consp l))
  :output-contract (natp (max l))
  (let* (
         (first (first l))
         (rest (rest l))
                   )
  (cond 
   ((endp (rest l)) first)
   ((>= first (max rest)) first)
   (t (max rest))
   ))
  )


; Next, see if there are improvements to readability and efficiency of your
; code by using let or let*. That is, avoid repeated evaluation of the same
; expression in your code.

#|

Define a simple math expression recognizer (also known as "parser"), called exprp.
For our purposes, a "math expression" is one of the following:

- a number

- a symbol (think of it as a variable; we will permit any symbol as variable)

- a list of the form
    (- <expr>)
  where <expr> is again a math expression

- a list of the form

  (<op> <expr> <expr>)

  where <op> is one of + - * /
  and both <expr> are math expressions.

  Give ample test cases for passing and failing "parses" of your input.
  Here are some suggestions (some of these are math expressions, some aren't.)

  (exprp 1)
  (exprp 'x)
  (exprp ())
  (exprp '(- 1 2))
  (exprp '(- 1 2 3))
  (exprp '(- (* 3 (+ 1 2)) (+ 1 2)))
  (exprp '(- (* 3 (+ 1 2)) (+ 1 2) 3))
  (exprp '(- (* 3 (+ 1 2)) (sqrt 9)))

|#

#|(defunc list-checked (x)
  :input-contract (listp x)
  :output-contract (booleanp (list-checked x))
  (cond 
   ((endp x) nil)
   ((endp (rest x)) (exprp (first x)))
   ((exprp (first x)) (list-checked (rest x)))
   (t nil))
  )|#


(defunc exprp (x) 
  :input-contract t
  :output-contract (booleanp (exprp x))
  (let* ((check-primitive (or (rationalp x) (symbolp x))))
  (cond 
   (check-primitive t)
   
   ((not (listp x)) nil)
   ((endp (rest x)) (exprp (first x)))
   ((exprp (first x)) (exprp (rest x)))
   (t nil)
   )
  ))