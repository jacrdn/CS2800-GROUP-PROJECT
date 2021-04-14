; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;; Determines the length of the given list
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

;; Appends the two given lists together
(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

;; Reverse the given list
(definec rev2 (x :tl) :tl
  (if (endp x)
      nil
    (app2 (rev2 (rest x)) (list (first x)))))

;; turns a given list into a palindrome
(definec palindromize (ls :tl) :tl
  (if (endp ls)
      '()
    (cons (car ls) (app2 (palindromize (cdr ls)) (list (car ls))))))

;; Is the given list a palindrome?
(definec palindromep (l :tl) :bool
  (equal l (rev2 l)))

;; Recursively palindromizes a given list n times
(definec iteratively-palindromize (x :tl n :pos) :tl
  (cond
   ((equal n 1) (palindromize x))
   (t (palindromize (iteratively-palindromize x (- n 1))))))

;; need:
;; -defthms to help solve the thm
;; --found by doing the pen and paper proof
;; ---we need lemmas for said pen and paper proof

;; Proves the associativity of app2
(defthm app2-assoc 
  (implies (and (tlp x) (tlp y) (tlp z))
    (equal (app2 x (app2 y z)) (app2 (app2 x y) z))))

;; Proves that the reverse of two appended lists is equal to
;; appending the reverse of the second list to the reverse of the first
(defthm rev2-app2
  (implies (and (tlp x) (tlp y))
    (equal (rev2 (app2 x y))
           (app2 (rev2 y) (rev2 x)))))

;; Proves that the palindromization of x is the same as
;; the reverse of the palindromization of x
(defthm palindromize-id
  (implies (tlp x)
    (equal (palindromize x) (rev2 (palindromize x)))))#|ACL2s-ToDo-Line|#


;; Conjecture: A palindromize of a palindromize is a palindrome.

(thm
  (implies (and (tlp x) (posp n))
           (palindromep
            (iteratively-palindromize x n)))
  ;;:hints (("Goal" :in-theory (disable palindromize-id))))
)
#|

Pen and Paper Proof:

----------------------------

;; Determines the length of the given list
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

;; Appends the two given lists together
(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

;; Reverse the given list
(definec rev2 (x :tl) :tl
  (if (endp x)
      nil
    (app2 (rev2 (rest x)) (list (first x)))))

;; turns a given list into a palindrome
(definec palindromize (ls :tl) :tl
  (if (endp ls)
      '()
    (cons (car ls) (app2 (palindromize (cdr ls)) (list (car ls))))))

(defthm app2-assoc 
  (implies (and (tlp x) (tlp y) (tlp z))
    (equal (app2 x (app2 y z)) (app2 (app2 x y) z))))

;; Is the given list a palindrome?
(definec palindromep (l :tl) :bool
  (equal l (rev2 l)))

;; Recursively palindromizes a given list n times
(definec iteratively-palindromize (x :tl n :pos) :tl
  (cond
   ((equal n 1) (palindromize x))
   (t (palindromize (iteratively-palindromize x (- n 1))))))
   
(defthm rev2-app2
  (implies (and (tlp x) (tlp y))
    (equal (rev2 (app2 x y))
           (app2 (rev2 y) (rev2 x)))))
 
;; WE NEED A LEMMA
;; to prove that palindromize == palindromize reved

Lemma palindromize-id:
(implies (tlp x)
  (equal (palindromize x) (rev2 (palindromize x))))
  
Proof by: Induction on (tlp x)

Induction Case palindromize-id-base:
(implies (not (consp x))
  (implies (tlp x)
    (equal (palindromize x) (rev2 (palindromize x)))))

Exportation:
(implies (and (not (consp x))
              (tlp x))
  (equal (palindromize x) (rev2 (palindromize x))))
  
Context:
C1. (not (consp x))
C2. (tlp x)

Goal:
(equal (palindromize x) (rev2 (palindromize x)))

Proof:
(equal (palindromize x) (rev2 (palindromize x)))
= { Def palindromize, C1 }
(equal nil (rev2 nil))
= { Def rev2, Obvious }
t
 
QED

Induction Case palindromize-id-cons:
(implies (and (consp x)
              (implies (tlp (cdr x))
                       (equal (palindromize (cdr x)) (rev2 (palindromize (cdr x))))))
  (implies (tlp x)
    (equal (palindromize x) (rev2 (palindromize x)))))
    
Exportation:
(implies (and (consp x)
              (implies (tlp (cdr x))
                       (equal (palindromize (cdr x)) (rev2 (palindromize (cdr x)))))
              (tlp x))
    (equal (palindromize x) (rev2 (palindromize x))))

Context:
C1. (consp x)
C2. (tlp x)
C3. (implies (tlp (cdr x))
      (equal (palindromize (cdr x)) (rev2 (palindromize (cdr x)))))
      
Derived Context:
D1. (tlp (cdr x)) { C1, C2 }
D2. (equal (palindromize (cdr x)) (rev2 (palindromize (cdr x)))) { D1, C3 }

Goal:
(equal (palindromize x) (rev2 (palindromize x)))

Proof:
(equal (palindromize x) (rev2 (palindromize x)))
= { Def palindromize, C1 }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (rev2 (palindromize x)))
= { Def palindromize, C1 }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (rev2 (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))))
= { Def rev2 }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (app2 (rev2 (rest (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))))
             (list (first (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))))))
= { Car-cdr axioms }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (app2 (rev2 (app2 (palindromize (cdr x)) (cons (car x) nil))) (list (car x))))
= { Theorem rev2-app2 ((x (palindromize (cdr x))) (y (cons (car x) nil))) }
(equal (cons (car x) (app2 (palindromize (cdr x)) (cons (car x) nil)))
       (app2 (app2 (rev2 (list (car x))) (rev2 (palindromize (cdr x)))) (list (car x))))
= { D2 }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (app2 (app2 (rev2 (cons (car x) nil)) (palindromize (cdr x))) (list (car x))))
= { Def rev2, Car-cdr axioms, Obvious }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (app2 (app2 (app2 nil (list (car x))) (palindromize (cdr x))) (list (car x))))
= { Def app2, Obvious }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (app2 (app2 (list (car x)) (palindromize (cdr x))) (list (car x))))
= { Theorem app2-assoc ((x (list (car x))) (y (palindromize (cdr x))) (z (list (car x)))) }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (app2 (list (car x)) (app2 (palindromize (cdr x)) (list (car x)))))
= { Def app2, Obvious }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (cons (first (list (car x))) (app2 (rest (list (car x))) (app2 (palindromize (cdr x)) (list (car x))))))
= { Car-cdr axioms }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (cons (car x) (app2 nil (app2 (palindromize (cdr x)) (list (car x))))))
= { Def app2, Obvious }
(equal (cons (car x) (app2 (palindromize (cdr x)) (list (car x))))
       (cons (car x) (app2 (palindromize (cdr x)) (list (car x)))))
= { Obvious }
t

QED

QED
  
;; THE BIG CONJECTURE
Conjecture ultimate-proof:
(implies (and (tlp x) (posp n))
  (palindromep (iteratively-palindromize x n)))

Proof by: Induction on (iteratively-palindromize x n)

Induction Case ultimate-proof-contract:
(implies (not (and (tlp x) (posp n)))
  (implies (and (tlp x) (posp n))
    (palindromep (iteratively-palindromize x n))))

Exportation:
(implies (and (not (and (tlp x) (posp n)))
              (tlp x)
              (posp n))
  (palindromep (iteratively-palindromize x n)))

Context:
C1. (not (and (tlp x) (posp n)))
C2. (tlp x)
C3. (posp n)

Derived Context:
D1. nil { C1, C2, C3 }

QED

Induction Case ultimate-proof-base:
(implies (and (tlp x) (posp n) (equal n 1))
  (implies (and (tlp x) (posp n))
    (palindromep (iteratively-palindromize x n))))
    
Exportation:
(implies (and (tlp x)
              (posp n)
              (equal n 1))
  (palindromep (iteratively-palindromize x n)))

Context:
C1. (tlp x)
C2. (posp n)
C3. (equal n 1)

Goal:
(palindromep (iteratively-palindromize x n))

Proof:
(palindromep (iteratively-palindromize x n))
= { Def iteratively-palindromize }
(palindromep (cond
               ((equal n 1) (palindromize x))
               (t (palindromize (iteratively-palindromize x (- n 1))))))
= { C3 }
(palindromep (palindromize x))
= { Def palindromep }
(equal (palindromize x) (rev2 (palindromize x)))
= { Lemma palindromize-id ((x x)) }
t
   
QED

Induction Case ultimate-proof-ind:
(implies (and (tlp x) (posp n) (not (equal n 1))
              (implies (and (tlp x) (posp (- n 1)))
                       (palindromep (iteratively-palindromize x (- n 1)))))
  (implies (and (tlp x) (posp n))
    (palindromep (iteratively-palindromize x n))))

Exportation:
(implies (and (tlp x) (posp n) (not (equal n 1))
              (implies (and (tlp x) (posp (- n 1)))
                       (palindromep (iteratively-palindromize x (- n 1)))))
  (palindromep (iteratively-palindromize x n)))

Context:
C1. (tlp x)
C2. (posp n)
C3. (not (equal n 1))
C4. (implies (and (tlp x) (posp (- n 1)))
                  (palindromep (iteratively-palindromize x (- n 1))))

Derived Context:
D1. (posp (- n 1)) { C2, C3 }
D2. (palindromep (iteratively-palindromize x (- n 1))) { C1, D1, C4 }

Goal:
(palindromep (iteratively-palindromize x n))

Proof:
(palindromep (iteratively-palindromize x n))
= { Def iteratively-palindromize }
(palindromep (cond
               ((equal n 1) (palindromize x))
               (t (palindromize (iteratively-palindromize x (- n 1))))))
= { C3 }
(palindromep (palindromize (iteratively-palindromize x (- n 1))))
= { Def palindromep }
(equal (palindromize (iteratively-palindromize x (- n 1)))
       (rev2 (palindromize (iteratively-palindromize x (- n 1)))))
= { Theorem palindromize-id ((x (iteratively-palindromize x (- n 1)))) }
t

QED

QED
---------------------------


|#
