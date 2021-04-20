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
;; PROGRAM ORGANIZATION:

;; 1. Defining Basic ACL2 Functions
;; 2. User-Defined Palindrome Functions
;; 3. Defining Lemmas / Theorems
;; 4. Defining Iterative Palindromizing as a Function
;; 5. Mechanically Proving Iterative Palindromization in ACL2s
;; 6. Unused / Debug Code
;; 7. Full Pen and Paper Proof

;; -----------------------------------------

;; 1. Defining Basic ACL2 Functions

;; First, we define the basic ACL2 functions we are
;; using for our proof, app2 and rev2.

;; Appends the two given lists together
(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

(check= (app2 '() '()) '())
(check= (app2 '() '(a b c)) '(a b c))
(check= (app2 '(1 2 3) '()) '(1 2 3))
(check= (app2 '(3 2 1) '(c b a)) '(3 2 1 c b a))

;; Reverse the given list
(definec rev2 (x :tl) :tl
  (if (endp x)
      nil
    (app2 (rev2 (rest x)) (list (first x)))))

(check= (rev2 '()) '())
(check= (rev2 '(1)) '(1))
(check= (rev2 '(a b c)) '(c b a))
(check= (rev2 '(1 l 2 k 3 j)) '(j 3 k 2 l 1))
(check= (rev2 '(nil t nil t)) '(t nil t nil))

;; 2. User-Defined Palindrome Functions

;; Next, we define our own function representations
;; of palindromic properties, specifically palindromize
;; and palindromep.

;; turns a given list into a palindrome
(definec palindromize (ls :tl) :tl
  (if (endp ls)
      '()
    (cons (car ls) (app2 (palindromize (cdr ls)) (list (car ls))))))

(check= (palindromize '()) '())
(check= (palindromize '(a)) '(a a))
(check= (palindromize '(a b c d)) '(a b c d d c b a))
(check= (palindromize '(1 2 b c a)) '(1 2 b c a a c b 2 1))

;; Is the given list a palindrome?
(definec palindromep (l :tl) :bool
  (equal l (rev2 l)))

(check= (palindromep '()) t)
(check= (palindromep '(a b c d)) nil)
(check= (palindromep '(a b c d d c b a)) t)
(check= (palindromep '(a b c d c b a)) t)
(check= (palindromep '(1 2 3 4 5 a b c d e 5 4 3 2 1)) nil)
(check= (palindromep '(1 2 3 4 5 a b c b a 5 4 3 2 1)) t)

;; 3. Defining Lemmas / Theorems

;; We also define theorems that will be helpful in our mechanized proof.
;; Specifically, these theorems allow us to define the function
;; iteratively-palindromize, complete the theorem for
;; palindromize-id, and solve the iterative palindromization theorem at the end.

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

;; We define the theorem palindromize-id, representing a property
;; of palindromized lists that states any palindromized list
;; is itself a palindrome.

;; Proves that the palindromization of x
;; is indeed a palindrome
(defthm palindromize-id
  (implies (tlp x)
    (palindromep (palindromize x))))

;; 4. Defining Iterative Palindromizing as a Function

;; We now define iteratively-palindromize. The function will pass
;; without any help if the manual output contract is not included, but
;; for the purposes of our proof, we must explicitly show that
;; iteratively-palindromize will always return a palindromic list.
;; ACL2s must accept the previously defined theorems to prove this.

;; Recursively palindromizes a given list n times
(definec iteratively-palindromize (x :tl n :pos) :tl
  :oc (palindromep (iteratively-palindromize x n))
  (cond
   ((equal n 1) (palindromize x))
   (t (palindromize (iteratively-palindromize x (- n 1))))))

(check= (iteratively-palindromize '() 1) '())
(check= (iteratively-palindromize '() 2) '())
(check= (iteratively-palindromize '() 3) '())
(check= (iteratively-palindromize '() 10) '())
(check= (iteratively-palindromize '(c a t) 1) '(c a t t a c))
(check= (iteratively-palindromize '(c a t) 2) '(c a t t a c c a t t a c))
(check= (iteratively-palindromize '(c a t) 3) '(c a t t a c c a t t a c c a t t a c c a t t a c))
(check= (iteratively-palindromize '(1 u p) 1) '(1 u p p u 1))
(check= (iteratively-palindromize '(1 u p) 2) '(1 u p p u 1 1 u p p u 1))

;; 5. Mechanically Proving Iterative Palindromization in ACL2s

;; Finally, we propose our iteratively-palindromize conjecture
;; to ACL2s as a theorem.  Mainly using palindromize-id and
;; the output contract of iteratively-palindromize (that states
;; the function always returns a palindrome), ACL2s is able to
;; mechanically prove that a palindromized list is always a
;; palindrome, regardless of how many times it is palindromized.

;; Conjecture: A palindromize of a palindromize is a palindrome.

(thm
  (implies (and (tlp x) (posp n))
           (palindromep
            (iteratively-palindromize x n))))

#|

;; 6. Unused / Debug Code

This theorem was an older version of palindromize-id, when
the lemma suggested equality between (palindromize x) and
(rev2 (palindromize x)). While this is true, ACL2s had trouble
with using the lemma since it tended to constantly rewrite
(palindromize x) with its reversed variant and vice versa
in an endless loop. After introducing the revised palindromize-id,
the older version became redundant.

(defthm palindromize-id
  (implies (tlp x)
    (equal (palindromize x) (rev2 (palindromize x)))))

;; 7. Full Pen and Paper Proof

----------------------------

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
 
;; WE NEED A LEMMA
;; to prove that palindromize == palindromize reved

Lemma palindromize-id:
(implies (tlp x)
  (palindromep (palindromize x)))
  
Proof by: Induction on (tlp x)

Induction Case palindromize-id-base:
(implies (not (consp x))
  (implies (tlp x)
    (palindromep (palindromize x))))

Exportation:
(implies (and (not (consp x))
              (tlp x))
  (palindromep (palindromize x)))
  
Context:
C1. (not (consp x))
C2. (tlp x)

Goal:
(palindromep (palindromize x))

Proof:
(palindromep (palindromize x))
= { Def palindromize, C1 }
(palindromep nil)
= { Def palindromep }
(equal nil (rev2 nil))
= { Def rev2, Obvious }
t
 
QED

Induction Case palindromize-id-cons:
(implies (and (consp x)
              (implies (tlp (cdr x))
                       (palindromep (palindromize (cdr x)))))
  (implies (tlp x)
    (palindromep (palindromize x))))
    
Exportation:
(implies (and (consp x)
              (implies (tlp (cdr x))
                       (palindromep (palindromize (cdr x))))
              (tlp x))
    (palindromep (palindromize x)))

Context:
C1. (consp x)
C2. (tlp x)
C3. (implies (tlp (cdr x))
      (palindromep (palindromize (cdr x))))
      
Derived Context:
D1. (tlp (cdr x)) { C1, C2 }
D2. (palindromep (palindromize (cdr x))) { D1, C3 }
D3. (equal (palindromize (cdr x))
           (rev2 (palindromize (cdr x)))) { D2, Def palindromep }

Goal:
(palindromep (palindromize x))

Proof:
(palindromep (palindromize x))
= { Def palindromep }
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
= { D3 }
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

NOTE: thie iteratively-palindromize with a manual
output contract can only be proven on
the checker website when the palindromize-id lemma is
a defthm instead of a lemma in the proof.

For the pen and paper proof, we did not include the
output contract because the proof still passes
without it.

For some reason, the pen and paper proof doesn't
need the output contract to pass, but the mechanical
proof does, presumably because ACL2s takes a different
route to solve the theorem.

;; Recursively palindromizes a given list n times
(definec iteratively-palindromize (x :tl n :pos) :tl
  (cond
   ((equal n 1) (palindromize x))
   (t (palindromize (iteratively-palindromize x (- n 1))))))
  
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
= { Theorem palindromize-id ((x (iteratively-palindromize x (- n 1)))) }
t

QED

QED

---------------------------


|#