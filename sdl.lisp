
;;; The syntax of Standard Deontic Logic axiomatized in FOL.
;;; http://plato.stanford.edu/entries/logic-deontic/#2.1
;;; Naveen Sundar Govindarajulu,
;;; RAIR Lab
;;; Rensselaer Polytechnic Institute
;;; Summer 2012
;;; Changed: January 2014


;;; SDL \vdash represented by holds in FOL. 
;;; Axioms become unconditional holds statements. 

(in-package :snark-user)


(defparameter *A2*
  '(forall ((?p proposition) (?q proposition))
    (holds 
     (implies!
      (Ob (implies! ?p ?q))
      (implies! 
        (Ob ?p)
	(Ob ?q))))))

(defparameter *A3*
  '(forall ((?p proposition))
    (holds 
     (implies!
      (Ob ?p)
      (not! (Ob (not! ?p)))))))

(defparameter *R1*
  '(forall ((?p proposition) (?q proposition)) 
    (implies 
     (and (holds ?p) (holds (implies! ?p ?q))) 
     (holds ?q))))

(defparameter *R2*
  '(forall ((?p proposition)) 
    (implies 
     (holds ?p) 
     (holds (Ob ?p)))))

(defparameter *not!*
  '(forall ((?p proposition))
    (iff
     (holds (not! ?p))
     (not (holds ?p)))))

(defparameter *or!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (or! ?p ?q))
     (or (holds ?p) (holds ?q)))))

(defparameter *and!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (and! ?p ?q))
     (and (holds ?p) (holds ?q)))))

(defparameter *implies!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (implies! ?p ?q))
     (implies (holds ?p) (holds ?q)))))


(defparameter *iff!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (iff! ?p ?q))
     (iff (holds ?p) (holds ?q)))))

(defparameter *ob-rm* 
  '(forall ((?p proposition) (?q proposition)) 
    (implies 
     (holds (implies! p q)) 
     (holds (implies! (Ob p) (Ob q))))))


(defparameter *ob-re* 
  '(forall ((?p proposition) (?q proposition)) 
    (implies 
     (holds (iff! p q)) 
     (holds (iff! (Ob p) (Ob q))))))

(defparameter *ded* 
  '(forall ((?p proposition) (?q proposition)) 
    (iff 
     (implies 
      (holds ?p) 
      (holds ?q))
     (holds (implies! ?p ?q)))))

(defparameter *Im-def*
  '(forall ((?p proposition))
    (iff (holds (Ob (not! ?p)))
     (holds (Im  ?p)))))


;;; aux statements are useful theorems of SDL included here for faster theorem proving.
(defparameter *aux-1*
  '(forall ((?p proposition) (?q proposition))
    (implies (holds (implies! ?p ?q)) 
	    (holds (implies! (Ob ?p) (Ob ?q))))))

(defparameter *aux-2*
  '(forall ((?p proposition) (?q proposition))
    (implies (holds (implies! ?q ?p)) 
	    (holds (implies! (Im ?p) (Im ?q))))))

(defparameter *aux-3*
  '(forall ((?p proposition))
    (not  (and (holds (Ob ?p)) 
	   (holds (Im ?p))))))


(defun test-pc (w)
  (snark:initialize)
  (use-hyperresolution t)
  (use-paramodulation t)
  (mapcar #'assert (list *not!* *and!* *or!* *iff!* *implies!*))
  (prove w))

(defun snark-deverbose ()
 (snark:print-options-when-starting  nil)
  (snark:print-agenda-when-finished nil)
  (snark:print-clocks-when-finished nil)
  (snark:print-final-rows nil)
  (snark:print-symbol-table-warnings nil)
  (snark:print-summary-when-finished nil)
  (snark:print-row-answers nil)
  (snark:print-row-goals nil) 
  (snark:print-rows-when-derived nil)
  (snark:print-row-reasons nil)
  (snark:print-row-partitions nil)
  (snark:print-rows-prettily nil)
  (snark:print-rows :min 0 :max 0))

(defun prove-r-sdl (w &optional (premises nil) (silent t))
  (snark:initialize)
  (if silent (snark-deverbose))
  (declare-sort 'proposition)
  (declare-constant 's :sort 'proposition)
  (declare-constant 'a :sort 'proposition)
  (declare-constant 'p :sort 'proposition)
  (declare-constant 'q :sort 'proposition)

  ;; (declare-constant 'search-and-rescue-mode :sort 'proposition)
  ;; (declare-constant 'transportation-mode :sort 'proposition)
  (declare-constant 'needs-money :sort 'proposition)
  (declare-constant 'takes-care-of-needs :sort 'proposition)
  (declare-constant 'other-legal-activity :sort 'proposition)
  (declare-constant 'sell-drug :sort 'proposition)
  (declare-constant 'have-money :sort 'proposition)
  (declare-constant 'give-money :sort 'proposition)
  (declare-constant 'illegal-act :sort 'proposition)

  (declare-relation 'holds 1 :sort '(proposition))
  (declare-function 'and! 2 :sort '(proposition proposition proposition))
  (declare-function 'or! 2 :sort '(proposition proposition proposition))
  (declare-function 'implies! 2 :sort '(proposition proposition proposition))
  (declare-function 'iff! 2 :sort '(proposition proposition proposition))
  (declare-function 'not! 1 :sort '(proposition  proposition))
  (declare-function 'Ob 1 :sort '(proposition  proposition))
  (declare-function 'Im 1 :sort '(proposition  proposition))
  
  (use-resolution t)
  (use-paramodulation t)
  ;(use-hyperresolution t)
  (mapcar #'assert 
	  (list *not!* *and!* *or!* *iff!* *implies!*
		*A2* *A3* *R1* *R2* *Im-def*
		*aux-1* *aux-2* *aux-3*
		 ;*ob-rm* *ob-re* *ded*
		))
  (mapcar #'assert premises)
  (if (equalp (prove w) :PROOF-FOUND)
      (progn (format t "------------PROOF FOUND------------")
	     (print-proof))))


(defparameter *contradiction* '(and P (not P)))
(defun tests ()
  (every (lambda (result) (equalp :PROOF-FOUND result))
	 (list
	   (prove-r-sdl '(holds (Ob (or! s (not! s)))))
	   (prove-r-sdl '(holds (not! (Ob (and! s (not! s))))))
	   ;; if |- p -> q then |- Ob(p) -> Ob(q)
	   (prove-r-sdl '(implies (holds (implies! p q)) 
			  (holds (implies! (Ob p) (Ob q)))))
	   ;; if |- q -> p then |- Ob(q) -> Ob(p)
	  (prove-r-sdl '(implies (holds (implies! q p))
			    (holds (implies! (Im p) (Im q))))))))


(defun print-proof ()
  (pprint (snark:row-ancestry (snark:proof)))
  (pprint (mapcar 'snark:row-reason (snark:row-ancestry (snark:proof)))))