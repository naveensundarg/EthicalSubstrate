(in-package :snark-user)



(defparameter *COLT-OB* 
  (list
   '(Ob take-care-of-needs)))


(defparameter *KB_GEN*
  (list '(holds needs-money)
	'(holds (not! other-legal-activity))))

(defparameter *KB_Robot* 
  (list
   '(holds takes-care-of-needs)
   '(holds (implies! (and! takes-care-of-needs needs-money) give-money))
   '(holds (implies! give-money have-money))
   '(holds (implies! have-money (or! sell-drug other-legal-activity)))
   '(holds (implies! sell-drug illegal-act))))

(defparameter *KB_IM*
  (list '(holds (Im illegal-act))))


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
