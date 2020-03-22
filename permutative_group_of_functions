(*

=================================================================
                 PERMUTATIVE GROUP OF FUNCTIONS
=================================================================

The permutative group of functions is defined as a single axiom:

                                        ∃ n : nat { f^n <=> id }

It has been proved that this axiom implies the axioms of Group Theory
for any natural number `n`:

https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/permutation-group-of-functions.pdf

This makes it possible to prove formally with a proof assistant whether
a function generates a permutative group.

Here are some simple examples.

Checked with Coq IDE 8.11.0 (https://coq.inria.fr/)

*)

(* Function composition *)
Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

(* Recursive composition `f^n` *)
Fixpoint compn {A : Type} (f : A -> A) (n : nat) :=
  match n with
  | 0 => fun x : A => x
  | 1 => fun x : A => f x
  | S r => fun x : A => (compn f r) (f x)
  end.

(* Identity function *)
Definition id {A : Type} := fun x: A => x.

(* Permutation group of functions *)
Definition fgroup {A : Type} (f : A -> A) :=
  exists n : nat, (compn f n) = @id A.

(* Prove that identity function of natural numbers is a group *)
Theorem id_nat_is_fgroup : fgroup (@id nat).
Proof.
  unfold id.
  unfold fgroup.
  pose (two := 2).
  refine (ex_intro _ two _).
  unfold compn.
  auto.
Qed.

(* Prove that identity function of any type is a group *)
Theorem id_is_fgroup (A : Type) : fgroup (@id A).
Proof.
  unfold id.
  unfold fgroup.
  pose (two := 2).
  refine (ex_intro _ two _).
  unfold compn.
  auto.
Qed.

(* Logical NOT *)
Definition not := fun x : bool =>
  match x with
  | true => false
  | false => true
  end.

(* Use functional extensionality *)
From Coq Require Import FunctionalExtensionality.

(* Prove logical NOT is a group *)
Theorem not_is_fgroup : fgroup not.
Proof.
  pose (two := 2).
  refine (ex_intro _ two _).
  compute.
  apply functional_extensionality.
  intro b.
  elim b.
  reflexivity.
  reflexivity.
Qed.

Inductive nat3 : Set :=
  | one : nat3
  | two : nat3
  | three : nat3.

Definition one_two_three := fun x : nat3 =>
  match x with
  | one => two
  | two => three
  | three => one
  end.

Theorem one_two_three_is_fgroup : fgroup one_two_three.
Proof.
  pose (x := 3).
  refine (ex_intro _ x _).
  compute.
  apply functional_extensionality.
  intro y.
  (* Prove case by case and apply reflexivity to each branch *)
  elim y; reflexivity.
Qed.
