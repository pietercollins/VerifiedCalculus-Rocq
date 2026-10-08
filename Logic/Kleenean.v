From Stdlib Require Import Logic.ConstructiveEpsilon.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import SetoidClass.

Require Import Topologic.


(*
Module Kleeneans.
*)

Notation Boolean := bool.

Notation B := Boolean.
Notation succ := S.


Inductive Basic : Set := 
  | unknown | known : B -> Basic.

Module Basic.

Ltac destr_kleene :=
 intros; destruct_all Basic; destruct_all bool; simpl in *; trivial; try discriminate.

Notation tru := (known true).
Notation indt := (unknown).
Notation fls := (known false).

Definition definitely (tb : Basic) : B :=
  match tb with | known true => true | _ => false end.
Definition possibly (tb : Basic) : B :=
  match tb with | known false => false | _ => true end.

Definition refines (tb1 tb2 : Basic) : Prop :=
  match tb1, tb2 with
  | _, indt => True
  | tru, tru => True
  | fls, fls => True
  | _, _ => False
  end.

Lemma refines_refl : Relation_Definitions.reflexive Basic refines.
Proof. unfold Relation_Definitions.reflexive. destr_kleene. Qed.

Lemma refines_trans : Relation_Definitions.transitive Basic refines.
Proof. unfold Relation_Definitions.transitive. destr_kleene. Qed.

Instance refines_is_reflexive : RelationClasses.Reflexive refines := refines_refl.
Instance refines_is_transitive : RelationClasses.Transitive refines := refines_trans.

Instance Basis : BasicTopologic.Basis (Basic) :=
{
  refines := refines;
  refines_refl := refines_refl;
  refines_trans := refines_trans;
}.


Local Definition common_of (b1 b2 : B) : Basic :=
  match b1, b2 with
  | true, true => known true
  | false, false => known false
  | _, _ => unknown
  end.

Local Definition common_of_four (b1 b2 b3 b4 : B) : Basic :=
  match b1, b2, b3, b4 with
  | true, true, true, true => known true
  | false, false, false, false => known false
  | _, _, _, _ => unknown
  end.

Local Definition lift_kleene (op : B -> B) (k : Basic) : Basic :=
  match k with 
  | unknown => common_of (op false) (op true)
  | known b => known (op b)
  end.

Local Definition lift_binary_kleene (op : B -> B -> B) (k1 : Basic) (k2 : Basic) : Basic :=
  match k1, k2 with 
  | unknown, unknown => common_of_four (op true true) (op true false) (op false true) (op false false)
  | unknown, known b2 => lift_kleene (fun b1 => op b1 b2) k1
  | known b1, unknown => lift_kleene (op b1) k2
  | known b1, known b2 => known (op b1 b2)
  end.

Local Definition not' := lift_kleene negb.
Local Definition impl' := lift_binary_kleene implb.
Local Definition and' := lift_binary_kleene andb.
Local Definition or' := lift_binary_kleene orb.
Local Definition iff' := lift_binary_kleene Bool.eqb.


Definition not (t : Basic) : Basic :=
  match t with
  | fls => tru
  | indt => indt
  | tru => fls
  end.

Definition impl (t1 t2 : Basic) : Basic :=
  match (t1,t2) with
  | (fls,_) => tru
  | (_,tru) => tru
  | (indt,_) => indt
  | (_,indt) => indt
  | (_,_) => fls
  end.

Definition and (t1 t2 : Basic) : Basic :=
  match (t1,t2) with
  | (fls,_) => fls
  | (_,fls) => fls
  | (indt,_) => indt
  | (_,indt) => indt
  | (_,_) => tru
  end.

Definition or (t1 t2 : Basic) : Basic :=
  match (t1,t2) with
  | (tru,_) => tru
  | (_,tru) => tru
  | (indt,_) => indt
  | (_,indt) => indt
  | (_,_) => fls
  end.

Definition iff (t1 t2 : Basic) : Basic :=
  match (t1,t2) with
  | (indt,_) => indt
  | (_,indt) => indt
  | (tru,tru) => tru
  | (fls,fls) => tru
  | (tru,fls) => fls
  | (fls,tru) => fls
  end.

Local Lemma impl_same : forall k1 k2, impl k1 k2 = impl' k1 k2.
Proof. destr_kleene. Qed.
Local Lemma and_same : forall k1 k2, and k1 k2 = and' k1 k2.
Proof. destr_kleene. Qed.
Local Lemma or_same : forall k1 k2, or k1 k2 = or' k1 k2.
Proof. destr_kleene. Qed.
Local Lemma iff_same : forall k1 k2, iff k1 k2 = iff' k1 k2.
Proof. destr_kleene. Qed.


Definition of_Bool : B -> Basic :=
  fun b => known b.

Lemma eq_dne : forall t1 t2 : Basic, ~ (t1 <> t2) -> t1 = t2. 
Proof. destr_kleene. all:exfalso; apply H; discriminate. Qed.

Lemma eq_dec : forall (t1 t2 : Basic), {t1 = t2} + {t1 <> t2 }.
Proof. destr_kleene. 1,6,9: left; reflexivity. all: right; discriminate. Qed.

Lemma not_eq_dec : forall (t1 t2 : Basic), {t1 <> t2} + {~ t1 <> t2 }.
Proof. destr_kleene. 1,6,9: right; intro H; apply H; reflexivity. all: left; discriminate. Qed.

Lemma tru_or_fls_dec : forall t, (t = tru \/ t = fls) -> {t=tru} + {t=fls}.
Proof. 
  destr_kleene.
  - exfalso. destruct H; discriminate.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma tru_or_fls_iff_not_indt : forall t: Basic, t = tru \/ t = fls <-> t <> indt.
Proof. 
  intro t. destruct_all Basic; destruct_all B.
  - split. intros Htf Hni; destruct Htf; discriminate. intro H. exfalso; apply H; reflexivity.
  - split. discriminate. intro H; left; reflexivity.
  - split. discriminate. intro H; right; reflexivity.
Qed.



Lemma impl_tru : forall t1 t2, impl t1 t2 = tru -> t1 = fls \/ t2 = tru.
Proof. destr_kleene. all: tauto. Qed.

Lemma impl_fls : forall t1 t2, impl t1 t2 = fls -> t1 = tru /\ t2 = fls.
Proof. destr_kleene. all: tauto. Qed.

Lemma and_tru : forall t1 t2, and t1 t2 = tru -> t1 = tru /\ t2 = tru.
Proof. destr_kleene. all: tauto. Qed.

Lemma and_fls: forall t1 t2 : Basic, and t1 t2 = fls -> t1 = fls \/ t2 = fls.
Proof. destr_kleene. all: tauto. Qed.

Lemma or_tru : forall t1 t2, or t1 t2 = tru -> t1 = tru \/ t2 = tru.
Proof. destr_kleene. all: tauto. Qed.

Lemma or_fls: forall t1 t2 : Basic, or t1 t2 = fls -> t1 = fls /\ t2 = fls.
Proof. destr_kleene. all: tauto. Qed.



Lemma not_eq_impl_fls : forall t, not t = impl t fls.
Proof. destr_kleene. all: tauto. Qed.

Lemma or_eq_impl_not : forall t1 t2, or t1 t2 = impl (not t1) t2.
Proof. destr_kleene. all: tauto. Qed.

Lemma and_eq_not_impl_not : forall t1 t2, and t1 t2 = not (impl t1 (not t2)).
Proof. destr_kleene. all: tauto. Qed.

Lemma iff_eq_impl_and_rimpl : forall t1 t2, iff t1 t2 = and (impl t1 t2) (impl t2 t1).
Proof. destr_kleene. all: tauto. Qed.

Lemma and_eq_not_or_not : forall t1 t2, and t1 t2 = not (or (not t1) (not t2)).
Proof. destr_kleene. all: tauto. Qed.

Lemma or_eq_not_and_not : forall t1 t2, or t1 t2 = not (and (not t1) (not t2)).
Proof. destr_kleene. all: tauto. Qed.

Lemma impl_eq_or_not : forall t1 t2, impl t1 t2 = or (not t1) t2.
Proof. destr_kleene. all: tauto. Qed.

Lemma not_is_monotone_operator : 
  @BasicTopologic.is_monotone_unary_operator Basic Basic.Basis not.
Proof. unfold BasicTopologic.is_monotone_unary_operator. destr_kleene. Qed.

Lemma impl_is_monotone_operator : BasicTopologic.is_monotone_binary_operator impl.
Proof. unfold BasicTopologic.is_monotone_binary_operator. destr_kleene. Qed.

Lemma and_is_monotone_operator : BasicTopologic.is_monotone_binary_operator and.
Proof. unfold BasicTopologic.is_monotone_binary_operator. destr_kleene. Qed.

Lemma or_is_monotone_operator : BasicTopologic.is_monotone_binary_operator or.
Proof. unfold BasicTopologic.is_monotone_binary_operator. destr_kleene. Qed.

Lemma iff_is_monotone_operator : BasicTopologic.is_monotone_binary_operator iff.
Proof. unfold BasicTopologic.is_monotone_binary_operator. destr_kleene. Qed.

End Basic.






Section PreKleeneSection.

Context `{N : Set} `{Lattice_N : Lattice N}.
Infix "<=" := le.

Notation B := bool.
Notation succ := S.

Import Basic.

Notation TB := Basic.
Notation TBBasis := Basic.Basis.

Notation TBtru := Basic.tru.
Notation TBindt := Basic.indt.
Notation TBfls := Basic.fls.
Notation TBnot := Basic.not.
Notation TBimpl := Basic.impl.
Notation TBand := Basic.and.
Notation TBor := Basic.or.
Notation TBiff := Basic.iff.


Definition is_monotone := @BasicTopologic.is_monotone N Lattice_N Basic Basic.Basis.

Lemma is_monotone_tru_fls : forall (tbs : N -> Basic),
  is_monotone tbs -> forall (m n : N), m <= n ->
  (tbs m = Basic.tru -> tbs n = Basic.tru) /\ (tbs m = Basic.fls -> tbs n = Basic.fls).
Proof.
  unfold is_monotone, BasicTopologic.is_monotone.
  intros tbs H m n Hmn.
  pose proof (H m n Hmn) as Hnm.
  split.
  - destruct (tbs m); destruct (tbs n).
    all: unfold BasicTopologic.refines in Hnm; simpl in Hnm.
    -- intro H'; discriminate H'.
    -- intro H'; discriminate H'.
    -- contradiction.
    -- destruct b, b0; tauto.
  - destruct (tbs m); destruct (tbs n).
    all: unfold BasicTopologic.refines in Hnm; simpl in Hnm.
    -- intro H'; discriminate H'.
    -- intro H'; discriminate H'.
    -- contradiction.
    -- destruct b, b0; tauto.
Qed.

Lemma is_monotone_indt : forall (tbs : N -> Basic), 
  is_monotone tbs -> forall m n, (m <= n -> tbs n = Basic.indt -> tbs m = Basic.indt).
Proof.
  intros tbs H m n Hmn.
  pose proof (is_monotone_tru_fls tbs H) as Htf. 
  intros Hn. destruct (Htf m n Hmn) as [Ht Hf].
  destruct (tbs n).
  - destruct (tbs m). 2: destruct b. 
    -- reflexivity. 
    -- symmetry. apply Ht. reflexivity.
    -- symmetry. apply Hf. reflexivity.
  - discriminate Hn.
Qed.




Declare Scope Kleenean_scope.

Record PreKleenean := mkPreKleenean {
  tbs :> N -> Basic;
  proper : is_monotone tbs
}.


Notation K := PreKleenean.


(* ?? Declare scope Kleenean_scope with key Kleenean *)
Delimit Scope Kleenean_scope with PreKleenean.

(* Automatically open scope Kleenean_scope for arguments of type Kleenean *)
Bind Scope Kleenean_scope with PreKleenean.

Local Open Scope Kleenean_scope.

Definition equiv (k1 k2 : K) : Prop := exists i, forall j, i <= j -> k1 j = k2 j.

Lemma equiv_refl : forall k : K, equiv k k.
Proof. unfold equiv. intro k. exists bot. intros j Hilej. reflexivity. Qed.

Lemma equiv_sym : forall k1 k2 : K, equiv k1 k2 -> equiv k2 k1.
Proof. unfold equiv. intros k1 k2 [i He]. exists i. intros j Hilej. specialize He with j. symmetry. exact (He Hilej). Qed.

Lemma equiv_trans : forall k1 k2 k3 : K, equiv k1 k2 -> equiv k2 k3 -> equiv k1 k3.
Proof. 
  unfold equiv. intros k1 k2 k3 [i12 He12] [i23 He23].
  set (i13 := max i12 i23); exists i13.
  intro j; specialize He12 with j; specialize He23 with j.
  intro Hi13lej. rewrite -> He12. rewrite <- He23. reflexivity.
  - assert (i23 <= i13) as Hi23lei13 by (apply le_max_r). transitivity i13; assumption.
  - assert (i12 <= i13) as Hi12lei13 by (apply le_max_l). transitivity i13; assumption.
Qed.

Add Parametric Relation : K equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as equiv_rel.

#[global]
Instance equiv_relP : RelationClasses.Equivalence equiv.
Proof.
  split.
  - exact equiv_refl.
  - exact equiv_sym.
  - exact equiv_trans.
Qed.

#[global]
Instance equiv_relT : CRelationClasses.Equivalence equiv.
Proof.
  split.
  - exact equiv_refl.
  - exact equiv_sym.
  - exact equiv_trans.
Qed.





Definition apart (k1 k2 : K) := exists i : N, k1 i <> Basic.indt /\ k2 i <> Basic.indt /\ k1 i <> k2 i.
Infix "#" := apart (at level 55, no associativity) : Kleenean_scope.

Lemma apart_irrefl : forall k : K, k # k -> False.
Proof.
  intros k. unfold apart. intros H. destruct H as [i [_ [_ Hn]]]. tauto.
Qed.

Lemma apart_sym : forall k1 k2 : K, k1 # k2 -> k2 # k1.
Proof.
  intros k1 k2. unfold apart. intros [i [H1 [H2 Hne]]]. exists i. 
  split. exact H2. split. exact H1. apply not_eq_sym. exact Hne.
Qed.



Definition definitely (k : K) : Prop := exists i, k i = Basic.tru.
(* Equivalently, forall i, ~ (ki = Basic.fls) *)

Definition possibly (k : K) : Prop := ~ (exists i, k i = Basic.fls).



Lemma cnst_monotone : forall t : Basic, is_monotone (fun _ => t).
Proof. unfold is_monotone. intros t m n Hmn. destruct t. simpl. tauto. destruct b; simpl; tauto. Qed.

Definition constant (t : Basic) := mkPreKleenean (fun _ => t) (cnst_monotone t).

Definition true := constant Basic.tru.
Definition indeterminate := constant Basic.indt.
Definition false := constant Basic.fls.

Lemma true_apart_false : apart true false.
Proof. unfold apart. exists bot. unfold true, false. simpl. split; try split; discriminate. Qed.

Lemma indeterminate_not_apart : forall (k : PreKleenean), ~ (indeterminate # k).
Proof. intro k. unfold apart. intros [i [H _]]. apply H. unfold indeterminate. reflexivity. Qed.


Lemma not_monotone (k : N -> Basic) (Hk : is_monotone k)
  : is_monotone (fun n => Basic.not (k n)).
Proof. 
  apply BasicTopologic.is_monotone_unary_lift. 
  now apply Basic.not_is_monotone_operator. 
  exact Hk.
Qed.

Definition not (k : PreKleenean) : PreKleenean :=
  mkPreKleenean (fun i => Basic.not (k i)) (not_monotone k (proper k)).


Lemma impl_monotone (k1 k2 : N -> Basic) (Hk1 : is_monotone k1) (Hk2 : is_monotone k2)
  : is_monotone (fun n => Basic.impl (k1 n) (k2 n)).
Proof.
  apply BasicTopologic.is_monotone_binary_lift. 
  now apply Basic.impl_is_monotone_operator. 
  exact Hk1. exact Hk2.
Qed.

Definition impl (k1 k2 : PreKleenean) : PreKleenean :=
  mkPreKleenean (fun i => Basic.impl (k1 i) (k2 i)) (impl_monotone k1 k2 (proper k1) (proper k2)).

Lemma not_monotone' (k : N -> Basic) (Hk : is_monotone k)
  : is_monotone (fun n => Basic.not (k n)).
Proof.
  apply ( BasicTopologic.is_monotone_extensional ( fun n : N => Basic.impl (k n) Basic.fls ) ).
  intro n. rewrite -> Basic.not_eq_impl_fls. reflexivity.
  apply impl_monotone.
  exact Hk.
  now apply cnst_monotone.
Qed.


Lemma and_monotone (k1 k2 : N -> Basic) (Hk1 : is_monotone k1) (Hk2 : is_monotone k2)
  : is_monotone (fun n => Basic.and (k1 n) (k2 n)).
Proof.
  apply ( BasicTopologic.is_monotone_extensional ( fun n : N => Basic.not (Basic.impl (k1 n) (Basic.not (k2 n))) ) ).
  intro n. rewrite -> Basic.and_eq_not_impl_not. reflexivity.
  apply not_monotone.
  apply impl_monotone.
  exact Hk1.
  apply not_monotone; exact Hk2.
Qed.

Lemma and_monotone' (k1 k2 : N -> Basic) (Hk1 : is_monotone k1) (Hk2 : is_monotone k2)
  : is_monotone (fun n => Basic.and (k1 n) (k2 n)).
Proof.
  apply BasicTopologic.is_monotone_binary_lift. 
  now apply Basic.and_is_monotone_operator. 
  exact Hk1. exact Hk2.
Qed.

Definition and (k1 k2 : PreKleenean) : PreKleenean :=
  mkPreKleenean (fun i => Basic.and (k1 i) (k2 i)) (and_monotone k1 k2 (proper k1) (proper k2)).


Lemma or_monotone (k1 k2 : N -> Basic) (Hk1 : is_monotone k1) (Hk2 : is_monotone k2)
  : is_monotone (fun n => Basic.or (k1 n) (k2 n)).
Proof.
  apply ( BasicTopologic.is_monotone_extensional ( fun n : N => Basic.not (Basic.and (Basic.not (k1 n)) (Basic.not (k2 n))) ) ).
  intro n. rewrite -> Basic.or_eq_not_and_not. reflexivity.
  apply not_monotone.
  apply and_monotone.
  apply not_monotone; exact Hk1.
  apply not_monotone; exact Hk2.
Qed.

Definition or (k1 k2 : PreKleenean) : PreKleenean :=
  mkPreKleenean (fun i => Basic.or (k1 i) (k2 i)) (or_monotone k1 k2 (proper k1) (proper k2)).


Lemma iff_monotone (k1 k2 : N -> Basic) (Hk1 : is_monotone k1) (Hk2 : is_monotone k2)
  : is_monotone (fun n => Basic.iff (k1 n) (k2 n)).
Proof.
  apply ( BasicTopologic.is_monotone_extensional ( fun n : N => Basic.and (Basic.impl (k1 n) (k2 n)) (Basic.impl (k2 n) (k1 n)) ) ).
  intro n. rewrite -> Basic.iff_eq_impl_and_rimpl. reflexivity.
  apply and_monotone.
  apply impl_monotone. exact Hk1. exact Hk2.
  apply impl_monotone. exact Hk2. exact Hk1.
Qed.

Definition iff (k1 k2 : PreKleenean) : PreKleenean :=
  mkPreKleenean (fun i => Basic.iff (k1 i) (k2 i)) (iff_monotone k1 k2 (proper k1) (proper k2)).

Instance Setoid_PreKleenean : Setoid PreKleenean := { equiv := equiv }.



Definition all_indt_or_exists_tru_or_fls (k : K) : Prop := 
  (forall i, k i = Basic.indt) \/ (exists i, k i = Basic.tru \/ k i = Basic.fls).

Lemma all_ge : forall (p : nat -> Prop) (i : nat),
  (p i) -> (forall j : nat, p j -> p (succ j)) -> (forall j, (i <= j)%nat -> p j).
Proof.
  intros p i pi pIj j Hilej.
  assert (forall k, p (i + k)) as Hpk. { 
    induction k.
    - rewrite -> Nat.add_0_r. exact pi.
    - rewrite -> Nat.add_succ_r. apply pIj. exact IHk.
  }
  set (Hk := Nat.le_exists_sub i j Hilej). destruct Hk as [k [Hk _]].
  rewrite -> Nat.add_comm in Hk. rewrite -> Hk. exact (Hpk k).
Qed.



Lemma all_from_not_indt : forall k : K, forall i, (k i <> Basic.indt -> forall j, i <= j -> k j = k i).
Proof.
  intro k. destruct k as [tbs Htbs].
  unfold is_monotone, BasicTopologic.is_monotone in Htbs. simpl in Htbs.
  unfold BasicTopologic.refines, Basic.refines in Htbs. simpl in Htbs.
  simpl.
  intros m Hm n Hmn.
  specialize Htbs with m n as Htbs'. clear Htbs. pose proof (Htbs' Hmn) as Htbs. clear Htbs'.
  destruct (tbs m), (tbs n).
  - reflexivity.
  - exfalso. apply Hm. reflexivity.
  - contradiction Htbs.
  - destruct b, b0. all: tauto.
Qed.


Lemma impl_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> impl k1 k2 == impl k1' k2'.
Proof.
  intros k1 k1' k2 k2' [i1 Hk1] [i2 Hk2].
  unfold equiv in *.
  set (i := max i1 i2).
  exists i. intros j Hilej.
  specialize Hk1 with j; specialize Hk2 with j.
  unfold impl. simpl.
  rewrite <- Hk1, <- Hk2. reflexivity.
  - transitivity i. now apply le_max_r. exact Hilej.
  - transitivity i. now apply le_max_l. exact Hilej.
Qed.


Lemma not_respectful : forall k k' : K, k == k' -> not k == not k'.
Proof.
  intros k k' [i Hk].
  unfold equiv in *.
  exists i. intros j Hilej. specialize Hk with j.
  unfold not. simpl.
  rewrite <- Hk. reflexivity. exact Hilej.
Qed.

Lemma not_eq_impl_false : forall k : K, not k == impl k false.
Proof.
  intros k. unfold equiv, not, false, impl. simpl.
  exists bot. intros j H0lej. now apply Basic.not_eq_impl_fls. 
Qed.

Lemma not_respectful' : forall k k' : K, k == k' -> not k == not k'.
Proof.
  intros k k' Hk.
  apply (equiv_trans _ (impl k false)).
  exact (not_eq_impl_false k).
  apply (equiv_trans _ (impl k' false)).
  apply impl_respectful.
  exact Hk.
  exact (equiv_refl false).
  apply equiv_sym.
  exact (not_eq_impl_false k').
Qed.
 
Lemma not_respectful'' : Classes.CMorphisms.respectful equiv equiv not not.
Proof.
  intros k k' [i Hk].
  unfold equiv in *.
  exists i. intros j Hilej. specialize Hk with j.
  unfold not. simpl.
  rewrite <- Hk. reflexivity. exact Hilej.
Qed.


Lemma or_eq_impl_not : forall k1 k2 : K, or k1 k2 == impl (not k1) k2.
Proof.
  intros k1 k2. unfold equiv, or, impl, not. simpl.
  exists bot. intros j H0lej. now apply Basic.or_eq_impl_not.
Qed.

Lemma or_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> or k1 k2 == or k1' k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  apply (equiv_trans _ (impl (not k1) k2)).
  exact (or_eq_impl_not k1 k2).
  apply (equiv_trans _ (impl (not k1') k2')).
  apply impl_respectful. apply not_respectful. exact Hk1. exact Hk2.
  apply equiv_sym.
  exact (or_eq_impl_not k1' k2').
Qed.


Lemma and_eq_not_impl_not : forall k1 k2 : K, and k1 k2 == not (impl k1 (not k2)).
Proof.
  intros k1 k2. unfold equiv, and, not, impl, not. simpl.
  exists bot. intros j H0lej. now apply Basic.and_eq_not_impl_not.
Qed.

Lemma and_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> and k1 k2 == and k1' k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  apply (equiv_trans _ (not (impl k1 (not k2)))).
  exact (and_eq_not_impl_not k1 k2).
  apply (equiv_trans _ (not (impl k1' (not k2')))).
  apply not_respectful. apply impl_respectful. exact Hk1. apply not_respectful. exact Hk2.
  apply equiv_sym.
  exact (and_eq_not_impl_not k1' k2').
Qed.


Lemma iff_eq_impl_and_rimpl : forall k1 k2 : K, iff k1 k2 == and (impl k1 k2) (impl k2 k1).
Proof.
  intros k1 k2. unfold equiv, iff, and, impl, impl. simpl.
  exists bot. intros j H0lej. now apply Basic.iff_eq_impl_and_rimpl.
Qed.

Lemma iff_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> iff k1 k2 == iff k1' k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  apply (equiv_trans _ (and (impl k1 k2) (impl k2 k1))).
  exact (iff_eq_impl_and_rimpl k1 k2).
  apply (equiv_trans _ (and (impl k1' k2') (impl k2' k1'))).
  apply and_respectful. 
  apply impl_respectful. exact Hk1. exact Hk2.
  apply impl_respectful. exact Hk2. exact Hk1.
  apply equiv_sym.
  exact (iff_eq_impl_and_rimpl k1' k2').
Qed.



Lemma apart_respectful
  : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> k1 # k2 -> k1' # k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  unfold equiv, apart in *.
  intros Hapart.
  destruct Hapart as [i Hapart].
  destruct Hk1 as [i1 Hk1].
  destruct Hk2 as [i2 Hk2].
  set (i' := max i (max i1 i2)). exists i'.
  assert (i <= i') as Hi by (now apply le_max_l).
  assert (i1 <= i') as Hi1. transitivity (max i1 i2). now apply le_max_l. now apply le_max_r.
  assert (i2 <= i') as Hi2. transitivity (max i1 i2). now apply le_max_r. now apply le_max_r.
  rewrite <- (Hk1 _ Hi1); rewrite <- (Hk2 _ Hi2).
  destruct Hapart as [Hn1i [Hn2i Ha]].
  split; (try split).
  - rewrite -> (all_from_not_indt k1 i Hn1i i' Hi). exact Hn1i.
  - rewrite -> (all_from_not_indt k2 i Hn2i i' Hi). exact Hn2i.
  - rewrite -> (all_from_not_indt k1 i Hn1i i' Hi).
    rewrite -> (all_from_not_indt k2 i Hn2i i' Hi). 
    exact Ha.
Qed.

Notation Proper := CMorphisms.Proper.
Notation respectful := CMorphisms.respectful.


#[global]
Instance not_Respectful : Proper (respectful equiv equiv) not.
Proof. intros k k' Hk. now apply not_respectful. Qed.

#[global]
Instance impl_Respectful : Proper (respectful equiv (respectful equiv equiv)) impl.
Proof. intros k1 k1' Hk1 k2 k2' Hk2. now apply impl_respectful. Qed.

#[global]
Instance and_Respectful : Proper (respectful equiv (respectful equiv equiv)) and.
Proof. intros k1 k1' Hk1 k2 k2' Hk2. now apply and_respectful. Qed.

#[global]
Instance or_Respectful : Proper (respectful equiv (respectful equiv equiv)) or.
Proof. intros k1 k1' Hk1 k2 k2' Hk2. now apply or_respectful. Qed.

#[global]
Instance iff_Respectful : Proper (respectful equiv (respectful equiv equiv)) iff.
Proof. intros k1 k1' Hk1 k2 k2' Hk2. now apply iff_respectful. Qed.

#[global]
Instance apart_Respectful : Proper (respectful equiv (respectful equiv CRelationClasses.iffT)) apart.
Proof.
  intros k1 k1' Hk1 k2 k2' Hk2. split. now apply apart_respectful. apply apart_respectful; now apply equiv_sym.
Qed.

End PreKleeneSection.


Definition Kleenean := @PreKleenean nat nat_Lattice.
Notation K := Kleenean.

Instance KleeneanSetoid : Setoid Kleenean := { equiv := equiv }.


Lemma defined_dec : forall k : Kleenean,
  (k == true \/ k == false) -> ({k == true} + {k == false}).
Proof.
  intros k H.
  assert (exists i, k i = Basic.tru \/ k i = Basic.fls) as Hi. {
    destruct H as [[i H]|[i H]]; specialize H with i; exists i.
    - left; exact (H (Nat.le_refl i)).
    - right; exact (H (Nat.le_refl i)).
  }
  assert ({ i | k i = Basic.tru \/ k i = Basic.fls}) as Hsi. {
    apply constructive_indefinite_ground_description_nat.
    - intros i. destruct (k i); try (destruct b).
      -- right. intro Hf. destruct Hf. discriminate. discriminate.
      -- left. left. reflexivity.
      -- left. right. reflexivity.
    - exact Hi.
  }
  destruct Hsi as [i Hsi].
  assert ({k i = Basic.tru} + {k i = Basic.fls}) as Hssi. {
    destruct (k i); try (destruct b).
    - exfalso. destruct Hsi; discriminate.
    - left; reflexivity.
    - right; reflexivity.
  }
  destruct Hssi as [Ht|Hf].
  - left. unfold equiv. exists i. unfold true. simpl. rewrite <- Ht.
    apply (all_from_not_indt k).
    now rewrite -> Ht.
  - right. unfold equiv, false. simpl. exists i. rewrite <- Hf. 
    apply (all_from_not_indt k).
    now rewrite -> Hf.
Qed.


Lemma impl_up : forall (k1 k2 : Kleenean), (impl k1 k2 == true) <-> (k1 == false \/ k2 == true).
Proof.
  intros k1 k2. unfold equiv, impl, true, false. simpl.
  split.
  - intro Himpl.
    destruct Himpl as [i Himpl].
    assert (Basic.impl (k1 i) (k2 i) = Basic.tru) as Handi by exact (Himpl i (Nat.le_refl i)).
    assert (k1 i = Basic.fls \/ k2 i = Basic.tru) as Habi by exact (Basic.impl_tru _ _ Handi).
    destruct Habi as [Hai|Hbi].
    -- left. exists i. rewrite <- Hai. apply (all_from_not_indt k1). rewrite -> Hai. discriminate.
    -- right. exists i. rewrite <- Hbi. apply (all_from_not_indt k2). rewrite -> Hbi. discriminate.
  - intro Hor.
    unfold equiv; simpl.
    destruct Hor as [[i Hai] | [i Hbi]].
    -- exists i. intros j Hilej. rewrite -> (Hai j Hilej). now unfold Basic.impl.
    -- exists i. intros j Hilej. rewrite -> (Hbi j Hilej). unfold Basic.impl. 
       destruct (k1 j). reflexivity. destruct b; reflexivity.
Qed.

Lemma impl_down : forall (k1 k2 : Kleenean), (impl k1 k2 == false) <-> (k1 == true /\ k2 == false).
Proof.
  intros k1 k2. unfold equiv, impl, true, false. simpl.
  split.
  - intro Hand.
    unfold equiv in *; simpl.
    destruct Hand as [i Hand]. 
    split.
    exists i. intros j Hilej. specialize Hand with j. apply Hand in Hilej as Handj.
    apply Basic.impl_fls in Handj. exact (proj1 Handj).
    exists i. intros j Hilej. specialize Hand with j. apply Hand in Hilej as Handj.
    apply Basic.impl_fls in Handj. exact (proj2 Handj).
  - intros [[ia Ha] [ib Hb]]. set (iab := max ia ib). exists iab.
    intros j Hj. simpl. rewrite -> (Ha j), -> (Hb j). unfold Basic.and. reflexivity.
    apply (Nat.le_trans _ iab). apply (Nat.le_max_r ia ib). exact Hj.
    apply (Nat.le_trans _ iab). apply (Nat.le_max_l ia ib). exact Hj.
Qed.







Module Abstract.

Class AbstractKleenean (K : Set) :=
  {
    true : K;
    false : K;

    equiv : K -> K -> Prop;
    apart : K -> K -> Prop;

    not : K -> K;
    impl : K -> K -> K;
    or : K -> K -> K;
    and : K -> K -> K;
 
    impl_respectful : forall k1 k1' k2 k2', equiv k1 k1' -> equiv k2 k2' -> equiv (impl k1 k2) (impl k1' k2');
    impl_up : forall k1 k2, (equiv (impl k1 k2) true) <-> (equiv k1 false) \/ (equiv k2 true);
    impl_down : forall k1 k2, (equiv (impl k1 k2) false) <-> (equiv k1 true) /\ (equiv k2 false);

    distinct : apart false true;
    defined_dec : forall k,
        (equiv k true \/ equiv k false) -> ({equiv k true} + {equiv k false});

  }.

End Abstract.

Import Abstract.

#[export]
Instance instance : AbstractKleenean Kleenean := 
{
  true := Kleenean.true;  
  false := Kleenean.false;

  equiv := Kleenean.equiv;
  apart := Kleenean.apart;

  not := Kleenean.not;
  impl := Kleenean.impl;
  or:= Kleenean.or;
  and := Kleenean.and;

  distinct := Kleenean.apart_sym _ _ Kleenean.true_apart_false;
  defined_dec := Kleenean.defined_dec;

  impl_respectful := Kleenean.impl_respectful;
  impl_up := Kleenean.impl_up;
  impl_down := Kleenean.impl_down;
}.





Definition ClassicalKleenean := Basic.

(* The Limited Principle of Omniscence *)
Definition LPO := forall p : nat -> Prop, (forall n : nat, {p n} + {~ p n}) ->
  { exists n : nat, p n } + { forall n : nat, ~ p n }.

Lemma eqv_true_or_indeterminate_or_false_dec : 
  LPO -> forall k : Kleenean, { k == true } + { k == indeterminate } + { k == false } .
Proof.
  intros lpo k.
  set (p := fun n => k n <> Basic.indt).
  assert (forall n, {p n} + {~ p n}) as Hpdec by (intro n; now apply Basic.not_eq_dec).
  set (H := lpo p Hpdec).
  unfold p in H.
  destruct H as [Hni|Hi].
  - apply (constructive_indefinite_ground_description_nat) in Hni.
    2: exact Hpdec.
    destruct Hni as [i Hni].
    remember (k i) as ki. 
    rewrite -> Heqki in Hni.
    pose proof (all_from_not_indt k i Hni) as Hj.
    destruct ki; try (destruct b).
    -- clear Hj. rewrite <- Heqki in Hni. contradiction.
    -- left; left. unfold equiv. exists i. rewrite <- Heqki in Hj. exact Hj. 
    -- right. unfold equiv. exists i. rewrite <- Heqki in Hj. exact Hj. 
  - left; right. unfold equiv. exists 0. intros j H0lej. 
    specialize Hi with j. apply Basic.eq_dne in Hi. exact Hi.
Qed.

Definition to_classical (lpo : LPO) (k : Kleenean) : ClassicalKleenean :=
  let Hk := eqv_true_or_indeterminate_or_false_dec lpo k in
    match Hk with
    | inleft Hti =>
         match Hti with
         | left Ht => Basic.tru
         | right Hf => Basic.indt
         end
    | inright Hf => Basic.fls
    end
.


Lemma constant_eqv {N : Set} {Lattice_N : Lattice N} : 
  forall {c1 c2 : Basic}, constant c1 == constant c2 -> c1 = c2.
Proof. intros c1 c2 H. unfold equiv in H. destruct H as [i H]. apply (H i). reflexivity. Qed.

Lemma compare_with_constants {N : Set} {Lattice_N : Lattice N} : 
  forall {k : PreKleenean} {c1 c2 : Basic}, 
    k == constant c1 -> k == constant c2 -> c1 = c2.
Proof. 
  intros k c1 c2 H1 H2.
  apply equiv_sym in H1.
  pose proof (equiv_trans _ k _ H1 H2) as H.
  now apply constant_eqv.
Qed.


Theorem to_classical_bijection (lpo : LPO) : forall (k : Kleenean) (t : ClassicalKleenean), 
  k == constant t <-> to_classical lpo k = t.
Proof.
  intros k. unfold to_classical. split.
  - intro H. 
    set (Hk := eqv_true_or_indeterminate_or_false_dec lpo k).
    set (pk := k : PreKleenean).
    destruct Hk as [[H'|H']|H'].
    all: now apply (compare_with_constants H' H).
  - intro H.
    remember (eqv_true_or_indeterminate_or_false_dec lpo k) as Hk.
    destruct Hk as [[H'|H']|H']. all: rewrite <- H; exact H'.
Qed.
