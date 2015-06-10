Require Import Arith List.

Inductive environment A :=
| Empty : environment A
| Extend : nat -> A -> environment A -> environment A.

Fixpoint lookup {A : Type} x env : option A :=
  match env with
    | Empty =>
      None
    | Extend x' a env' =>
      if beq_nat x x'
      then Some a
      else lookup x env'
  end.

Definition env_equiv {A : Type} env  env' :=
  forall x,
    @lookup A x env = lookup x env'.

Require Import Setoid.

Instance tc_env_equiv {A : Type} : Equivalence (@env_equiv A).
Proof.
  unfold env_equiv.
  split.
  unfold Reflexive; intros.
  reflexivity.
  unfold Symmetric; intros.
  rewrite H.
  reflexivity.
  unfold Transitive; intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma env_equiv_extend_eq {A : Type} :
  forall x v env env',
    env_equiv env env' ->
    env_equiv (Extend A x v env) (Extend A x v env').
Proof.
  unfold env_equiv.
  intros.
  simpl.
  destruct (beq_nat x0 x).
  reflexivity.
  apply H.
Qed.

Lemma lookup_empty {A : Type} :
  forall x,
    lookup x (Empty A) = None.
Proof.
  reflexivity.
Qed.

Lemma lookup_extend_eq {A : Type} :
  forall x v env,
    lookup x (Extend A x v env) = Some v.
Proof.
  intros.
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma lookup_extend_neq {A : Type} :
  forall x x' v' env,
    beq_nat x x' = false ->
    lookup x (Extend A x' v' env) = lookup x env.
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma env_shadow :
  forall A x v v' env,
    env_equiv (Extend A x v (Extend A x v' env)) (Extend A x v env).
Proof.
  intros.
  unfold env_equiv.
  intros x'.
  simpl.
  remember (beq_nat x' x) as b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Lemma env_permute :
  forall A x x' v v' env,
    beq_nat x x' = false ->
    env_equiv (Extend A x v (Extend A x' v' env)) (Extend A x' v' (Extend A x v env)).
Proof.
  intros.
  unfold env_equiv.
  intros y.
  simpl.
  remember (beq_nat y x) as eqyx.
  destruct eqyx.
  symmetry in Heqeqyx.
  apply beq_nat_true in Heqeqyx.
  rewrite Heqeqyx.
  rewrite H.
  reflexivity.
  reflexivity.
Qed.

Fixpoint drop {A : Type} x env : environment A :=
  match env with
    | Empty =>
      Empty _
    | Extend x' a env' =>
      if beq_nat x x'
      then drop x env'
      else Extend _ x' a (drop x env')
  end.

Definition distinct {A : Type} (env : environment A) :=
  forall x v,
    lookup x env = Some v ->
    exists env',
      env_equiv (Extend A x v env') env /\
      lookup x env' = None.
