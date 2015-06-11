Require Import Arith List.
Require Import "Lattice".
Require Import "Environment".

Inductive type : Type :=
| Bool : label -> type
| Arrow : type -> type -> label -> type.

Inductive expr : Type :=
| TT  : label -> expr
| FF  : label -> expr
| Cond : expr -> expr -> expr -> expr
| Var :  nat -> expr
| Abs :  nat -> type -> expr -> label -> expr
| App : expr -> expr -> expr.

Inductive value : expr -> Prop :=
| value_true :
    forall l,
      value (TT l)
| value_false :
    forall l,
      value (FF l)
| value_abs :
    forall x t e l,
      value (Abs x t e l).

Definition value_with_label v l :=
  value v /\
  (v = (TT l) \/ v = (FF l) \/ (exists x t e, v = Abs x t e l)).

Definition stamp expr label :=
  match expr with
    | TT l => TT (join l label)
    | FF l => FF (join l label)
    | Abs x t e l => Abs x t e (join l label)
    | _ => expr
  end.

Lemma stamp_preserves_value :
  forall e l,
    value (stamp e l) <->
    value e.
Proof.
  intros e l.
  split; intro H.
  destruct e; intros; try inversion H.
  apply value_true.
  apply value_false.
  apply value_abs.

  destruct e; intros; try inversion H; subst; simpl.
  apply value_true.
  apply value_false.
  apply value_abs.
Qed.

Lemma stamp_value_is_join :
  forall v l l',
    value_with_label v l ->
    value_with_label (stamp v l') (join l l').
Proof.
  intros v l l' Hv; unfold value_with_label.
  destruct Hv.
  destruct H0.
  subst.
  simpl.
  split.
  apply value_true.
  left.
  reflexivity.
  destruct H0.
  subst.
  split.
  apply value_false.
  right.
  left.
  reflexivity.
  destruct H0.
  destruct H0.
  destruct H0.
  subst.
  split.
  simpl.
  apply value_abs.
  right.
  right.
  exists x.
  exists x0.
  exists x1.
  reflexivity.
Qed.

Lemma stamp_high_is_high :
  forall v l,
    value_with_label v l ->
    value_with_label (stamp v High) High.
Proof.
  intros.
  apply (stamp_value_is_join v l High) in H.
  rewrite join_high_r in H.
  apply H.
Qed.

Lemma stamp_low_is_neutral :
  forall v l,
    value_with_label v l ->
    value_with_label (stamp v Low) l.
Proof.
  intros.
  apply (stamp_value_is_join v l Low) in H.
  rewrite join_low_r in H.
  apply H.
Qed.

Fixpoint sub (v : expr) (x : nat) (e : expr) :=
  match e with
    | TT l =>
      TT l
    | FF l =>
      FF l
    | Cond e1 e2 e3 =>
      Cond (sub v x e1) (sub v x e2) (sub v x e3)
    | Var y =>
      if beq_nat x y then v else e
    | Abs y t f l  =>
      if beq_nat x y then e else Abs y t (sub v x f) l
    | App e1 e2 =>
      App (sub v x e1) (sub v x e2)
  end.

Inductive big_step : expr -> expr -> Prop :=
| big_step_val :
    forall v,
      value v ->
      big_step v v
| big_step_cond_true :
    forall e1 l e2 e3 v,
      big_step e1 (TT l) ->
      big_step e2 v ->
      big_step (Cond e1 e2 e3) (stamp v l)
| big_step_cond_false :
    forall e1 l e2 e3 v,
      big_step e1 (FF l) ->
      big_step e2 v ->
      big_step (Cond e1 e2 e3) (stamp v l)
| big_step_app :
    forall e1 x s e l e2 v v',
      big_step e1 (Abs x s e l) ->
      big_step e2 v ->
      big_step (sub v x e) v' ->
      big_step (App e1 e2) (stamp v' l).

Lemma big_step_deterministic :
  forall e v v',
    big_step e v ->
    big_step e v' ->
    v = v'.
Proof.
  intros e v v' Hstep.
  revert v'.
  induction Hstep; intros v'' Hstep'; inversion Hstep'; subst.
  reflexivity.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  specialize (IHHstep1 _ H3).
  inversion IHHstep1; subst.
  specialize (IHHstep2 _ H4); subst.
  reflexivity.
  specialize (IHHstep1 _ H3).
  inversion IHHstep1.
  inversion H.
  specialize (IHHstep1 _ H3).
  inversion IHHstep1.
  specialize (IHHstep1 _ H3).
  inversion IHHstep1; subst.
  specialize (IHHstep2 _ H4); subst.
  reflexivity.
  inversion H.
  specialize (IHHstep1 _ H1).
  inversion IHHstep1; subst; clear IHHstep1.
  specialize (IHHstep2 _ H2); subst.
  specialize (IHHstep3 _ H4); subst; auto.
Qed.

Lemma big_steps_to_value :
  forall e v,
    big_step e v ->
    value v.
Proof.
  intros e v Hstep.
  induction Hstep; subst; auto.
  apply stamp_preserves_value with (l := l); auto.
  apply stamp_preserves_value; auto.
  apply stamp_preserves_value; auto.
Qed.

Inductive subtype : type -> type -> Prop :=
| TFunSub :
    forall s1' s1 s2 s2' l l',
      subtype s1' s1 ->
      subtype s2 s2' ->
      flows_to l l' ->
      subtype (Arrow s1 s2 l) (Arrow s1' s2' l')
| TBoolSub :
    forall l l',
      flows_to l l' ->
      subtype (Bool l) (Bool l').

Lemma subtype_refl :
  forall t,
    subtype t t.
Proof.
  induction t.
  apply TBoolSub.
  apply flows_to_refl.

  apply TFunSub.
  apply IHt1.
  apply IHt2.
  apply flows_to_refl.
Qed.

Lemma subtype_antisym :
  forall t t',
    subtype t t' ->
    subtype t' t ->
    t = t'.
Proof.
  intros t t' Hsub.
  induction Hsub; intros.
  inversion H0.
  subst.
  rewrite IHHsub1; auto.
  rewrite IHHsub2; auto.
  rewrite (flows_to_antisym l l'); auto.

  inversion H0.
  subst.
  rewrite (flows_to_antisym l l'); auto.
Qed.

Lemma subtype_bool_left :
  forall l s,
    subtype (Bool l) s ->
    exists l',
      s = (Bool l') /\ flows_to l l'.
Proof.
  destruct s.
  intros.
  exists l0.
  inversion H; subst.
  split.
  reflexivity.
  apply H2.
  intros.
  inversion H.
Qed.

Lemma subtype_bool_right :
  forall l s,
    subtype s (Bool l) ->
    exists l',
      s = (Bool l') /\ flows_to l' l.
Proof.
  destruct s.
  intros.
  exists l0.
  inversion H; subst.
  split.
  reflexivity.
  apply H2.
  intros.
  inversion H.
Qed.

Lemma subtype_arrow_left :
  forall l s1 s2 s,
    subtype (Arrow s1 s2 l) s ->
    exists s1' s2' l',
      s = (Arrow s1' s2' l') /\ flows_to l l' /\ subtype s1' s1 /\ subtype s2 s2'.
Proof.
  destruct s.
  intros.
  inversion H.
  intros.
  exists s3. exists s4. exists l0.
  inversion H; subst.
  split.
  reflexivity.
  split.
  assumption.
  split; assumption.
Qed.

Lemma subtype_arrow_right :
  forall l s1 s2 s,
    subtype s (Arrow s1 s2 l) ->
    exists s1' s2' l',
      s = (Arrow s1' s2' l') /\ flows_to l' l /\ subtype s1 s1' /\ subtype s2' s2.
Proof.
  destruct s.
  intros.
  inversion H.
  intros.
  exists s3. exists s4. exists l0.
  inversion H; subst.
  split.
  reflexivity.
  split.
  assumption.
  split; assumption.
Qed.

Lemma subtype_trans :
  forall t t' t'',
    subtype t t' ->
    subtype t' t'' ->
    subtype t t''.
Proof.
  intros t t'.
  revert t.
  induction t' as [l'| s1' IHs1' s2' IHs2' l'].

  intros t t'' H H0.
  apply subtype_bool_left in H0.
  destruct H0 as [l'' [H0 H0']].
  subst.
  apply subtype_bool_right in H.
  destruct H as [l [H H']].
  subst.
  apply TBoolSub.
  apply flows_to_trans with (l' := l'); assumption.

  intros t t'' H0 H.
  apply subtype_arrow_left in H.
  destruct H as [s1''  [s2'' [l'' [H5 [H6 [H7 H8]]]]]].
  subst.
  apply subtype_arrow_right in H0.
  destruct H0 as [s1  [s2 [l [H5 [H9 [H10 H11]]]]]].
  subst.
  apply TFunSub.
  apply IHs1'; assumption.
  apply IHs2'; assumption.
  apply flows_to_trans with (l' := l'); assumption.
Qed.

Definition stamp_type t l :=
  match t with
    | Bool l' => Bool (join l' l)
    | Arrow t1 t2 l' => Arrow t1 t2 (join l' l)
  end.

Definition type_with_label t l :=
  match t with
    | Bool l' => l = l'
    | Arrow _ _ l' => l = l'
  end.

Lemma all_types_have_label :
  forall t, exists l,
    type_with_label t l.
Proof.
  destruct t.
  exists l; auto.
  reflexivity.
  exists l.
  reflexivity.
Qed.

Lemma stamp_type_is_join :
  forall t l l',
    type_with_label t l ->
    type_with_label (stamp_type t l') (join l l').
Proof.
  intros.
  destruct t.
  simpl.
  simpl in H.
  subst.
  reflexivity.

  simpl.
  simpl in H.
  subst.
  reflexivity.
Qed.

Lemma stamp_preserves_subtype :
  forall s l s',
    subtype (stamp_type s l) s' ->
    subtype s s'.
Proof.
  induction s; intros.
  simpl in H.
  apply subtype_bool_left in H.
  destruct H.
  destruct H.
  subst.
  apply TBoolSub.
  apply flows_to_trans with (l' := (join l l0)).
  apply join_is_upper_bound.
  apply H0.

  simpl in H.
  apply subtype_arrow_left in H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H1.
  subst.
  apply TFunSub.
  apply H1.
  apply H2.
  apply flows_to_trans with (l' := (join l l0)).
  apply join_is_upper_bound.
  apply H0.
Qed.

Lemma stamp_l_preserves_subtype :
  forall s l s',
    subtype s s' ->
    subtype (stamp_type s l) (stamp_type s' l).
Proof.
  induction s; intros.
  apply subtype_bool_left in H.
  destruct H.
  destruct H.
  subst.
  simpl.
  apply TBoolSub.
  destruct (join_is_upper_bound x l0).
  apply join_is_least_upper_bound; auto.
  apply flows_to_trans with (l' := x); auto.

  apply subtype_arrow_left in H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H1.
  subst.
  apply TFunSub; auto.
  destruct (join_is_upper_bound x1 l0); auto.
  apply join_is_least_upper_bound; auto.
  apply flows_to_trans with (l' := x1); auto.
Qed.

Inductive typing : environment type -> expr -> type -> Prop :=
| typing_true :
    forall c l l',
      flows_to l l' ->
      typing c (TT l) (Bool l')
| typing_false :
    forall c l l',
      flows_to l l' ->
      typing c (FF l) (Bool l')
| typing_cond :
    forall c s s' e1 e2 e3 l,
      typing c e1 (Bool l) ->
      typing c e2 s ->
      typing c e3 s ->
      subtype (stamp_type s l) s' ->
      typing c (Cond e1 e2 e3) s'
| typing_app :
    forall c e1 e2 s2 s2' s s' l,
      typing c e1 (Arrow s2 s l) ->
      typing c e2 s2' ->
      subtype s2' s2 ->
      subtype (stamp_type s l) s' ->
      typing c (App e1 e2) s'
| typing_abs :
    forall c x e s1' s1 s2 s2' l l',
      typing (Extend type x s1 c) e s2 ->
      subtype s1' s1 ->
      subtype s2 s2' ->
      flows_to l l' ->
      typing c (Abs x s1 e l) (Arrow s1' s2' l')
| typing_var :
    forall x c s s',
      lookup x c = Some s ->
      subtype s s' ->
      typing c (Var x) s'.

Lemma typing_inversion_true :
  forall c l s,
    typing c (TT l) s ->
    exists l',
      s = (Bool l') /\ flows_to l l'.
Proof.
  intros.
  inversion H; subst.
  exists l'; auto.
Qed.

Lemma typing_inversion_false :
  forall c l s,
    typing c (FF l) s ->
    exists l',
      s = (Bool l') /\ flows_to l l'.
Proof.
  intros.
  inversion H; subst.
  exists l'; auto.
Qed.

Lemma typing_inversion_cond :
  forall c e1 e2 e3 s l,
    typing c (Cond e1 e2 e3) s ->
    type_with_label s l ->
    exists l' s',
      typing c e1 (Bool l') /\
      typing c e2 s' /\
      typing c e3 s' /\
      subtype (stamp_type s' l') s.
Proof.
  intros.
  inversion H; subst.
  exists l0.
  exists s0.
  split; auto.
Qed.

Lemma typing_inversion_var :
  forall c x s,
    typing c (Var x) s ->
    exists s',
      lookup x c = Some s' /\ subtype s' s.
Proof.
  intros.
  inversion H; subst.
  exists s0.
  split; auto.
Qed.

Lemma typing_inversion_app :
  forall c e1 e2 s l,
    typing c (App e1 e2) s ->
    type_with_label s l ->
    exists l' s1 s1' s2,
      typing c e1 (Arrow s1 s2 l') /\
      typing c e2 s1' /\
      subtype s1' s1 /\
      subtype (stamp_type s2 l') s.
Proof.
  intros.
  inversion H; subst.
  exists l0.
  exists s2.
  exists s2'.
  exists s0.
  split; auto.
Qed.

Lemma typing_inversion_abs :
  forall c x s1' e l' u,
    typing c (Abs x s1' e l') u ->
    exists s1 s2 s2' l,
      u = (Arrow s1 s2 l) /\
      typing (Extend _ x s1' c) e s2' /\
      subtype s1 s1' /\
      subtype s2' s2 /\
      flows_to l' l.
Proof.
  intros.
  inversion H; subst.
  exists s1'0.
  exists s2'.
  exists s2.
  exists l'0; auto.
Qed.

Lemma typing_is_context_invariant :
  forall c c' e s,
    env_equiv c c' ->
    typing c e s ->
    typing c' e s.
Proof.
  intros c c' e s Hequiv Htype.
  revert c' Hequiv.
  induction Htype; intros c' Hequiv.

  apply typing_true; auto.

  apply typing_false; auto.

  apply typing_cond with (s := s)(l := l); auto.

  apply typing_app with (s2 := s2)(s := s)(l := l)(s2' := s2'); auto.

  apply typing_abs with (s2 := s2); auto.
  apply IHHtype.
  apply env_equiv_extend_eq.
  apply Hequiv.

  apply typing_var with (s := s); auto.
  rewrite <- H.
  symmetry.
  apply Hequiv.
Qed.

Inductive free_in : nat -> expr -> Prop :=
| free_in_cond :
    forall x e1 e2 e3,
      (free_in x e1 \/ free_in x e2 \/ free_in x e3) ->
      free_in x (Cond e1 e2 e3)
| free_in_app :
    forall x e1 e2,
      (free_in x e1 \/ free_in x e2) ->
      free_in x (App e1 e2)
| free_in_var :
    forall x,
      free_in x (Var x)
| free_in_abs :
    forall x y s e l,
      x <> y ->
      free_in x e ->
      free_in x (Abs y s e l).

Lemma free_in_dec :
  forall x e,
    { free_in x e} + { ~ free_in x e }.
Proof.
  unfold not.
  induction e.

  right.
  intros.
  inversion H.

  right.
  intros.
  inversion H.

  destruct IHe1.
  left.
  apply free_in_cond.
  left.
  assumption.
  destruct IHe2.
  left.
  apply free_in_cond.
  right.
  left.
  assumption.
  destruct IHe3.
  left.
  apply free_in_cond.
  right.
  right.
  apply f1.
  right.
  intros.
  inversion H; subst.
  destruct H2.
  auto.
  destruct H0; auto.

  case_eq (beq_nat x n).
  intros.
  apply beq_nat_true in H.
  subst.
  left.
  apply free_in_var.
  right.
  intros.
  inversion H0.
  subst.
  rewrite <- beq_nat_refl in H.
  inversion H.

  destruct IHe.
  case_eq (beq_nat x n); intros.
  apply beq_nat_true in H.
  subst.
  right.
  intros.
  inversion H.
  auto.
  left.
  apply beq_nat_false in H.
  apply free_in_abs; assumption.
  right.
  intros.
  inversion H; auto.

  destruct IHe1.
  left.
  apply free_in_app; auto.
  destruct IHe2.
  left.
  apply free_in_app; auto.
  right.
  intros.
  inversion H.
  destruct H2; auto.
Qed.

Definition closed e :=
  forall x, ~ free_in x e.

Definition ctxt_approx c c' :=
  forall x t,
    (lookup x c = Some t ->
     exists t',
      lookup x c' = Some t' /\ subtype t t').

Definition ctxt_equiv c c' :=
  ctxt_approx c c' /\ ctxt_approx c' c.

Lemma ctxt_equiv_sound :
  forall e c c',
    ctxt_equiv c c' ->
    (forall x, free_in x e ->
       lookup x c = lookup x c').
Proof.
  unfold ctxt_equiv.
  unfold ctxt_approx.
  intros.
  destruct H.
  case_eq (lookup x c); intros.
  case_eq (lookup x c'); intros.
  specialize (H x t H2).
  specialize (H1 x t0 H3).
  destruct H.
  destruct H.
  destruct H1.
  destruct H1.
  rewrite H1 in H2.
  inversion H2.
  subst.
  clear H2.
  rewrite H in H3.
  inversion H3.
  subst.
  clear H3.
  assert (t = t0).
  apply subtype_antisym; auto.
  subst.
  reflexivity.

  specialize (H x t H2).
  destruct H.
  destruct H.
  rewrite H in H3.
  inversion H3.

  case_eq (lookup x c'); intros.
  specialize (H1 x t H3).
  destruct H1.
  destruct H1.
  rewrite H2 in H1.
  inversion H1.

  reflexivity.
Qed.

Lemma env_approx :
  forall e c c' s s' l l',
    typing c e s ->
    type_with_label s l ->
    ctxt_approx c c' ->
    typing c' e s' ->
    type_with_label s' l' ->
    subtype s (stamp_type s' l).
Proof.
  intros e c c' s s' l l' Htyp Hlab Happx Htyp'.
  generalize dependent c.
  generalize dependent s.
  revert l.
  revert l'.
  induction Htyp'; intros l'' l''' s'' Htwl c' Htype Happx Htwl'.

  simpl in Htwl.
  apply typing_inversion_true in Htype.
  destruct Htype.
  destruct H0.
  subst.
  simpl in Htwl.
  subst.
  apply TBoolSub.
  apply join_is_upper_bound.

  simpl in Htwl.
  apply typing_inversion_false in Htype.
  destruct Htype.
  destruct H0.
  subst.
  simpl in Htwl.
  subst.
  apply TBoolSub.
  apply join_is_upper_bound.

  apply typing_inversion_cond with (l := l) in Htype.
  destruct Htype as [l' H0].
  destruct H0 as [t H0].
  destruct H0.
  destruct H1.
  destruct H2.
Abort.

Lemma env_invariance :
  forall e c c' s,
    typing c e s ->
    (forall x, free_in x e -> lookup x c = lookup x c') ->
    typing c' e s.
Proof.
  intros e c c' s Htype.
  revert c'.
  induction Htype; intros.

  apply typing_true.
  assumption.

  apply typing_false.
  assumption.

  apply typing_cond with (s := s)(l := l); auto.
  apply (IHHtype1 c'); auto.
  intros.
  apply H0.
  apply free_in_cond; auto.
  apply (IHHtype2 c'); auto; intros.
  apply H0.
  apply free_in_cond; auto.
  apply (IHHtype3 c'); auto.
  intros.
  apply H0.
  apply free_in_cond; auto.

  apply typing_app with (s2 := s2)(s := s)(l := l)(s2' := s2'); auto.
  apply IHHtype1; intros.
  apply H1.
  apply free_in_app; auto.
  apply IHHtype2; intros.
  apply H1.
  apply free_in_app; auto.

  apply typing_abs with (s2 := s2); auto.
  apply IHHtype.
  intros.
  simpl.
  case_eq (beq_nat x0 x); intro Heq.
  reflexivity.
  apply H2.
  apply free_in_abs.
  apply beq_nat_false in Heq.
  assumption.
  apply H3.

  apply typing_var with (s := s); auto.
  rewrite <- H.
  symmetry.
  apply H1.
  apply free_in_var.
Qed.

Lemma free_in_env :
  forall x e c s,
    typing c e s ->
    free_in x e ->
    exists s', lookup x c = Some s'.
Proof.
  intros x e c s Htype.
  revert x.
  induction Htype; intros x' Hfree.
  inversion Hfree.
  inversion Hfree.
  inversion Hfree.
  destruct H2.
  apply IHHtype1.
  assumption.
  destruct H2.
  apply IHHtype2.
  assumption.
  apply IHHtype3.
  assumption.

  inversion Hfree.
  destruct H3.
  apply IHHtype1.
  assumption.
  apply IHHtype2.
  assumption.

  inversion Hfree; subst.
  specialize (IHHtype x' H8).
  destruct IHHtype.
  apply beq_nat_false_iff in H5.
  simpl in H2.
  rewrite H5 in H2.
  exists x0.
  assumption.

  inversion Hfree; subst.
  exists s.
  assumption.
Qed.

Lemma typeable_closed :
  forall e s,
    typing (Empty _) e s ->
    closed e.
Proof.
  intros.
  unfold closed.
  intros.
  unfold not.
  intros.
  apply free_in_env with (x := x) in H.
  destruct H.
  inversion H.
  assumption.
Qed.

Lemma subsumption :
  forall c e s s',
    typing c e s ->
    subtype s s' ->
    typing c e s'.
Proof.
  intros c e s s' Htyp.
  revert s'.
  induction Htyp.

  intros s' Htyp.
  apply subtype_bool_left in Htyp.
  destruct Htyp.
  destruct H0.
  subst.
  apply typing_true.
  apply flows_to_trans with (l' := l'); assumption.

  intros s' Htyp.
  apply subtype_bool_left in Htyp.
  destruct Htyp.
  destruct H0.
  subst.
  apply typing_false.
  apply flows_to_trans with (l' := l'); assumption.

  intros s'' Hsub.
  apply typing_cond with (s := s)(l := l).
  apply Htyp1.
  apply Htyp2.
  apply Htyp3.
  apply subtype_trans with (t' := s').
  apply H.
  apply Hsub.

  intros s'' Hsub.
  apply typing_app with (s2 := s2)(s := s) (l := l)(s2' := s2'); auto.
  apply subtype_trans with (t' := s'); auto.

  intros s' Hsub.
  apply subtype_arrow_left in Hsub.
  destruct Hsub.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H4.
  subst.
  apply typing_abs with (s2 := s2).
  apply Htyp.
  apply subtype_trans with (t' := s1'); assumption.
  apply subtype_trans with (t' := s2'); assumption.
  apply flows_to_trans with (l' := l'); assumption.

  intros s'' Hsub.
  apply typing_var with (s := s).
  assumption.
  apply subtype_trans with (t' := s'); assumption.
Qed.

Lemma stamp_idemp :
  forall s l,
    type_with_label s l ->
    s = (stamp_type s l).
Proof.
  destruct s; intros; simpl in H; subst; simpl; rewrite <- join_idempotent;  reflexivity.
Qed.

Lemma canonical_form_bool :
  forall c v l,
    value v ->
    typing c v (Bool l) ->
    exists l',
      (v = (TT l') \/ v = (FF l')) /\ flows_to l' l.
Proof.
  intros c e l' Hval.
  inversion Hval; subst.

  intros Htype.
  inversion Htype; subst.
  exists l.
  split.
  left.
  reflexivity.
  apply H2.

  intros Htype.
  inversion Htype; subst.
  exists l.
  split.
  right.
  reflexivity.
  apply H2.

  intros Htype.
  inversion Htype.
Qed.

Lemma canonical_form_arrow :
  forall c v s1 s2 l,
    value v ->
    typing c v (Arrow s1 s2 l) ->
    exists x s1' e l',
      v = (Abs x s1' e l') /\ subtype s1 s1' /\ flows_to l' l.
Proof.
  intros c v s1 s2 l Hval.
  inversion Hval; subst; intro Htype.

  inversion Htype.
  inversion Htype.

  inversion Htype; subst.
  exists x.
  exists t.
  exists e.
  exists l0.
  split.
  reflexivity.
  split.
  assumption.
  assumption.
Qed.

Lemma substitution_lemma :
  forall e v c x s s',
    typing (Extend type x s' c) e s ->
    typing (Empty type) v s' ->
    typing c (sub v x e) s.
Proof.
  intros e v c x s s' Htype Htypev.
  generalize dependent s.
  generalize dependent c.
  induction e; intros; simpl.

  apply typing_inversion_true in Htype.
  destruct Htype as [l' [Hx Hflow]].
  subst.
  apply typing_true; auto.

  apply typing_inversion_false in Htype.
  destruct Htype as [l' [Hx Hflow]].
  subst.
  apply typing_false; auto.

  destruct (all_types_have_label s) as [l Hs].
  apply typing_inversion_cond with (l := l) in Htype; auto.
  destruct Htype as [l' Htype].
  destruct Htype as [s'' Htype].
  destruct Htype as [He1 [He2 [He3 Hsub]]].
  apply typing_cond with (s := s'')(l := l'); auto.

  apply typing_inversion_var in Htype.
  destruct Htype as [s'' [Hfound Hsub]].
  destruct (eq_nat_dec x n).
  subst.
  simpl in Hfound.
  rewrite <- beq_nat_refl in Hfound.
  inversion Hfound; subst.
  rewrite <- beq_nat_refl.
  apply subsumption with (s := s'').
  apply env_invariance with (c := Empty _).
  apply Htypev.
  intros.
  apply (free_in_env x) in Htypev.
  destruct Htypev.
  inversion H0.
  apply H.
  apply Hsub.
  apply beq_nat_false_iff in n0.
  rewrite n0.
  apply typing_var with (s := s'').
  simpl in Hfound.
  rewrite NPeano.Nat.eqb_sym in Hfound.
  rewrite n0 in Hfound.
  assumption.
  apply Hsub.

  rename n into y.
  apply typing_inversion_abs in Htype.
  destruct Htype as [s1 [s2 [s2' [l' [Heq [He [Hsubs1t [Hsubs2's2 Hflow]]]]]]]].
  subst.
  case_eq (beq_nat x y); intros.
  apply beq_nat_true in H.
  subst.
  apply typing_abs with (s2 := s2'); auto.
  apply env_invariance with (c := (Extend _ y t (Extend _ y s' c))).
  apply He.
  intros.
  apply env_shadow.

  apply typing_abs with (s2 := s2'); auto.
  apply IHe.
  apply env_invariance with (c := (Extend _ y t (Extend _ x s' c))).
  apply He.
  intros.
  apply env_permute.
  rewrite NPeano.Nat.eqb_sym.
  apply H.

  destruct (all_types_have_label s) as [l].
  apply typing_inversion_app with (l := l) in Htype; auto.

  destruct Htype as [l' [s1 [s1' [s2 [He1 [He2 [Hsub1 Hsub2]]]]]]].
  apply typing_app with (s2 := s1) (s := s2) (l := l')(s2' := s1'); auto.
Qed.

Lemma stamp_mono :
  forall s l,
    subtype s (stamp_type s l).
Proof.
  destruct s; intros; simpl.
  apply TBoolSub.
  apply join_is_upper_bound.
  apply TFunSub.
  apply subtype_refl.
  apply subtype_refl.
  apply join_is_upper_bound.
Qed.

Lemma stamp_typing :
  forall l l' c v s,
    typing c v s ->
    flows_to l l' ->
    typing c (stamp v l) (stamp_type s l').
Proof.
  intros l l' c v s Htype.
  revert l l'.
  inversion Htype; subst; intros l'' l''' Hflow; simpl.

  apply typing_true.
  apply join_is_least_upper_bound.
  apply flows_to_trans with (l' := l'); auto.
  apply join_is_upper_bound.
  apply flows_to_trans with (l' := l'''); auto.
  apply join_is_upper_bound.

  apply typing_false.
  apply join_is_least_upper_bound.
  apply flows_to_trans with (l' := l'); auto.
  apply join_is_upper_bound.
  apply flows_to_trans with (l' := l'''); auto.
  apply join_is_upper_bound.

  apply typing_cond with (s := s0)(l := l); auto.
  apply subtype_trans with (t' := s); auto.
  apply stamp_mono.

  apply typing_app with (s2 := s2)(s2' := s2')(s := s0)(l := l); auto.
  apply subtype_trans with (t' := s); auto.
  apply stamp_mono.

  apply typing_abs with (s2 := s2); auto.
  apply join_is_least_upper_bound; auto.
  apply flows_to_trans with (l' := l'); auto.
  apply join_is_upper_bound.
  apply flows_to_trans with (l' := l'''); auto.
  apply join_is_upper_bound.

  apply typing_var with (s := s0); auto.
  apply subtype_trans with (t' := s); auto.
  apply stamp_mono.
Qed.

Lemma stamp_join :
  forall s l1 l2 l' s',
    subtype (stamp_type (stamp_type s l1) l2) s' ->
    type_with_label s' l' ->
    type_with_label s l1 ->
    flows_to (join l1 l2) l'.
Proof.
  destruct s; destruct s'; simpl; intros; subst.
  rewrite <- join_idempotent in H.
  inversion H; subst; auto.
  inversion H.
  inversion H.
  inversion H; subst.
  rewrite <- join_idempotent in H8.
  apply H8.
Qed.

Lemma preservation :
  forall e v s,
    big_step e v ->
    typing (Empty _) e s ->
    typing (Empty _) v s.
Proof.
  intros e v s Hstep.
  revert s.
  induction Hstep; intros s' Htype.

  apply Htype.

  destruct (all_types_have_label s') as [l' Hs'].
  apply typing_inversion_cond with (l := l') in Htype; auto.
  destruct Htype as [l'' [s [He1 [He2 [He3 Hsub]]]]].

  destruct (all_types_have_label s) as [ls Hls].
  rewrite (stamp_idemp _ _ Hls) in Hsub.
  rewrite (stamp_idemp _ _ Hls) in He2.
  rewrite (stamp_idemp _ _ Hls) in He3.
  assert (flows_to (join ls l'') l').
  apply stamp_join with (s := s)(s' := s'); auto.

  specialize (IHHstep2 _ He2).
  specialize (IHHstep1 _ He1).
  apply typing_inversion_true in IHHstep1.
  destruct IHHstep1 as [l''' [Heq Hflow]].
  inversion Heq; subst; clear Heq.

  rewrite (stamp_idemp _ _ Hs') in Hsub.
  apply stamp_preserves_subtype in Hsub.
  rewrite (stamp_idemp _ _ Hs').
  apply stamp_typing.
  apply subsumption with (s := s); auto.
  rewrite (stamp_idemp _ _ Hls).
  apply IHHstep2.
  rewrite <- (stamp_idemp _ _ Hls) in Hsub.
  rewrite <- (stamp_idemp _ _ Hs') in Hsub.
  apply Hsub.
  apply flows_to_trans with (l' := l'''); auto.
  apply flows_to_trans with (l' := (join ls l''')); auto.
  apply join_is_upper_bound.

  destruct (all_types_have_label s') as [l' Hs'].
  apply typing_inversion_cond with (l := l') in Htype; auto.
  destruct Htype as [l'' [s [He1 [He2 [He3 Hsub]]]]].

  destruct (all_types_have_label s) as [ls Hls].
  rewrite (stamp_idemp _ _ Hls) in Hsub.
  rewrite (stamp_idemp _ _ Hls) in He2.
  rewrite (stamp_idemp _ _ Hls) in He3.
  assert (flows_to (join ls l'') l').
  apply stamp_join with (s := s)(s' := s'); auto.

  specialize (IHHstep2 _ He2).
  specialize (IHHstep1 _ He1).
  apply typing_inversion_false in IHHstep1.
  destruct IHHstep1 as [l''' [Heq Hflow]].
  inversion Heq; subst; clear Heq.

  rewrite (stamp_idemp _ _ Hs') in Hsub.
  apply stamp_preserves_subtype in Hsub.
  rewrite (stamp_idemp _ _ Hs').
  apply stamp_typing.
  apply subsumption with (s := s); auto.
  rewrite (stamp_idemp _ _ Hls).
  apply IHHstep2.
  rewrite <- (stamp_idemp _ _ Hls) in Hsub.
  rewrite <- (stamp_idemp _ _ Hs') in Hsub.
  apply Hsub.
  apply flows_to_trans with (l' := l'''); auto.
  apply flows_to_trans with (l' := (join ls l''')); auto.
  apply join_is_upper_bound.


  destruct (all_types_have_label s') as [l' Hl'].
  apply typing_inversion_app with (l := l') in Htype; auto.
  destruct Htype as [l'' [s1 [s1' [s2 [He1 [He2 [Hsub1 Hsub2]]]]]]].

  specialize (IHHstep1 _ He1).
  apply typing_inversion_abs in IHHstep1.
  destruct IHHstep1 as [s0 [s3 [s2' [l0 [Heq [Htype [Hsubs0 [Hsubs2' Hflow]]]]]]]].
  inversion Heq; subst; clear Heq.
  apply substitution_lemma with (v := v) in Htype.
  specialize (IHHstep3 _ Htype).
  apply subsumption with (s := (stamp_type s2' l0)).
  apply stamp_typing; auto.
  apply subtype_trans with (t' := (stamp_type s3 l0)); auto.
  apply stamp_l_preserves_subtype; auto.
  apply IHHstep2; auto.
  apply subsumption with (s := s1'); auto.
  apply subtype_trans with (t' := s0); auto.
Qed.

Definition type_with_at_least_label t l :=
  match t with
    | Bool l' => flows_to l l'
    | Arrow _ _ l' => flows_to l l'
  end.

Lemma subtype_raises_label :
  forall s' s l,
    subtype s' s ->
    type_with_at_least_label s' l ->
    type_with_at_least_label s l.
Proof.
  intros s' s l Hsub.
  inversion Hsub; intro Htype; simpl in Htype; subst; simpl; apply flows_to_trans with (l' := l0); auto.
Qed.


Definition non_interference e :=
  forall t x v1 v2 v,
    type_with_label t High ->
    typing (Extend _ x t (Empty _)) e (Bool Low) ->
    value v1 ->
    value v2 ->
    typing (Empty _) v1 t ->
    typing (Empty _) v2 t ->
    ((big_step (sub v1 x e) v) <-> (big_step (sub v2 x e) v)).

Lemma values_non_interferent :
  forall v,
    value v ->
    non_interference v.
Proof.
  intros.
  unfold non_interference.
  inversion H; intros.
  split; auto.
  split; auto.
  split; auto.
  intros.
  inversion H2.
  inversion H2.
Qed.

Lemma big_step_preserves_non_interference :
  forall e v,
    non_interference e ->
    big_step e v ->
    non_interference v.
Proof.
  intros.
  apply big_steps_to_value in H0.
  apply values_non_interferent.
  apply H0.
Qed.

Fixpoint LR sigma e1 e2 t l' : Prop :=
  type_with_label t l' /\
  exists v1 v2,
    big_step e1 v1 /\
    big_step e2 v2 /\
    typing (Empty _) v1 t /\
    typing (Empty _) v2 t /\
    match t with
      | Bool l =>
        flows_to l sigma ->
        v1 = v2
      | Arrow s1 s2 l =>
        forall ls1,
          type_with_label s1 ls1 ->
          forall v1' v2' ls1,
            flows_to l sigma ->
            LR sigma v1' v2' s1 ls1 ->
            LR sigma (App v1 v1') (App v2 v2') s2 l
    end.

Lemma unfold_LR :
  forall sigma e1 e2 t l' ,
    LR sigma e1 e2 t l' =
    (type_with_label t l' /\
     exists v1 v2,
       big_step e1 v1 /\
       big_step e2 v2 /\
       typing (Empty _) v1 t /\
       typing (Empty _) v2 t /\
       match t with
         | Bool l =>
           flows_to l sigma ->
           v1 = v2
         | Arrow s1 s2 l =>
           forall ls1,
             type_with_label s1 ls1 ->
             forall v1' v2' ls1,
               flows_to l sigma ->
               LR sigma v1' v2' s1 ls1 ->
               LR sigma (App v1 v1') (App v2 v2') s2 l
       end).
Proof.
  destruct t; reflexivity.
Qed.

Lemma join_comm :
  forall l l',
    join l l' = join l' l.
Proof.
  destruct l; destruct l'; reflexivity.
Qed.

Lemma join_with_l_mono :
  forall l1 l2 l,
    flows_to l1 l2 ->
    flows_to (join l1 l) (join l2 l).
Proof.
  intros.
  apply join_is_least_upper_bound.
  apply flows_to_trans with (l' := l2); auto.
  apply join_is_upper_bound.
  apply join_is_upper_bound.
Qed.

Lemma big_step_preserves_LR :
  forall sigma s l e1 v1 e2 v2,
    big_step e1 v1 ->
    big_step e2 v2 ->
    LR sigma e1 e2 s l ->
    LR sigma v1 v2 s l.
Proof.
  intros sigma.
  induction s; intros l' e1 v1 e2 v2 Hstep1 Hstep2 Hrel;
  simpl in Hrel;
  destruct Hrel as [Hl [v1' [v2' [Htype1 [Htype2 [Hstep1' [Hstep2' Hrel]]]]]]];
  subst;
  simpl;
  split;
  auto.

  exists v1.
  exists v2.
  split.
  apply big_step_val.
  eapply big_steps_to_value.
  apply Hstep1.
  split.
  apply big_step_val.
  eapply big_steps_to_value.
  apply Hstep2.
  rewrite (big_step_deterministic e1 v1 v1'); auto.
  rewrite (big_step_deterministic e2 v2 v2'); auto.

  exists v1.
  exists v2.
  split.
  apply big_step_val.
  eapply big_steps_to_value.
  apply Hstep1.
  split.
  apply big_step_val.
  eapply big_steps_to_value.
  apply Hstep2.
  rewrite (big_step_deterministic e1 v1 v1'); auto.
  rewrite (big_step_deterministic e2 v2 v2'); auto.
Qed.

Lemma value_steps_to_self :
  forall v v',
    value v ->
    big_step v v' ->
    v' = v.
Proof.
  intros.
  inversion H0; subst; auto.
  inversion H.
  inversion H.
  inversion H.
Qed.

Lemma big_step_preserves_LR' :
  forall sigma s e1 e2 v1 v2 l,
    typing (Empty _) e1 s ->
    typing (Empty _) e2 s ->
    big_step e1 v1 ->
    big_step e2 v2 ->
    LR sigma v1 v2 s l ->
    LR sigma e1 e2 s l.
Proof.
  intros sigma s.
  induction s; intros e1 e2 v1 v2 l' Htype1 Htype2 Hstep1 Hstep2 Hrel;
  destruct Hrel as [Hl [v1' [v2' [Hstep1' [Hstep2' [Htype1' [Htype2' Hrel]]]]]]];
  simpl;
  split;  auto.

  exists v1.
  exists v2.
  split; auto.
  split; auto.
  split.
  eapply preservation.
  apply Hstep1.
  apply Htype1.
  split.
  eapply preservation.
  apply Hstep2.
  apply Htype2.
  intros.
  rewrite (big_step_deterministic e1 v1 v1'); auto.
  rewrite (big_step_deterministic e2 v2 v2'); auto.
  rewrite (value_steps_to_self v2 v2'); auto.
  eapply big_steps_to_value.
  apply Hstep2.
  rewrite (value_steps_to_self v1 v1'); auto.
  eapply big_steps_to_value.
  apply Hstep1.

  exists v1.
  exists v2.
  split; auto.
  split; auto.
  split.
  eapply preservation.
  apply Hstep1.
  auto.
  split.
  eapply preservation.
  apply Hstep2.
  auto.
  intros.
  rewrite (big_step_deterministic e1 v1 v1'); auto.
  rewrite (big_step_deterministic e2 v2 v2'); auto.
  eapply Hrel; auto.
  apply H.
  apply H1.
  rewrite (value_steps_to_self v2 v2'); auto.
  eapply big_steps_to_value; auto.
  apply Hstep2.
  rewrite (value_steps_to_self v1 v1'); auto.
  eapply big_steps_to_value; auto.
  apply Hstep1.
Qed.

Definition substitution := environment expr.

Fixpoint substitute s e :=
  match s with
    | Empty =>
      e
    | Extend x v s' =>
      substitute s' (sub v x e)
  end.

Definition assignment := environment type.

Fixpoint extend (a : assignment) (c : environment type) :=
  match a with
    | Empty =>
      c
    | Extend x s a' =>
      Extend _ x s (extend a' c)
  end.

Inductive instantiations : label -> assignment -> environment expr -> environment expr -> Prop :=
| instantiate_empty :
    forall sigma,
      instantiations sigma (Empty _) (Empty _) (Empty _)
| instantiate_extend :
    forall v1 v2 ass env1 env2 sigma s l x,
      value v1 ->
      value v2 ->
      instantiations sigma ass env1 env2 ->
      LR sigma v1 v2 s l ->
      instantiations sigma
                     (Extend type x s ass)
                     (Extend expr x v1 env1)
                     (Extend expr x v2 env2).

Lemma vacous_substitution :
  forall x e,
    ~ free_in x e ->
    forall v,
      sub v x e = e.
Proof.
  induction e; intros.
  reflexivity.
  reflexivity.
  simpl.

  rewrite IHe1, IHe2, IHe3; auto;
  unfold not;
  intros;
  apply H;
  apply free_in_cond; auto.

  simpl.
  case_eq (beq_nat x n); auto.
  intros.
  apply beq_nat_true in H0.
  subst.
  contradict H.
  apply free_in_var.

  simpl.
  case_eq (beq_nat x n); auto.
  intros.
  apply beq_nat_false in H0.
  destruct (free_in_dec x e).
  contradict H.
  apply free_in_abs; auto.
  rewrite IHe; auto.

  simpl.
  rewrite IHe1, IHe2; auto;
  unfold not;
  intros;
  apply H;
  apply free_in_app; auto.
Qed.

Lemma substitution_closed :
  forall e,
    closed e ->
    forall v x,
      sub v x e = e.
Proof.
  intros.
  apply vacous_substitution.
  apply H.
Qed.

Lemma substition_not_free_in :
  forall e x v,
    closed v ->
    ~ free_in x (sub v x e).
Proof.
  unfold closed, not.
  induction e; simpl; intros.

  inversion H0.
  inversion H0.

  inversion H0; subst; clear H0.
  destruct H3.
  apply (IHe1 _ _ H H0).
  destruct H0.
  apply (IHe2 _ _ H H0).
  apply (IHe3 _ _ H H0).

  case_eq (beq_nat x n); intros.
  rewrite H1 in H0.
  apply (H x); auto.
  rewrite H1 in H0.
  inversion H0; subst.
  rewrite <- beq_nat_refl in H1; auto.
  inversion H1.

  case_eq (beq_nat x n); intros.
  rewrite H1 in H0.
  inversion H0; subst.
  contradict H5.
  apply beq_nat_true; auto.
  rewrite H1 in H0.
  inversion H0; subst.
  apply (IHe x v); auto.

  inversion H0; subst.
  destruct H3.
  apply (IHe1 x v); auto.
  apply (IHe2 x v); auto.
Qed.

Lemma duplicate_substitution :
  forall v' x e v,
    closed v ->
    sub v' x (sub v x e) = (sub v x e).
Proof.
  intros.
  eapply vacous_substitution.
  apply substition_not_free_in.
  apply H.
Qed.

Lemma swap_substitution :
  forall e x x' v v',
  x <> x' ->
  closed v ->
  closed v' ->
  sub v x (sub v' x' e) = sub v' x' (sub v x e).
Proof.
  induction e; intros x x' v v' Hneq Hv Hv'.
  reflexivity.
  reflexivity.
  simpl.
  rewrite IHe1, IHe2, IHe3; auto.
  simpl.
  case_eq (beq_nat x n); case_eq (beq_nat x' n); intros; auto; simpl.
  contradict Hneq.
  apply beq_nat_true in H.
  apply beq_nat_true in H0.
  subst.
  reflexivity.
  rewrite H0.
  symmetry.
  eapply substitution_closed; auto.
  rewrite H.
  eapply substitution_closed; auto.
  rewrite H0, H.
  reflexivity.

  simpl; case_eq(beq_nat x n); case_eq (beq_nat x' n); intros; auto; simpl.
  contradict Hneq.
  apply beq_nat_true in H.
  apply beq_nat_true in H0.
  subst; auto.
  rewrite H, H0.
  reflexivity.
  rewrite H, H0.
  reflexivity.
  rewrite H, H0.
  rewrite IHe; auto.

  simpl.
  rewrite IHe1, IHe2; auto.
Qed.

Lemma substitute_close :
  forall env e,
    closed e ->
    substitute env e = e.
Proof.
  induction env; intros.
  reflexivity.
  simpl.
  rewrite substitution_closed; auto.
Qed.

Fixpoint closed_env env :=
  match env with
    | Empty => True
    | Extend x e env' => closed e /\ closed_env env'
  end.

Lemma sub_substitute :
  forall env v x e,
    closed v ->
    closed_env env ->
    substitute env (sub v x e) = sub v x (substitute (drop x env) e).
Proof.
  induction env; intros.
  reflexivity.
  simpl.
  case_eq (beq_nat x n); intros.
  apply beq_nat_true in H1; subst.
  rewrite duplicate_substitution; auto.
  apply IHenv; auto.
  apply H0.
  apply beq_nat_false in H1.
  rewrite swap_substitution; auto.
  apply IHenv; auto.
  apply H0.
  apply H0.
Qed.

Lemma substitute_var :
  forall env x,
    closed_env env ->
    substitute env (Var x) =
    match lookup x env with
      | Some v => v
      | Non => Var x
    end.
Proof.
  induction env; intros; simpl.
  reflexivity.
  case_eq (beq_nat x n); intros.
  apply beq_nat_true in H0; subst.
  rewrite <- beq_nat_refl.
  apply substitute_close; auto.
  apply H.
  rewrite NPeano.Nat.eqb_sym.
  rewrite H0.
  apply IHenv; auto.
  apply H.
Qed.

Lemma substitute_abs :
  forall env x s e l,
    substitute env (Abs x s e l) = Abs x s (substitute (drop x env) e) l.
Proof.
  induction env; intros.
  reflexivity.
  case_eq (beq_nat x n); intros.
  apply beq_nat_true in H; subst.
  simpl.
  rewrite <- beq_nat_refl.
  apply IHenv; auto.

  simpl.
  rewrite NPeano.Nat.eqb_sym, H.
  apply IHenv.
Qed.

Lemma substitute_app :
  forall env e1 e2,
    substitute env (App e1 e2) = App (substitute env e1) (substitute env e2).
Proof.
  induction env; auto; intros; auto.
  apply IHenv.
Qed.

Lemma substitute_true :
  forall env l,
    substitute env (TT l) = TT l.
Proof.
  induction env; auto.
Qed.

Lemma substitute_false :
  forall env l,
    substitute env (FF l) = FF l.
Proof.
  induction env; auto.
Qed.

Lemma substitute_cond :
  forall env e1 e2 e3,
    substitute env (Cond e1 e2 e3) =
    Cond (substitute env e1) (substitute env e2) (substitute env e3).
Proof.
  induction env; auto; intros; auto.
  apply IHenv.
Qed.

Lemma extend_lookup :
  forall c x,
    lookup x c = lookup x (extend c (Empty _)).
Proof.
  induction c; intros; simpl; auto;
  case_eq (beq_nat x n); intros; auto.
Qed.

Lemma extend_drop :
  forall ass c x x',
    lookup x' (extend (drop x ass) c) =
    if beq_nat x x'
    then lookup x' c
    else lookup x' (extend ass c).
Proof.
  induction ass; intros.
  case_eq (beq_nat x x'); intros; auto.

  simpl.
  case_eq (beq_nat x n); intros; simpl.
  apply beq_nat_true in H; subst.
  case_eq (beq_nat n x'); intros.
  apply beq_nat_true in H; subst.
  rewrite IHass.
  rewrite <- beq_nat_refl.
  reflexivity.
  rewrite NPeano.Nat.eqb_sym.
  rewrite H.
  rewrite IHass.
  rewrite H.
  reflexivity.
  case_eq (beq_nat x' n); intros.
  apply beq_nat_true in H0; subst.
  rewrite H.
  reflexivity.
  rewrite IHass.
  reflexivity.
Qed.

Lemma instantiation_domains_match :
  forall ass sigma env1 env2 x s,
    instantiations sigma ass env1 env2 ->
    lookup x ass = Some s ->
    exists v1 v2,
      lookup x env1 = Some v1 /\
      lookup x env2 = Some v2.
Proof.
  intros ass sigma env1 env2 x s Hin.
  revert x s.
  induction Hin; intros.
  inversion H.

  simpl in H2.
  case_eq (beq_nat x0 x); intros.
  exists v1.
  exists v2.
  simpl.
  rewrite H3.
  split; reflexivity.
  simpl in H2.
  rewrite H3 in H2.
  specialize (IHHin _ _ H2).
  destruct IHHin as [v1' [v2' [Hl1 Hl2]]].
  exists v1'.
  exists v2'.
  simpl.
  rewrite H3.
  split; auto.
Qed.

Lemma instantiation_envs_closed :
  forall ass sigma  env1 env2,
    instantiations sigma ass env1 env2 ->
    closed_env env1 /\ closed_env env2.
Proof.
  intros ass sigma env1 env2 Hin.
  induction Hin.
  split; constructor.

  simpl.
  rewrite unfold_LR in H1.
  destruct H1 as [Hlab [v1' [v2' [Hstep1 [Hstep2 [Htype1 [Htype2 _]]]]]]].
  apply typeable_closed in Htype1.
  apply typeable_closed in Htype2.
  destruct IHHin.
  split.
  split; auto.
  rewrite <- (value_steps_to_self v1 v1'); auto.
  split; auto.
  rewrite <- (value_steps_to_self v2 v2'); auto.
Qed.

Lemma type_with_labels :
  forall s l l',
    type_with_label s l ->
    type_with_at_least_label s l' ->
    flows_to l' l.
Proof.
  intros.
  destruct s;
  simpl in *; subst;
  auto.
Qed.

Lemma instantiations_LR :
  forall sigma ass env1 env2,
    instantiations sigma ass env1 env2 ->
    forall x s v1 v2 ls,
      type_with_label s ls ->
      lookup x ass = Some s ->
      lookup x env1 = Some v1 ->
      lookup x env2 = Some v2 ->
      LR sigma v1 v2 s ls.
Proof.
  intros sigma ass env1 env2 Hin.
  induction Hin; intros.
  inversion H0.
  simpl in *.
  case_eq (beq_nat x0 x); intros.
  apply beq_nat_true in H6; subst; auto.
  rewrite <- beq_nat_refl in *.
  inversion H3; subst; clear H3.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5.
  assert (l = ls).
  rewrite unfold_LR in H1.
  destruct H1 as [H1 _].
  destruct s0; simpl in *; intros; subst; auto.
  subst.
  apply H1.
  rewrite H6 in *.
  apply IHHin with (x := x0); auto.
Qed.

Lemma instantiations_drop :
  forall sigma ass env1 env2,
  instantiations sigma ass env1 env2 ->
  forall x,
    instantiations sigma (drop x ass) (drop x env1) (drop x env2).
Proof.
  intros sigma ass env1 env2 Hi.
  induction Hi; intros.
  simpl.
  constructor.
  simpl.
  case_eq (beq_nat x0 x); intros.
  apply IHHi; auto.
  eapply instantiate_extend; auto.
  apply H1; auto.
Qed.

Lemma typing_at_least :
  forall s l e,
    typing (Empty _) e (stamp_type s l) ->
    type_with_at_least_label s l ->
    typing (Empty _) e s.
Proof.
  induction s; intros.
  simpl in *.
  eapply subsumption.
  apply H.
  apply TBoolSub.
  rewrite join_comm.
  rewrite <- H0.
  apply flows_to_refl.
  simpl in *.
  eapply subsumption.
  apply H.
  apply TFunSub.
  apply subtype_refl.
  apply subtype_refl.
  rewrite join_comm.
  rewrite <- H0.
  apply flows_to_refl.
Qed.

Lemma substitue_lemma :
  forall sigma ass env1 env2,
    instantiations sigma ass env1 env2 ->
    forall c e s,
      typing (extend ass c) e s ->
      typing c (substitute env1 e) s /\
      typing c (substitute env2 e) s.
Proof.
  intros sigma ass env1 env2 Hi.
  induction Hi; intros; auto.

  simpl in *.
  rewrite unfold_LR in H1.
  destruct H1 as [Hlab [v1' [v2' [Hstep1 [Hstep2 [Htype1 [Htype2 Hrel]]]]]]].
  split.
  apply IHHi.
  eapply substitution_lemma.
  apply H2.
  rewrite <- (value_steps_to_self v1 v1'); auto.
  apply IHHi.
  eapply substitution_lemma.
  apply H2.
  rewrite <- (value_steps_to_self v2 v2'); auto.
Qed.

Lemma subtype_relation :
  forall sigma e1 e2 s s' ls ls',
    subtype s s' ->
    LR sigma e1 e2 s ls ->
    type_with_label s' ls' ->
    LR sigma e1 e2 s' ls'.
Proof.
Admitted.

Theorem FTLR :
  forall sigma ass e s l env1 env2,
    typing (extend ass (Empty _)) e s ->
    type_with_label s l ->
    instantiations sigma ass env1 env2 ->
    LR sigma (substitute env1 e) (substitute env2 e) s l.
Proof.
  intros sigma ass e s l env1 env2 Htype.
  remember (extend ass (Empty _)) as gamma.
  assert (forall x, lookup x gamma = lookup x ass).
  intros.
  rewrite Heqgamma.
  rewrite <- extend_lookup.
  reflexivity.
  clear Heqgamma.
  generalize dependent ass.
  revert l.
  induction Htype; intros.

  simpl in *; subst.
  split; auto.
  exists (TT l).
  exists (TT l).
  rewrite 2 substitute_true.
  split.
  apply big_step_val; constructor.
  split.
  apply big_step_val; constructor.
  split.
  apply typing_true; auto.
  split; auto.
  apply typing_true; auto.

  simpl in *; subst.
  split; auto.
  exists (FF l).
  exists (FF l).
  rewrite 2 substitute_false.
  split.
  apply big_step_val; constructor.
  split.
  apply big_step_val; constructor.
  split.
  apply typing_false; auto.
  split; auto.
  apply typing_false; auto.

  admit.



  admit.

  admit.

  destruct (all_types_have_label s) as [ls Hl].
  eapply (subtype_relation _ _ _ _ _ ls l).
  apply H0.
  rewrite 2 substitute_var.
  specialize (H1 x).
  rewrite H in H1.
  symmetry in H1.
  pose proof (instantiation_domains_match ass sigma env1 env2 x s H3 H1).
  destruct H4.
  destruct H4.
  destruct H4.
  rewrite H4, H5.
  eapply (instantiations_LR sigma ass env1 env2 H3); auto.
  apply H1.
  auto.
  auto.
  apply (instantiation_envs_closed _ _ _ _ H3).
  apply (instantiation_envs_closed _ _ _ _ H3).
  auto.
Qed.

Theorem ni :
  forall e,
    non_interference e.
Proof.
  unfold non_interference; intros.
  replace e with (substitute (Empty _) e); auto.
  replace (Extend type x t (Empty _)) with (extend (Extend _ x t (Empty _)) (Empty _)) in H0; auto.
  pose proof (FTLR Low (Extend _ x t (Empty _)) e (Bool Low) Low (Extend _ x v1 (Empty _)) (Extend _ x v2 (Empty _)) H0 eq_refl) as Hrel.
  assert (instantiations Low (Extend type x t (Empty type))
           (Extend expr x v1 (Empty expr)) (Extend expr x v2 (Empty expr))).
  eapply (instantiate_extend _ _ _ _ _ _ _ High); auto.
  apply instantiate_empty.
  rewrite unfold_LR.
  split; auto.
  exists v1.
  exists v2.
  split.
  constructor; auto.
  split.
  constructor; auto.
  split; auto.
  split; auto.
  destruct t; simpl in H; subst.
  intros.
  inversion H.
  intros.
  inversion H5.
  apply Hrel in H5.
  simpl in H5.
  destruct H5 as [_ [v1' [v2' [Hstep1 [Hstep2 [Htype1 [Htype2 Hflows]]]]]]].
  specialize (Hflows eq_refl); subst.
  replace (Empty expr) with (drop x (Empty expr)); auto.
  rewrite <-2 sub_substitute.
  simpl.
  split; intros.
  rewrite (big_step_deterministic (sub v1 x e) v v2'); auto.
  rewrite (big_step_deterministic (sub v2 x e) v v2'); auto.

  eapply typeable_closed.
  apply H4.
  constructor.
  eapply typeable_closed.
  apply H3.
  constructor.
Qed.
