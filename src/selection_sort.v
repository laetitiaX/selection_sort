(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import FunInd.
Require Import Sorted.
Require Import Permutation.
Require Import Recdef.

(* end hide *)
 
(** A função [select_min] a seguir, recebe uma lista de naturais e retorna o menor elemento desta lista. Se a lista for vazia, [select_min nil] retorna None. *)
 
Function select_min (l : list nat) {measure length l} : option nat :=
  match l with
  | nil => None
  | h::nil => Some h
  | h1::h2::tl => if h1 <=? h2 then select_min (h1::tl) else select_min (h2::tl)
  end.
Proof.
  - auto.
  - auto.
Defined.
 
Definition le_all x l := forall y, In y l -> x <= y.
 
(** A correção da função [select_min] é estabelecida provando-se que, se [select_min l] retorna um natural [m] então [m] é menor ou igual do que todos os elementos de [l]. *)
 
Lemma select_min_correct : forall l m, select_min l = Some m -> le_all m l.
Proof.
  intros l m H. functional induction (select_min l).
  - (* Caso 1: l = nil *)
    discriminate H.
 
  - (* Caso 2: l = h :: nil *)
    (* Extraímos a igualdade h = m e substituímos no contexto *)
    inversion H. subst.
    (* Expandimos a definição de le_all *)
    unfold le_all.
    intros y Hy.
    (* O operador In verifica se 'y' está na lista [m] *)
    simpl in Hy.
    destruct Hy as [Hy_eq_m | Hy_falso].
    + (* Sub-caso 2.1: y = m *)
      subst. lia.
    + (* Sub-caso 2.2: y está na lista vazia *)
      contradiction.
- (* Caso 3: h1 <=? h2 = true *)
    (* Ativamos a hipótese de indução com a hipótese H *)
    apply IHo in H.
    apply Nat.leb_le in e0.
 
    (* Expandimos a definição do nosso objetivo e pegamos um elemento qualquer 'y' *)
    unfold le_all in *. intros y Hy.
    (* O y pode ser h1, h2, ou estar no resto da lista (tl) *)
    simpl in Hy.
    destruct Hy as [Hy_h1 | [Hy_h2 | Hy_tl]].
    + (* Sub-caso 3.1: y é o h1 *)
      subst y. apply H. simpl. left. reflexivity.
    + (* Sub-caso 3.2: y é o h2 *)
      subst y.
      (* Sabemos por H que m <= h1. Como h1 <= h2 (e0), logo m <= h2. *)
      assert (Hm_h1: m <= h1). { apply H. simpl. left. reflexivity. }
      lia.
    + (* Sub-caso 3.3: y está em tl *)
      apply H. simpl. right. assumption.
 
  - (* Caso 4: h1 <=? h2 = false (ou seja, h2 < h1) *)
    (* A lógica é idêntica ao Caso 3, mas espelhada para o caso falso *)
    apply IHo in H.
    apply Nat.leb_gt in e0.
 
    unfold le_all in *. intros y Hy.
    simpl in Hy.
    destruct Hy as [Hy_h1 | [Hy_h2 | Hy_tl]].
    + (* Sub-caso 4.1: y é o h1 *)
      subst y.
      (* Sabemos por H que m <= h2. Como h2 < h1 (e0), logo m <= h1. *)
      assert (Hm_h2: m <= h2). { apply H. simpl. left. reflexivity. }
      lia.
    + (* Sub-caso 4.2: y é o h2 *)
      subst y. apply H. simpl. left. reflexivity.
    + (* Sub-caso 4.3: y está em tl *)
      apply H. simpl. right. assumption.
Qed.
 
(** A função principal [ss] recebe uma lista de naturais [l], e retorna uma permutação ordenada de [l]: *)
 
(** Função para remover a primeira ocorrência *)
Fixpoint remove_one (x: nat) (l: list nat) : list nat :=
  match l with
  | nil => nil
  | y::tl => if x =? y then tl else y :: (remove_one x tl)
  end.
 
(** Lema auxiliar: remover uma ocorrência de um elemento que está na lista
    estritamente diminui o tamanho da lista. Necessário para justificar que
    a recursão em [ss_aux]/[ss] *)
Lemma remove_one_length : forall x l, In x l -> length (remove_one x l) < length l.
Proof.
  intros x l.
  induction l as [| y l' IH]; intros Hin.
  - (* l = nil: In x nil é falso *)
    simpl in Hin. contradiction.
  - (* l = y :: l' *)
    simpl in Hin.
    simpl.
    destruct (x =? y) eqn:Heq.
    + (* x = y: remove_one devolve l' *)
      simpl. lia.
    + (* x <> y: a busca continua em l' *)
      apply Nat.eqb_neq in Heq.
      destruct Hin as [Hxy | Hin'].
      * exfalso. apply Heq. symmetry. exact Hxy.
      * simpl. assert (H := IH Hin'). lia.
Qed.
 
(** Lema auxiliar: se [x] está em [l], então [l] é uma permutação de
    [x :: remove_one x l]. Usado para reconstruir a lista original a
    partir do mínimo retirado. *)
Lemma perm_add_one : forall x l, In x l -> Permutation l (x :: remove_one x l).
Proof.
  intros x l.
  induction l as [| y l' IH]; intros Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    simpl.
    destruct (x =? y) eqn:Heq.
    + (* x = y *)
      apply Nat.eqb_eq in Heq. subst y.
      apply Permutation_refl.
    + (* x <> y *)
      apply Nat.eqb_neq in Heq.
      destruct Hin as [Hxy | Hin'].
      * exfalso. apply Heq. symmetry. exact Hxy.
      * assert (Hp := IH Hin').
        apply Permutation_trans with (y :: x :: remove_one x l').
        -- apply perm_skip. exact Hp.
        -- apply perm_swap.
Qed.
 
  (** Lema auxiliar 1: O elemento mínimo encontrado pertence sempre à lista original *)
Lemma select_min_in : forall l m, select_min l = Some m -> In m l.
Proof.
  intros l m H. functional induction (select_min l).
  - discriminate.
  - inversion H. subst. simpl. left. reflexivity.
  - apply IHo in H. simpl in *. destruct H as [H1 | Htl].
    + left. exact H1.
    + right. right. exact Htl.
  - apply IHo in H. simpl in *. destruct H as [H2 | Htl].
    + right. left. exact H2.
    + right. right. exact Htl.
Qed.
 
(** Função principal com Combustível *)
Fixpoint ss_aux (fuel: nat) (l: list nat) : list nat :=
  match fuel with
  | 0 => nil
  | S fuel' =>
      match select_min l with
      | None => nil
      | Some m => m :: (ss_aux fuel' (remove_one m l))
      end
  end.
 
(** Definição final de ss *)
Definition ss (l: list nat) : list nat :=
  ss_aux (length l) l.
 

Theorem selectionsort_correct: forall l, Sorted le (ss l) /\ Permutation l (ss l).
Proof.
  intros l.
  remember (length l) as n eqn:Heqn.
  revert l Heqn.
  induction n as [n IHn] using lt_wf_ind.
  intros l Heqn.
  unfold ss.
  destruct l as [| h tl].
  - split; constructor.
  - remember (select_min (h :: tl)) as res eqn:Hmin.
    destruct res as [n0 |].
    + symmetry in Hmin.
      simpl. rewrite Hmin.
      assert (Hperm_len : Permutation (h :: tl) (n0 :: remove_one n0 (h :: tl))).
      { apply perm_add_one. apply select_min_in. exact Hmin. }
      apply Permutation_length in Hperm_len.
      simpl in Hperm_len. injection Hperm_len as Hfuel.
      rewrite Hfuel.
      change (if n0 =? h then tl else h :: remove_one n0 tl) with (remove_one n0 (h :: tl)).
      change (ss_aux (length (remove_one n0 (h :: tl))) (remove_one n0 (h :: tl)))
        with (ss (remove_one n0 (h :: tl))).
      split.
      * apply Sorted_cons.
        { assert (Hlen : length (remove_one n0 (h::tl)) < n).
          { rewrite Heqn. apply remove_one_length. apply select_min_in. exact Hmin. }
          apply (proj1 (IHn _ Hlen _ eq_refl)). }
        { assert (Hlen : length (remove_one n0 (h::tl)) < n).
          { rewrite Heqn. apply remove_one_length. apply select_min_in. exact Hmin. }
          pose proof (IHn _ Hlen _ eq_refl) as [_ Hperm_rest].
          destruct (ss (remove_one n0 (h::tl))) as [| b l'] eqn:Hss.
          - apply HdRel_nil.
          - apply HdRel_cons.
            pose proof (select_min_correct _ _ Hmin) as Hmin_le.
            apply Hmin_le.
            assert (Hperm_full: Permutation (h :: tl) (n0 :: remove_one n0 (h :: tl))).
            { apply perm_add_one. apply select_min_in. exact Hmin. }
            apply Permutation_in with (l := n0 :: remove_one n0 (h :: tl)).
            + symmetry. exact Hperm_full.
            + right. apply Permutation_in with (l := b :: l').
              * symmetry. exact Hperm_rest.
              * simpl. left. reflexivity. }
      * assert (Hperm: Permutation (h :: tl) (n0 :: remove_one n0 (h :: tl))).
        { apply perm_add_one. apply select_min_in. exact Hmin. }
        apply Permutation_trans with (n0 :: remove_one n0 (h :: tl)).
        -- exact Hperm.
        -- apply perm_skip.
           assert (Hlen : length (remove_one n0 (h::tl)) < n).
           { rewrite Heqn. apply remove_one_length. apply select_min_in. exact Hmin. }
           apply (proj2 (IHn _ Hlen _ eq_refl)).
   + (* Caso o mínimo não existe (None) *)
      exfalso.
      clear Heqn IHn n. 
      revert h Hmin.
      induction tl as [| h2 tl' IH]; intros h Hmin.
      * (* Base: tl = nil *)
        change (select_min (h :: nil)) with (Some h) in Hmin.
        discriminate Hmin.
      * (* Passo indutivo: tl = h2 :: tl' *)
        destruct (h <=? h2) eqn:Heq.
        -- (* Caso h <= h2 *)
           (* Usamos o lema de redução da função (gerado automaticamente) *)
           rewrite select_min_equation in Hmin.
           simpl in Hmin.
           rewrite Heq in Hmin.
           eapply IH. exact Hmin.
        -- (* Caso h > h2 *)
           rewrite select_min_equation in Hmin.
           simpl in Hmin.
           rewrite Heq in Hmin.
           eapply IH. exact Hmin.
Qed.
(** Repositório: %\url{https://github.com/flaviodemoura/selection_sort}% *)