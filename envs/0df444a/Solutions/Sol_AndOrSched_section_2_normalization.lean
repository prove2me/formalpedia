-- Prove2me | solution 1 for AndOrSched.section_2_normalization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:48:36.745685+00:00
-- url     : https://prove2.me/submissions/23e9b655-82d2-438c-9a1f-01caa17196a4

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_scaleD
import Definitions.Def_AndOrSched_normalize
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_outSched
import Definitions.Def_AndOrSched_zeroSet
import Definitions.Def_AndOrSched_toNorm
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_andRel
import Definitions.Def_AndOrSched_HasPred
open scoped Classical NNReal

namespace Aux_AOS_norm

open AndOrSched

/-! ### The zero set -/

def Closed (I : Instance) (S : Set I.N) : Prop :=
  ∀ k : I.N, I.p k = 0 → (∀ i, andRel I i k → i ∈ S) →
    ((∃ a, k = Sum.inl a) ∨
      ∃ b, k = Sum.inr b ∧ (orPred I b = ∅ ∨ ∃ a ∈ orPred I b, Sum.inl a ∈ S)) → k ∈ S

theorem mem_Z (I : Instance) (j : I.N) : j ∈ zeroSet I ↔ ∀ S, Closed I S → j ∈ S := Iff.rfl

theorem Z_closed (I : Instance) : Closed I (zeroSet I) := by
  intro k hp hand hor
  rw [mem_Z]
  intro S hS
  apply hS k hp (fun i hi => (mem_Z I i).mp (hand i hi) S hS)
  rcases hor with h | ⟨b, hb, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨b, hb, ?_⟩
    rcases h with h | ⟨a, ha, haZ⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, (mem_Z I _).mp haZ S hS⟩

theorem Z_inv (I : Instance) (j : I.N) (hj : j ∈ zeroSet I) :
    I.p j = 0 ∧ (∀ i, andRel I i j → i ∈ zeroSet I) ∧
      ((∃ a, j = Sum.inl a) ∨ ∃ b, j = Sum.inr b ∧
        (orPred I b = ∅ ∨ ∃ a ∈ orPred I b, Sum.inl a ∈ zeroSet I)) := by
  let S' : Set I.N := {k | k ∈ zeroSet I ∧ I.p k = 0 ∧ (∀ i, andRel I i k → i ∈ zeroSet I) ∧
      ((∃ a, k = Sum.inl a) ∨ ∃ b, k = Sum.inr b ∧
        (orPred I b = ∅ ∨ ∃ a ∈ orPred I b, Sum.inl a ∈ zeroSet I))}
  have hS' : Closed I S' := by
    intro k hp hand hor
    have hand' : ∀ i, andRel I i k → i ∈ zeroSet I := by
      intro i hi
      obtain ⟨h1, -⟩ := hand i hi
      exact h1
    have hor' : (∃ a, k = Sum.inl a) ∨ ∃ b, k = Sum.inr b ∧
        (orPred I b = ∅ ∨ ∃ a ∈ orPred I b, Sum.inl a ∈ zeroSet I) := by
      rcases hor with h | ⟨b, hb, h⟩
      · exact Or.inl h
      · refine Or.inr ⟨b, hb, ?_⟩
        rcases h with h | ⟨a, ha, haS⟩
        · exact Or.inl h
        · obtain ⟨h1, -⟩ := haS
          exact Or.inr ⟨a, ha, h1⟩
    show k ∈ zeroSet I ∧ I.p k = 0 ∧ (∀ i, andRel I i k → i ∈ zeroSet I) ∧ _
    exact ⟨Z_closed I k hp hand' hor', hp, hand', hor'⟩
  obtain ⟨-, h⟩ := (mem_Z I j).mp hj S' hS'
  exact h

theorem pZ (I : Instance) (j : I.N) (hj : j ∈ zeroSet I) : I.p j = 0 := (Z_inv I j hj).1

theorem pZR (I : Instance) (j : I.N) (hj : j ∈ zeroSet I) : ((I.p j : ℚ≥0) : ℝ) = 0 := by
  rw [pZ I j hj]; simp

/-! ### Non-redundant predecessors -/

theorem exists_nonred (I : Instance) (hI : Acyclic I) (b : I.B) (a : I.A)
    (ha : a ∈ orPred I b) :
    ∃ a' ∈ nonRedPred I b, a' = a ∨ Relation.TransGen I.andA a' a := by
  haveI : IsTrans I.A (Relation.TransGen I.andA) := ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
  haveI : Std.Irrefl (Relation.TransGen I.andA) := ⟨hI.1⟩
  have hwf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen I.andA)
  refine hwf.induction (C := fun a => a ∈ orPred I b →
    ∃ a' ∈ nonRedPred I b, a' = a ∨ Relation.TransGen I.andA a' a) a ?_ ha
  intro a ih ha
  by_cases hnr : a ∈ nonRedPred I b
  · exact ⟨a, hnr, Or.inl rfl⟩
  · have hex : ∃ a' ∈ orPred I b, a' ≠ a ∧ Relation.TransGen I.andA a' a := by
      by_contra hcon
      apply hnr
      unfold nonRedPred
      rw [Finset.mem_filter]
      exact ⟨ha, hcon⟩
    obtain ⟨a', ha', _, htg⟩ := hex
    obtain ⟨a'', h1, h2⟩ := ih a' htg ha'
    refine ⟨a'', h1, Or.inr ?_⟩
    rcases h2 with rfl | h2
    · exact htg
    · exact h2.trans htg

theorem nonred_sub (I : Instance) (b : I.B) (a : I.A) (ha : a ∈ nonRedPred I b) :
    a ∈ orPred I b := by
  unfold nonRedPred at ha
  exact (Finset.mem_filter.mp ha).1

theorem orPred_ne (I : Instance) (b : I.B) (h : orPred I b ≠ ∅) : ∃ a, a ∈ orPred I b := by
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr h
  exact ⟨a, ha⟩

theorem tg_le (I : Instance) (C : I.N → ℝ) (hC : IsFeasible I C) {u v : I.A}
    (h : Relation.TransGen I.andA u v) : C (Sum.inl u) ≤ C (Sum.inl v) := by
  induction h with
  | @single v' h =>
    have h1 := hC.2.2.1 (Sum.inl u) (Sum.inl v') h
    have h2 : (0 : ℝ) ≤ ((I.p (Sum.inl v') : ℚ≥0) : ℝ) := by positivity
    linarith
  | @tail m v' _ h ih =>
    have h1 := hC.2.2.1 (Sum.inl m) (Sum.inl v') h
    have h2 : (0 : ℝ) ≤ ((I.p (Sum.inl v') : ℚ≥0) : ℝ) := by positivity
    linarith

/-! ### The scaling factor -/

theorem D_pos (I : Instance) : 0 < scaleD I := by
  unfold scaleD
  apply Nat.pos_of_ne_zero
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨j, _, hj⟩ := h
  exact (I.p j).den_ne_zero hj

theorem floor_scale (I : Instance) (j : I.N) :
    ((Nat.floor (I.p j * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0) = I.p j * (scaleD I : ℚ≥0) := by
  obtain ⟨k, hk⟩ : (I.p j).den ∣ scaleD I := Finset.dvd_lcm (Finset.mem_univ j)
  have e : I.p j * (scaleD I : ℚ≥0) = (((I.p j).num * k : ℕ) : ℚ≥0) := by
    rw [hk]
    push_cast
    rw [← mul_assoc, NNRat.mul_den_eq_num]
  rw [e, Nat.floor_natCast]

theorem pnorm_real (I : Instance) (j : I.N) :
    ((((Nat.floor (I.p j * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0)) : ℝ) =
      ((I.p j : ℚ≥0) : ℝ) * (scaleD I : ℝ) := by
  rw [floor_scale, NNRat.cast_mul, NNRat.cast_natCast]

theorem one_le_scaled (I : Instance) (j : I.N) (h : I.p j ≠ 0) :
    (1 : ℚ≥0) ≤ ((Nat.floor (I.p j * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0) := by
  rw [Nat.one_le_cast]
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  have e := floor_scale I j
  rw [h0, Nat.cast_zero] at e
  rcases mul_eq_zero.mp e.symm with h1 | h1
  · exact h h1
  · have := D_pos I
    have h2 : scaleD I = 0 := by exact_mod_cast h1
    omega

/-! ### The normalized instance -/

abbrev AZ (I : Instance) : Type := {a : I.A // Sum.inl a ∉ zeroSet I}
abbrev BZ (I : Instance) : Type := {b : I.B // Sum.inr b ∉ zeroSet I}

theorem pA (I : Instance) (a : I.A) (ha : Sum.inl a ∉ zeroSet I) :
    ((((AndOrSched.normalize I).p (Sum.inl (⟨a, ha⟩ : AZ I))) : ℚ≥0) : ℝ) =
      ((I.p (Sum.inl a) : ℚ≥0) : ℝ) * (scaleD I : ℝ) :=
  pnorm_real I (Sum.inl a)

theorem pB (I : Instance) (b : I.B) (hb : Sum.inr b ∉ zeroSet I) :
    ((((AndOrSched.normalize I).p (Sum.inr (Sum.inl (⟨b, hb⟩ : BZ I)))) : ℚ≥0) : ℝ) =
      ((I.p (Sum.inr b) : ℚ≥0) : ℝ) * (scaleD I : ℝ) :=
  pnorm_real I (Sum.inr b)

theorem pDm (I : Instance) (d : I.A) (hd : Sum.inl d ∉ zeroSet I) :
    ((((AndOrSched.normalize I).p (Sum.inr (Sum.inr (⟨d, hd⟩ : AZ I)))) : ℚ≥0) : ℝ) = 0 := by
  show (((0 : ℚ≥0)) : ℝ) = 0
  simp

theorem mem_orPredB (I : Instance) (b : I.B) (hb : Sum.inr b ∉ zeroSet I) (a : I.A)
    (ha : Sum.inl a ∉ zeroSet I) :
    (⟨a, ha⟩ : AZ I) ∈ orPred (AndOrSched.normalize I) (Sum.inl (⟨b, hb⟩ : BZ I)) ↔
      a ∈ nonRedPred I b ∧ ¬ ∃ a' ∈ orPred I b, Sum.inl a' ∈ zeroSet I :=
  ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr
    ⟨@Finset.mem_univ (AndOrSched.normalize I).A _ (⟨a, ha⟩ : AZ I), h⟩⟩

theorem mem_orPredD (I : Instance) (d : I.A) (hd : Sum.inl d ∉ zeroSet I) (a : I.A)
    (ha : Sum.inl a ∉ zeroSet I) :
    (⟨a, ha⟩ : AZ I) ∈ orPred (AndOrSched.normalize I) (Sum.inr (⟨d, hd⟩ : AZ I)) ↔ a = d := by
  constructor
  · intro h
    have h2 : (⟨a, ha⟩ : AZ I) = ⟨d, hd⟩ := (Finset.mem_filter.mp h).2
    exact congrArg Subtype.val h2
  · intro h
    exact Finset.mem_filter.mpr ⟨@Finset.mem_univ (AndOrSched.normalize I).A _ (⟨a, ha⟩ : AZ I),
      (Subtype.ext h : (⟨a, ha⟩ : AZ I) = ⟨d, hd⟩)⟩

noncomputable def orig (I : Instance) : (AndOrSched.normalize I).N → I.N :=
  @Sum.elim (AZ I) (BZ I ⊕ AZ I) I.N (fun a => Sum.inl a.1)
    (Sum.elim (fun b => Sum.inr b.1) (fun d => Sum.inl d.1))

theorem tg_norm (I : Instance) {a a' : (AndOrSched.normalize I).A}
    (h : Relation.TransGen (AndOrSched.normalize I).andA a a') :
    Relation.TransGen I.andA (Subtype.val (p := fun a => Sum.inl a ∉ zeroSet I) a)
      (Subtype.val (p := fun a => Sum.inl a ∉ zeroSet I) a') := by
  induction h with
  | single h => exact Relation.TransGen.single h
  | tail _ h ih => exact ih.tail h

theorem tg_normB (I : Instance) {y z : (AndOrSched.normalize I).B}
    (h : Relation.TransGen (AndOrSched.normalize I).andB y z) :
    ∃ b c : BZ I, y = Sum.inl b ∧ z = Sum.inl c ∧ Relation.TransGen I.andB b.1 c.1 := by
  induction h with
  | @single z' h =>
    rcases y with b | d
    · rcases z' with c | e
      · exact ⟨b, c, rfl, rfl, Relation.TransGen.single h⟩
      · exact (h : False).elim
    · exact (h : False).elim
  | @tail m z' _ h ih =>
    obtain ⟨b, c, hy, hm, htg⟩ := ih
    subst hm
    rcases z' with c' | e
    · exact ⟨b, c', hy, rfl, htg.tail h⟩
    · exact (h : False).elim

end Aux_AOS_norm

namespace Aux_AOS_norm

open AndOrSched

theorem acyclic_norm (I : Instance) (hI : Acyclic I) : Acyclic (AndOrSched.normalize I) := by
  refine ⟨fun a h => hI.1 _ (tg_norm I h), fun y h => ?_⟩
  obtain ⟨b, c, hy, hz, htg⟩ := tg_normB I h
  subst hy
  have : b = c := Sum.inl_injective hz
  subst this
  exact hI.2 _ htg

theorem norm_isNormalized (I : Instance) (hI : Acyclic I) :
    IsNormalized (AndOrSched.normalize I) := by
  refine ⟨fun a => rfl, ?_, ?_, ?_⟩
  · intro j
    rcases j with a | b | d
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨0, by show (0 : ℚ≥0) = ((0 : ℕ) : ℚ≥0); simp⟩
  · intro j hj
    unfold HasPred at hj
    push_neg at hj
    obtain ⟨hj1, hj2⟩ := hj
    rcases j with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩
    · -- an A-job
      show (1 : ℚ≥0) ≤ ((Nat.floor (I.p (Sum.inl a) * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0)
      apply one_le_scaled
      intro hp0
      apply ha
      apply Z_closed I _ hp0
      · intro i hi
        rcases i with a'' | b''
        · by_contra hz
          exact hj1 (Sum.inl (⟨a'', hz⟩ : AZ I)) hi
        · exact (hi : False).elim
      · exact Or.inl ⟨a, rfl⟩
    · -- a B-job
      show (1 : ℚ≥0) ≤ ((Nat.floor (I.p (Sum.inr b) * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0)
      apply one_le_scaled
      intro hp0
      apply hb
      apply Z_closed I _ hp0
      · intro i hi
        rcases i with a'' | b''
        · exact (hi : False).elim
        · by_contra hz
          exact hj1 (Sum.inr (Sum.inl (⟨b'', hz⟩ : BZ I))) hi
      · refine Or.inr ⟨b, rfl, ?_⟩
        by_cases h1 : ∃ a ∈ orPred I b, Sum.inl a ∈ zeroSet I
        · exact Or.inr h1
        · by_cases h2 : orPred I b = ∅
          · exact Or.inl h2
          · exfalso
            obtain ⟨a, ha⟩ := orPred_ne I b h2
            obtain ⟨a', ha', -⟩ := exists_nonred I hI b a ha
            have ha'Z : Sum.inl a' ∉ zeroSet I := fun hz => h1 ⟨a', nonred_sub I b a' ha', hz⟩
            have hmem := (mem_orPredB I b hb a' ha'Z).mpr ⟨ha', h1⟩
            have := hj2 (Sum.inl (⟨b, hb⟩ : BZ I)) rfl
            rw [this] at hmem
            exact Finset.notMem_empty _ hmem
    · -- a dummy
      exfalso
      have := hj2 (Sum.inr (⟨d, hd⟩ : AZ I)) rfl
      have hmem := (mem_orPredD I d hd d hd).mpr rfl
      rw [this] at hmem
      exact Finset.notMem_empty _ hmem
  · intro y
    unfold nonRedPred
    apply Finset.filter_true_of_mem
    intro a ha
    rintro ⟨a', ha', hne, htg⟩
    rcases y with ⟨b, hb⟩ | ⟨d, hd⟩
    · obtain ⟨a0, ha0⟩ := a
      obtain ⟨a1, ha1⟩ := a'
      have h0 := (mem_orPredB I b hb a0 ha0).mp ha
      have h1 := (mem_orPredB I b hb a1 ha1).mp ha'
      have htg' := tg_norm I htg
      have hne' : a1 ≠ a0 := fun h => hne (by subst h; rfl)
      have h0' := h0.1
      unfold nonRedPred at h0'
      rw [Finset.mem_filter] at h0'
      exact h0'.2 ⟨a1, nonred_sub I b a1 h1.1, hne', htg'⟩
    · obtain ⟨a0, ha0⟩ := a
      obtain ⟨a1, ha1⟩ := a'
      have h0 := (mem_orPredD I d hd a0 ha0).mp ha
      have h1 := (mem_orPredD I d hd a1 ha1).mp ha'
      subst h0
      subst h1
      exact hne rfl

theorem delta_norm (I : Instance) : delta (AndOrSched.normalize I) ≤ delta I := by
  unfold delta
  apply max_le (le_max_left _ _)
  apply Finset.sup_le
  intro y _
  have hsub : (nonRedPred (AndOrSched.normalize I) y).card ≤
      (orPred (AndOrSched.normalize I) y).card := by
    apply Finset.card_le_card
    unfold nonRedPred
    exact Finset.filter_subset _ _
  rcases y with ⟨b, hb⟩ | ⟨d, hd⟩
  · have h2 : (orPred (AndOrSched.normalize I) (Sum.inl (⟨b, hb⟩ : BZ I))).card ≤
        (nonRedPred I b).card := by
      apply Finset.card_le_card_of_injOn (fun a => Subtype.val (p := fun a => Sum.inl a ∉ zeroSet I) a)
      · intro a ha
        obtain ⟨a0, ha0⟩ := a
        exact ((mem_orPredB I b hb a0 ha0).mp ha).1
      · intro a _ a' _ h
        exact Subtype.ext h
    have h3 : (nonRedPred I b).card ≤ Finset.univ.sup fun b => (nonRedPred I b).card :=
      Finset.le_sup (f := fun b => (nonRedPred I b).card) (Finset.mem_univ b)
    have h4 := le_max_right 1 (Finset.univ.sup fun b => (nonRedPred I b).card)
    omega
  · have h2 : (orPred (AndOrSched.normalize I) (Sum.inr (⟨d, hd⟩ : AZ I))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha a' ha'
      obtain ⟨a0, ha0⟩ := a
      obtain ⟨a1, ha1⟩ := a'
      have h0 := (mem_orPredD I d hd a0 ha0).mp ha
      have h1 := (mem_orPredD I d hd a1 ha1).mp ha'
      subst h0
      subst h1
      rfl
    have h4 := le_max_left 1 (Finset.univ.sup fun b => (nonRedPred I b).card)
    omega

theorem card_norm (I : Instance) :
    Fintype.card (AndOrSched.normalize I).N ≤ 2 * Fintype.card I.N := by
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  show Nat.card (AZ I ⊕ (BZ I ⊕ AZ I)) ≤ 2 * Nat.card (I.A ⊕ I.B)
  rw [Nat.card_sum, Nat.card_sum, Nat.card_sum]
  have h1 : Nat.card (AZ I) ≤ Nat.card I.A := Finite.card_subtype_le _
  have h2 : Nat.card (BZ I) ≤ Nat.card I.B := Finite.card_subtype_le _
  omega

theorem p01_norm (I : Instance) (h : ∀ j, I.p j = 0 ∨ I.p j = 1) :
    ∀ j, (AndOrSched.normalize I).p j = 0 ∨ (AndOrSched.normalize I).p j = 1 := by
  have hD : scaleD I = 1 := by
    apply Nat.dvd_one.mp
    unfold scaleD
    apply Finset.lcm_dvd
    intro j _
    rcases h j with h1 | h1 <;> rw [h1] <;> simp
  intro j
  rcases j with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩
  · show ((Nat.floor (I.p (Sum.inl a) * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0) = 0 ∨
      ((Nat.floor (I.p (Sum.inl a) * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0) = 1
    rw [floor_scale, hD, Nat.cast_one, mul_one]
    exact h _
  · show ((Nat.floor (I.p (Sum.inr b) * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0) = 0 ∨
      ((Nat.floor (I.p (Sum.inr b) * (scaleD I : ℚ≥0)) : ℕ) : ℚ≥0) = 1
    rw [floor_scale, hD, Nat.cast_one, mul_one]
    exact h _
  · exact Or.inl rfl

end Aux_AOS_norm

namespace Aux_AOS_norm

open AndOrSched

theorem orig_inl (I : Instance) (a : I.A) (ha : Sum.inl a ∉ zeroSet I) :
    orig I (Sum.inl (⟨a, ha⟩ : AZ I)) = Sum.inl a := rfl
theorem orig_B (I : Instance) (b : I.B) (hb : Sum.inr b ∉ zeroSet I) :
    orig I (Sum.inr (Sum.inl (⟨b, hb⟩ : BZ I))) = Sum.inr b := rfl
theorem orig_D (I : Instance) (d : I.A) (hd : Sum.inl d ∉ zeroSet I) :
    orig I (Sum.inr (Sum.inr (⟨d, hd⟩ : AZ I))) = Sum.inl d := rfl

theorem p'_le (I : Instance) (j' : (AndOrSched.normalize I).N) :
    ((((AndOrSched.normalize I).p j') : ℚ≥0) : ℝ) ≤
      (scaleD I : ℝ) * ((I.p (orig I j') : ℚ≥0) : ℝ) := by
  have hD : (0 : ℝ) < scaleD I := by exact_mod_cast D_pos I
  rcases j' with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩
  · have e := pA I a ha
    have e2 := orig_inl I a ha
    rw [e, e2]
    linarith
  · have e := pB I b hb
    have e2 := orig_B I b hb
    rw [e, e2]
    linarith
  · have e := pDm I d hd
    rw [e]
    exact mul_nonneg hD.le (by positivity)

theorem orig_eq (I : Instance) (i j : (AndOrSched.normalize I).N) (h : orig I i = orig I j)
    (hij : i ≠ j) :
    ((((AndOrSched.normalize I).p i) : ℚ≥0) : ℝ) = 0 ∨
      ((((AndOrSched.normalize I).p j) : ℚ≥0) : ℝ) = 0 := by
  rcases i with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩ <;> rcases j with ⟨a', ha'⟩ | ⟨b', hb'⟩ | ⟨d', hd'⟩
  · have h' : (Sum.inl a : I.N) = Sum.inl a' := h
    have := Sum.inl_injective h'
    subst this
    exact absurd rfl hij
  · have h' : (Sum.inl a : I.N) = Sum.inr b' := h
    exact absurd h' Sum.inl_ne_inr
  · exact Or.inr (pDm I d' hd')
  · have h' : (Sum.inr b : I.N) = Sum.inl a' := h
    exact absurd h' Sum.inr_ne_inl
  · have h' : (Sum.inr b : I.N) = Sum.inr b' := h
    have := Sum.inr_injective h'
    subst this
    exact absurd rfl hij
  · have h' : (Sum.inr b : I.N) = Sum.inl d' := h
    exact absurd h' Sum.inr_ne_inl
  · exact Or.inl (pDm I d hd)
  · have h' : (Sum.inl d : I.N) = Sum.inr b' := h
    exact absurd h' Sum.inl_ne_inr
  · have h' : (Sum.inl d : I.N) = Sum.inl d' := h
    have := Sum.inl_injective h'
    subst this
    exact absurd rfl hij

theorem orig_injOn (I : Instance) : Set.InjOn (orig I)
    ((Finset.univ.filter (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a)) :
      Set (AndOrSched.normalize I).N) := by
  intro i hi j hj h
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  rcases i with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩
  · exact absurd ⟨_, rfl⟩ hi'
  all_goals rcases j with ⟨a', ha'⟩ | ⟨b', hb'⟩ | ⟨d', hd'⟩
  all_goals first
    | exact absurd ⟨_, rfl⟩ hj'
    | skip
  · have h' : (Sum.inr b : I.N) = Sum.inr b' := h
    have := Sum.inr_injective h'
    subst this
    rfl
  · have h' : (Sum.inr b : I.N) = Sum.inl d' := h
    exact absurd h' Sum.inr_ne_inl
  · have h' : (Sum.inl d : I.N) = Sum.inr b' := h
    exact absurd h' Sum.inl_ne_inr
  · have h' : (Sum.inl d : I.N) = Sum.inl d' := h
    have := Sum.inl_injective h'
    subst this
    rfl

theorem forward (I : Instance) (hI : Acyclic I) (C : I.N → ℝ) (hC : IsFeasible I C) :
    ∃ C' : (AndOrSched.normalize I).N → ℝ, IsFeasible (AndOrSched.normalize I) C' ∧
      cost (AndOrSched.normalize I) C' ≤ (scaleD I : ℝ) * cost I C := by
  have hD : (0 : ℝ) < scaleD I := by exact_mod_cast D_pos I
  have hpnn : ∀ j : I.N, (0 : ℝ) ≤ ((I.p j : ℚ≥0) : ℝ) := fun j => by positivity
  have hCnn : ∀ j, 0 ≤ C j := fun j => le_trans (hpnn j) (hC.1 j)
  refine ⟨fun j' => (scaleD I : ℝ) * C (orig I j'), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- release
    intro j'
    have h1 := p'_le I j'
    have h2 := mul_le_mul_of_nonneg_left (hC.1 (orig I j')) hD.le
    show _ ≤ (scaleD I : ℝ) * C (orig I j')
    linarith
  · -- disjointness
    intro i j hij
    show (scaleD I : ℝ) * C (orig I i) ≤ (scaleD I : ℝ) * C (orig I j) - _ ∨
      (scaleD I : ℝ) * C (orig I j) ≤ (scaleD I : ℝ) * C (orig I i) - _
    by_cases ho : orig I i = orig I j
    · rw [ho]
      rcases orig_eq I i j ho hij with h | h
      · right; rw [h]; linarith
      · left; rw [h]; linarith
    · have hi := p'_le I i
      have hj := p'_le I j
      rcases hC.2.1 (orig I i) (orig I j) ho with h | h
      · left
        have := mul_le_mul_of_nonneg_left h hD.le
        linarith
      · right
        have := mul_le_mul_of_nonneg_left h hD.le
        linarith
  · -- AND precedences
    intro i j hij
    rcases i with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩ <;> rcases j with ⟨a', ha'⟩ | ⟨b', hb'⟩ | ⟨d', hd'⟩
    · have h1 : I.andA a a' := hij
      have h2 := hC.2.2.1 (Sum.inl a) (Sum.inl a') h1
      have e := pA I a' ha'
      show (scaleD I : ℝ) * C (Sum.inl a) + _ ≤ (scaleD I : ℝ) * C (Sum.inl a')
      rw [e]
      have := mul_le_mul_of_nonneg_left h2 hD.le
      linarith
    all_goals first
      | exact (hij : False).elim
      | skip
    · have h1 : I.andB b b' := hij
      have h2 := hC.2.2.1 (Sum.inr b) (Sum.inr b') h1
      have e := pB I b' hb'
      show (scaleD I : ℝ) * C (Sum.inr b) + _ ≤ (scaleD I : ℝ) * C (Sum.inr b')
      rw [e]
      have := mul_le_mul_of_nonneg_left h2 hD.le
      linarith
  · -- OR precedences
    intro y hy
    rcases y with ⟨b, hb⟩ | ⟨d, hd⟩
    · obtain ⟨⟨a0, ha0⟩, ha0m⟩ := hy
      obtain ⟨ha0nr, hnoZ⟩ := (mem_orPredB I b hb a0 ha0).mp ha0m
      have hne : (orPred I b).Nonempty := ⟨a0, nonred_sub I b a0 ha0nr⟩
      obtain ⟨a, ha, hCa⟩ := hC.2.2.2 b hne
      obtain ⟨a', ha'nr, ha'⟩ := exists_nonred I hI b a ha
      have ha'Z : Sum.inl a' ∉ zeroSet I := fun hz => hnoZ ⟨a', nonred_sub I b a' ha'nr, hz⟩
      refine ⟨(⟨a', ha'Z⟩ : AZ I), (mem_orPredB I b hb a' ha'Z).mpr ⟨ha'nr, hnoZ⟩, ?_⟩
      have hle : C (Sum.inl a') ≤ C (Sum.inl a) := by
        rcases ha' with rfl | htg
        · exact le_rfl
        · exact tg_le I C hC htg
      have e := pB I b hb
      show (scaleD I : ℝ) * C (Sum.inl a') + _ ≤ (scaleD I : ℝ) * C (Sum.inr b)
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left hle hD.le
      have h2 := mul_le_mul_of_nonneg_left hCa hD.le
      linarith
    · refine ⟨(⟨d, hd⟩ : AZ I), (mem_orPredD I d hd d hd).mpr rfl, ?_⟩
      have e := pDm I d hd
      show (scaleD I : ℝ) * C (Sum.inl d) + _ ≤ (scaleD I : ℝ) * C (Sum.inl d)
      rw [e]
      linarith
  · -- cost
    unfold cost
    show ∑ j', ((AndOrSched.normalize I).w j' : ℝ) * ((scaleD I : ℝ) * C (orig I j')) ≤
      (scaleD I : ℝ) * ∑ j, (I.w j : ℝ) * C j
    have hzero : ∀ j' ∈ Finset.univ.filter
        (fun j' : (AndOrSched.normalize I).N => ∃ a, j' = Sum.inl a),
        ((AndOrSched.normalize I).w j' : ℝ) * ((scaleD I : ℝ) * C (orig I j')) = 0 := by
      intro j' hj'
      obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hj').2
      show ((0 : ℝ≥0) : ℝ) * _ = 0
      simp
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j' : (AndOrSched.normalize I).N => ∃ a, j' = Sum.inl a),
      Finset.sum_eq_zero hzero, zero_add]
    have hval : ∀ j' ∈ Finset.univ.filter
        (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a),
        ((AndOrSched.normalize I).w j' : ℝ) * ((scaleD I : ℝ) * C (orig I j')) =
        (I.w (orig I j') : ℝ) * ((scaleD I : ℝ) * C (orig I j')) := by
      intro j' hj'
      have hj'' := (Finset.mem_filter.mp hj').2
      rcases j' with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩
      · exact absurd ⟨_, rfl⟩ hj''
      · rfl
      · rfl
    calc ∑ j' ∈ Finset.univ.filter
          (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a),
          ((AndOrSched.normalize I).w j' : ℝ) * ((scaleD I : ℝ) * C (orig I j'))
        = ∑ j' ∈ Finset.univ.filter
          (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a),
          (I.w (orig I j') : ℝ) * ((scaleD I : ℝ) * C (orig I j')) := Finset.sum_congr rfl hval
      _ = ∑ x ∈ (Finset.univ.filter
          (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a)).image (orig I),
          (I.w x : ℝ) * ((scaleD I : ℝ) * C x) := (Finset.sum_image (f := fun x : I.N => (I.w x : ℝ) * ((scaleD I : ℝ) * C x)) (orig_injOn I)).symm
      _ ≤ ∑ x, (I.w x : ℝ) * ((scaleD I : ℝ) * C x) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => mul_nonneg (by positivity) (mul_nonneg hD.le (hCnn x)))
      _ = (scaleD I : ℝ) * ∑ x, (I.w x : ℝ) * C x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

end Aux_AOS_norm

namespace Aux_AOS_norm

open AndOrSched

theorem toNorm_Z (I : Instance) (j : I.N) (hj : j ∈ zeroSet I) : toNorm I j = none := by
  rcases j with a | b
  · show (if h : Sum.inl a ∈ zeroSet I then none else
      some (Sum.inl (⟨a, h⟩ : {a : I.A // Sum.inl a ∉ zeroSet I}))) = none
    rw [dif_pos hj]
  · show (if h : Sum.inr b ∈ zeroSet I then none else
      some (Sum.inr (Sum.inl (⟨b, h⟩ : {b : I.B // Sum.inr b ∉ zeroSet I})))) = none
    rw [dif_pos hj]

theorem toNorm_A (I : Instance) (a : I.A) (h : Sum.inl a ∉ zeroSet I) :
    toNorm I (Sum.inl a) = some (Sum.inl (⟨a, h⟩ : AZ I)) := by
  show (if h : Sum.inl a ∈ zeroSet I then none else
      some (Sum.inl (⟨a, h⟩ : {a : I.A // Sum.inl a ∉ zeroSet I}))) = _
  rw [dif_neg h]

theorem toNorm_B (I : Instance) (b : I.B) (h : Sum.inr b ∉ zeroSet I) :
    toNorm I (Sum.inr b) = some (Sum.inr (Sum.inl (⟨b, h⟩ : BZ I))) := by
  show (if h : Sum.inr b ∈ zeroSet I then none else
      some (Sum.inr (Sum.inl (⟨b, h⟩ : {b : I.B // Sum.inr b ∉ zeroSet I})))) = _
  rw [dif_neg h]

theorem out_Z (I : Instance)
    (σ : (AndOrSched.normalize I).N ≃ Fin (Fintype.card (AndOrSched.normalize I).N))
    (j : I.N) (hj : j ∈ zeroSet I) : outSched I σ j = 0 := by
  simp only [outSched, toNorm_Z I j hj]

theorem out_A (I : Instance)
    (σ : (AndOrSched.normalize I).N ≃ Fin (Fintype.card (AndOrSched.normalize I).N))
    (a : I.A) (h : Sum.inl a ∉ zeroSet I) :
    outSched I σ (Sum.inl a) =
      listC (AndOrSched.normalize I) σ (Sum.inl (⟨a, h⟩ : AZ I)) / (scaleD I : ℝ) := by
  simp only [outSched, toNorm_A I a h]
  rfl

theorem out_B (I : Instance)
    (σ : (AndOrSched.normalize I).N ≃ Fin (Fintype.card (AndOrSched.normalize I).N))
    (b : I.B) (h : Sum.inr b ∉ zeroSet I) :
    outSched I σ (Sum.inr b) =
      listC (AndOrSched.normalize I) σ (Sum.inr (Sum.inl (⟨b, h⟩ : BZ I))) / (scaleD I : ℝ) := by
  simp only [outSched, toNorm_B I b h]
  rfl

theorem backward (I : Instance) (hI : Acyclic I)
    (σ : (AndOrSched.normalize I).N ≃ Fin (Fintype.card (AndOrSched.normalize I).N))
    (hF : IsFeasible (AndOrSched.normalize I) (listC (AndOrSched.normalize I) σ)) :
    IsFeasible I (outSched I σ) ∧
      cost I (outSched I σ) ≤
        cost (AndOrSched.normalize I) (listC (AndOrSched.normalize I) σ) / (scaleD I : ℝ) := by
  have hD : (0 : ℝ) < scaleD I := by exact_mod_cast D_pos I
  have hDne : (scaleD I : ℝ) ≠ 0 := hD.ne'
  have hpnn : ∀ j : I.N, (0 : ℝ) ≤ ((I.p j : ℚ≥0) : ℝ) := fun j => by positivity
  have hLnn : ∀ j', 0 ≤ listC (AndOrSched.normalize I) σ j' := fun j' =>
    Finset.sum_nonneg (fun i _ => by positivity)
  -- the scaled values
  have hmulA : ∀ a (h : Sum.inl a ∉ zeroSet I), outSched I σ (Sum.inl a) * (scaleD I : ℝ) =
      listC (AndOrSched.normalize I) σ (Sum.inl (⟨a, h⟩ : AZ I)) := by
    intro a h
    rw [out_A I σ a h]
    exact div_mul_cancel₀ _ hDne
  have hmulB : ∀ b (h : Sum.inr b ∉ zeroSet I), outSched I σ (Sum.inr b) * (scaleD I : ℝ) =
      listC (AndOrSched.normalize I) σ (Sum.inr (Sum.inl (⟨b, h⟩ : BZ I))) := by
    intro b h
    rw [out_B I σ b h]
    exact div_mul_cancel₀ _ hDne
  -- release dates
  have hrel : ∀ j, ((I.p j : ℚ≥0) : ℝ) ≤ outSched I σ j := by
    intro j
    by_cases hj : j ∈ zeroSet I
    · simp only [out_Z I σ j hj, pZR I j hj, le_refl]
    · rcases j with a | b
      · have h1 := hF.1 (Sum.inl (⟨a, hj⟩ : AZ I))
        rw [pA I a hj, ← hmulA a hj] at h1
        exact le_of_mul_le_mul_right h1 hD
      · have h1 := hF.1 (Sum.inr (Sum.inl (⟨b, hj⟩ : BZ I)))
        rw [pB I b hj, ← hmulB b hj] at h1
        exact le_of_mul_le_mul_right h1 hD
  refine ⟨⟨hrel, ?_, ?_, ?_⟩, ?_⟩
  · -- disjointness
    intro i j hij
    by_cases hi : i ∈ zeroSet I
    · left
      rw [out_Z I σ i hi]
      linarith [hrel j]
    · by_cases hj : j ∈ zeroSet I
      · right
        rw [out_Z I σ j hj]
        linarith [hrel i]
      · rcases i with a | b <;> rcases j with a' | b'
        · have hne : (Sum.inl (⟨a, hi⟩ : AZ I) : (AndOrSched.normalize I).N) ≠
              Sum.inl (⟨a', hj⟩ : AZ I) := by
            intro h
            apply hij
            have := congrArg (orig I) h
            exact this
          rcases hF.2.1 (Sum.inl (⟨a, hi⟩ : AZ I)) (Sum.inl (⟨a', hj⟩ : AZ I)) hne with h1 | h1
          · left
            rw [pA I a' hj, ← hmulA a hi, ← hmulA a' hj] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
          · right
            rw [pA I a hi, ← hmulA a' hj, ← hmulA a hi] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
        · have hne : (Sum.inl (⟨a, hi⟩ : AZ I) : (AndOrSched.normalize I).N) ≠
              Sum.inr (Sum.inl (⟨b', hj⟩ : BZ I)) := Sum.inl_ne_inr
          rcases hF.2.1 (Sum.inl (⟨a, hi⟩ : AZ I)) (Sum.inr (Sum.inl (⟨b', hj⟩ : BZ I))) hne with h1 | h1
          · left
            rw [pB I b' hj, ← hmulA a hi, ← hmulB b' hj] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
          · right
            rw [pA I a hi, ← hmulB b' hj, ← hmulA a hi] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
        · have hne : (Sum.inr (Sum.inl (⟨b, hi⟩ : BZ I)) : (AndOrSched.normalize I).N) ≠
              Sum.inl (⟨a', hj⟩ : AZ I) := Sum.inr_ne_inl
          rcases hF.2.1 (Sum.inr (Sum.inl (⟨b, hi⟩ : BZ I))) (Sum.inl (⟨a', hj⟩ : AZ I)) hne with h1 | h1
          · left
            rw [pA I a' hj, ← hmulB b hi, ← hmulA a' hj] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
          · right
            rw [pB I b hi, ← hmulA a' hj, ← hmulB b hi] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
        · have hne : (Sum.inr (Sum.inl (⟨b, hi⟩ : BZ I)) : (AndOrSched.normalize I).N) ≠
              Sum.inr (Sum.inl (⟨b', hj⟩ : BZ I)) := by
            intro h
            apply hij
            have := congrArg (orig I) h
            exact this
          rcases hF.2.1 (Sum.inr (Sum.inl (⟨b, hi⟩ : BZ I))) (Sum.inr (Sum.inl (⟨b', hj⟩ : BZ I))) hne with h1 | h1
          · left
            rw [pB I b' hj, ← hmulB b hi, ← hmulB b' hj] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
          · right
            rw [pB I b hi, ← hmulB b' hj, ← hmulB b hi] at h1
            exact le_of_mul_le_mul_right (by linarith) hD
  · -- AND precedences
    intro i j hij
    by_cases hj : j ∈ zeroSet I
    · obtain ⟨hp0, hand, -⟩ := Z_inv I j hj
      have hi : i ∈ zeroSet I := hand i hij
      rw [out_Z I σ i hi, out_Z I σ j hj, hp0]
      simp
    · by_cases hi : i ∈ zeroSet I
      · rw [out_Z I σ i hi]
        linarith [hrel j]
      · rcases i with a | b <;> rcases j with a' | b'
        · have h1 := hF.2.2.1 (Sum.inl (⟨a, hi⟩ : AZ I)) (Sum.inl (⟨a', hj⟩ : AZ I)) hij
          rw [pA I a' hj, ← hmulA a hi, ← hmulA a' hj] at h1
          exact le_of_mul_le_mul_right (by linarith) hD
        · exact (hij : False).elim
        · exact (hij : False).elim
        · have h1 := hF.2.2.1 (Sum.inr (Sum.inl (⟨b, hi⟩ : BZ I)))
            (Sum.inr (Sum.inl (⟨b', hj⟩ : BZ I))) hij
          rw [pB I b' hj, ← hmulB b hi, ← hmulB b' hj] at h1
          exact le_of_mul_le_mul_right (by linarith) hD
  · -- OR precedences
    intro b hne
    by_cases hb : Sum.inr b ∈ zeroSet I
    · obtain ⟨hp0, -, hor⟩ := Z_inv I _ hb
      rcases hor with ⟨a, ha⟩ | ⟨b', hb', h⟩
      · exact absurd ha Sum.inr_ne_inl
      · have hbb : b' = b := (Sum.inr_injective hb').symm
        subst hbb
        rcases h with h | ⟨a, ha, haZ⟩
        · exact absurd h (Finset.nonempty_iff_ne_empty.mp hne)
        · refine ⟨a, ha, ?_⟩
          rw [out_Z I σ _ haZ, out_Z I σ _ hb, hp0]
          simp
    · by_cases hz : ∃ a ∈ orPred I b, Sum.inl a ∈ zeroSet I
      · obtain ⟨a, ha, haZ⟩ := hz
        refine ⟨a, ha, ?_⟩
        rw [out_Z I σ _ haZ]
        linarith [hrel (Sum.inr b)]
      · obtain ⟨a0, ha0⟩ := hne
        obtain ⟨a1, ha1nr, -⟩ := exists_nonred I hI b a0 ha0
        have ha1Z : Sum.inl a1 ∉ zeroSet I := fun h => hz ⟨a1, nonred_sub I b a1 ha1nr, h⟩
        have hmem := (mem_orPredB I b hb a1 ha1Z).mpr ⟨ha1nr, hz⟩
        obtain ⟨⟨a2, ha2⟩, ha2m, hle⟩ := hF.2.2.2 (Sum.inl (⟨b, hb⟩ : BZ I)) ⟨_, hmem⟩
        obtain ⟨ha2nr, -⟩ := (mem_orPredB I b hb a2 ha2).mp ha2m
        refine ⟨a2, nonred_sub I b a2 ha2nr, ?_⟩
        rw [pB I b hb, ← hmulA a2 ha2, ← hmulB b hb] at hle
        exact le_of_mul_le_mul_right (by linarith) hD
  · -- cost
    rw [le_div_iff₀ hD]
    unfold cost
    -- the jobs outside Z come from non-A jobs of the normalized instance
    have hinj := orig_injOn I
    have hcover : ∀ x ∈ (Finset.univ : Finset I.N),
        x ∉ (Finset.univ.filter (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a)).image
          (orig I) → (I.w x : ℝ) * outSched I σ x = 0 := by
      intro x _ hx
      by_cases hxZ : x ∈ zeroSet I
      · rw [out_Z I σ x hxZ, mul_zero]
      · exfalso
        apply hx
        rw [Finset.mem_image]
        rcases x with a | b
        · refine ⟨Sum.inr (Sum.inr (⟨a, hxZ⟩ : AZ I)), ?_, rfl⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rintro ⟨a', h'⟩
          exact Sum.inr_ne_inl h'
        · refine ⟨Sum.inr (Sum.inl (⟨b, hxZ⟩ : BZ I)), ?_, rfl⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rintro ⟨a', h'⟩
          exact Sum.inr_ne_inl h'
    have hterm : ∀ j' ∈ Finset.univ.filter
        (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a),
        (fun j : I.N => (I.w j : ℝ) * outSched I σ j) (orig I j') * (scaleD I : ℝ) ≤
          ((AndOrSched.normalize I).w j' : ℝ) * listC (AndOrSched.normalize I) σ j' := by
      intro j' hj'
      have hj'' := (Finset.mem_filter.mp hj').2
      rcases j' with ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨d, hd⟩
      · exact absurd ⟨_, rfl⟩ hj''
      · show (I.w (Sum.inr b) : ℝ) * outSched I σ (Sum.inr b) * (scaleD I : ℝ) ≤
          (I.w (Sum.inr b) : ℝ) * listC (AndOrSched.normalize I) σ (Sum.inr (Sum.inl (⟨b, hb⟩ : BZ I)))
        exact le_of_eq (by rw [mul_assoc, hmulB b hb])
      · show (I.w (Sum.inl d) : ℝ) * outSched I σ (Sum.inl d) * (scaleD I : ℝ) ≤
          (I.w (Sum.inl d) : ℝ) * listC (AndOrSched.normalize I) σ (Sum.inr (Sum.inr (⟨d, hd⟩ : AZ I)))
        rw [mul_assoc, hmulA d hd]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hdm := (mem_orPredD I d hd d hd).mpr rfl
        obtain ⟨⟨a2, ha2⟩, ha2m, hle⟩ := hF.2.2.2 (Sum.inr (⟨d, hd⟩ : AZ I)) ⟨_, hdm⟩
        have h2 := (mem_orPredD I d hd a2 ha2).mp ha2m
        subst h2
        rw [pDm I a2 hd] at hle
        linarith
    have hsum1 : ∑ x, (I.w x : ℝ) * outSched I σ x =
        ∑ x ∈ (Finset.univ.filter (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a)).image
          (orig I), (I.w x : ℝ) * outSched I σ x :=
      (Finset.sum_subset (Finset.subset_univ _) hcover).symm
    rw [hsum1, Finset.sum_image hinj, Finset.sum_mul]
    calc ∑ j' ∈ Finset.univ.filter (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a),
          (fun j : I.N => (I.w j : ℝ) * outSched I σ j) (orig I j') * (scaleD I : ℝ)
        ≤ ∑ j' ∈ Finset.univ.filter (fun j' : (AndOrSched.normalize I).N => ¬ ∃ a, j' = Sum.inl a),
            ((AndOrSched.normalize I).w j' : ℝ) * listC (AndOrSched.normalize I) σ j' :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ j', ((AndOrSched.normalize I).w j' : ℝ) * listC (AndOrSched.normalize I) σ j' :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j' _ _ => mul_nonneg (by positivity) (hLnn j'))

end Aux_AOS_norm

open AndOrSched Aux_AOS_norm in
theorem solution (I : Instance) (hI : Acyclic I) :
    Acyclic (AndOrSched.normalize I) ∧ IsNormalized (AndOrSched.normalize I) ∧
    delta (AndOrSched.normalize I) ≤ delta I ∧
    Fintype.card (AndOrSched.normalize I).N ≤ 2 * Fintype.card I.N ∧
    ((∀ j, I.p j = 0 ∨ I.p j = 1) →
      ∀ j, (AndOrSched.normalize I).p j = 0 ∨ (AndOrSched.normalize I).p j = 1) ∧
    (∀ C : I.N → ℝ, IsFeasible I C →
      ∃ C' : (AndOrSched.normalize I).N → ℝ, IsFeasible (AndOrSched.normalize I) C' ∧
        cost (AndOrSched.normalize I) C' ≤ (scaleD I : ℝ) * cost I C) ∧
    ∀ σ : (AndOrSched.normalize I).N ≃ Fin (Fintype.card (AndOrSched.normalize I).N),
      IsFeasible (AndOrSched.normalize I) (listC (AndOrSched.normalize I) σ) →
        IsFeasible I (outSched I σ) ∧
        cost I (outSched I σ) ≤
          cost (AndOrSched.normalize I) (listC (AndOrSched.normalize I) σ) / (scaleD I : ℝ) :=
  ⟨acyclic_norm I hI, norm_isNormalized I hI, delta_norm I, card_norm I, p01_norm I,
    fun C hC => forward I hI C hC, fun σ hF => backward I hI σ hF⟩
