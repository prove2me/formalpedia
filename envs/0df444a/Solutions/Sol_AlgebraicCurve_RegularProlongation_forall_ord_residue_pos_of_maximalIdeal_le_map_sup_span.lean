-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d7aeafd3-4c5b-59ad-8ce5-97ebd72f88fb

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing

namespace RegularProlongationPosAscentSol

theorem min_ord_le_ord_add {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (v.ord a) (v.ord b) ≤ v.ord (a + b) := by
  have h := v.adicValuation.map_add a b
  have hva := v.adicValuation_ne_zero ha
  have hvb := v.adicValuation_ne_zero hb
  have hvab := v.adicValuation_ne_zero hab
  change min (-(WithZero.log (v.adicValuation a))) (-(WithZero.log (v.adicValuation b))) ≤
    -(WithZero.log (v.adicValuation (a + b)))
  rcases le_total (v.adicValuation a) (v.adicValuation b) with hle | hle
  · have h1 : v.adicValuation (a + b) ≤ v.adicValuation b := h.trans (max_le hle le_rfl)
    have h2 : WithZero.log (v.adicValuation (a + b)) ≤ WithZero.log (v.adicValuation b) :=
      (WithZero.log_le_log hvab hvb).2 h1
    exact min_le_of_right_le (by linarith)
  · have h1 : v.adicValuation (a + b) ≤ v.adicValuation a := h.trans (max_le le_rfl hle)
    have h2 : WithZero.log (v.adicValuation (a + b)) ≤ WithZero.log (v.adicValuation a) :=
      (WithZero.log_le_log hvab hva).2 h1
    exact min_le_of_left_le (by linarith)

section Pos

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem reg_pos (R : RegularProlongation A F Fbar) (xp : Place (ResidueField A) Fbar)
    (N0 N1 : Subring F) [IsLocalRing ↥N0] [IsLocalRing ↥N1] (h01 : N0 ≤ N1)
    (hN1 : ∀ f : F, f ∈ N1 → f ∈ R.integers)
    (hreg0 : ∀ (f : ↥N0) (h : (f : F) ∈ R.integers), 0 ≤ xp.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < xp.ord (R.residue ⟨f, h⟩)))
    (hreg1 : ∀ (f : ↥N1) (h : (f : F) ∈ R.integers), 0 ≤ xp.ord (R.residue ⟨f, h⟩))
    (w : F) (hw1 : w ∈ N1) (hwres : ∀ h : w ∈ R.integers, R.residue ⟨w, h⟩ = 0)
    (hmax : maximalIdeal ↥N1 ≤ (maximalIdeal ↥N0).map (Subring.inclusion h01) ⊔ Ideal.span {⟨w, hw1⟩}) :
    ∀ (f : ↥N1) (h : (f : F) ∈ R.integers), 0 ≤ xp.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < xp.ord (R.residue ⟨f, h⟩)) := by
  classical

  let red : ↥N1 → Fbar := fun f => R.residue ⟨(f : F), hN1 _ f.2⟩
  have hred : ∀ (f : ↥N1) (h : (f : F) ∈ R.integers), R.residue ⟨f, h⟩ = red f := fun f h => rfl
  have red_add : ∀ f g : ↥N1, red (f + g) = red f + red g := by
    intro f g
    change R.residue _ = R.residue _ + R.residue _
    rw [← map_add]
    rfl
  have red_mul : ∀ f g : ↥N1, red (f * g) = red f * red g := by
    intro f g
    change R.residue _ = R.residue _ * R.residue _
    rw [← map_mul]
    rfl
  have red_zero : red 0 = 0 := by
    change R.residue _ = 0
    have : (⟨((0 : ↥N1) : F), hN1 _ (0 : ↥N1).2⟩ : ↥R.integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]

  let I : Ideal ↥N1 :=
    { carrier := {f | red f = 0 ∨ 0 < xp.ord (red f)}
      add_mem' := by
        intro f g hf hg
        simp only [Set.mem_setOf_eq] at hf hg ⊢
        rw [red_add]
        by_cases hs : red f + red g = 0
        · exact Or.inl hs
        right
        rcases hf with hf | hf
        · rw [hf, zero_add] at hs ⊢
          exact hg.resolve_left hs
        rcases hg with hg | hg
        · rw [hg, add_zero] at hs ⊢
          exact hf
        have hf0 : red f ≠ 0 := by
          intro h0; rw [h0, Place.ord_zero] at hf; exact lt_irrefl _ hf
        have hg0 : red g ≠ 0 := by
          intro h0; rw [h0, Place.ord_zero] at hg; exact lt_irrefl _ hg
        exact lt_of_lt_of_le (lt_min hf hg) (min_ord_le_ord_add xp hf0 hg0 hs)
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        exact Or.inl red_zero
      smul_mem' := by
        intro c f hf
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hf ⊢
        rw [red_mul]
        by_cases hs : red c * red f = 0
        · exact Or.inl hs
        right
        have hc0 : red c ≠ 0 := fun h0 => hs (by rw [h0, zero_mul])
        have hf0 : red f ≠ 0 := fun h0 => hs (by rw [h0, mul_zero])
        rw [Place.ord_mul _ hc0 hf0]
        have hcn : 0 ≤ xp.ord (red c) := hreg1 c (hN1 _ c.2)
        rcases hf with hf | hf
        · exact absurd hf hf0
        linarith }
  have hI_mem : ∀ f : ↥N1, f ∈ I ↔ (red f = 0 ∨ 0 < xp.ord (red f)) := fun f => Iff.rfl

  have hmapI : (maximalIdeal ↥N0).map (Subring.inclusion h01) ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap, hI_mem]
    have hmnu : ¬ IsUnit m := (IsLocalRing.mem_maximalIdeal m).mp hm
    have hmR : ((m : ↥N0) : F) ∈ R.integers := hN1 _ (h01 m.2)
    have key := (hreg0 m hmR).2 hmnu
    have hval : red (Subring.inclusion h01 m) = R.residue ⟨(m : F), hmR⟩ := rfl
    rw [hval]
    by_cases h0 : R.residue ⟨(m : F), hmR⟩ = 0
    · exact Or.inl h0
    · exact Or.inr (key h0)
  have hwI : Ideal.span {(⟨w, hw1⟩ : ↥N1)} ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change red ⟨w, hw1⟩ = 0 ∨ 0 < xp.ord (red ⟨w, hw1⟩)
    exact Or.inl (hwres (hN1 _ hw1))
  have hmaxI : maximalIdeal ↥N1 ≤ I := hmax.trans (sup_le hmapI hwI)

  intro f h
  refine ⟨hreg1 f h, fun hnu hne => ?_⟩
  have hfI : f ∈ I := hmaxI ((IsLocalRing.mem_maximalIdeal f).mpr hnu)
  rw [hI_mem] at hfI
  rw [hred] at hne ⊢
  exact hfI.resolve_left hne

end Pos

end RegularProlongationPosAscentSol

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : Place (ResidueField A) Fbar)
    (N₀ N₁ : Subring F) [IsLocalRing ↥N₀] [IsLocalRing ↥N₁] (h01 : N₀ ≤ N₁)
    (hN₁ : ∀ f : F, f ∈ N₁ → f ∈ R.integers)
    (hreg₀ : ∀ (f : ↥N₀) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < x.ord (R.residue ⟨f, h⟩)))
    (hreg₁ : ∀ (f : ↥N₁) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩))
    (w : F) (hw : w ∈ N₁) (hwres : ∀ h : w ∈ R.integers, R.residue ⟨w, h⟩ = 0)
    (hmax : maximalIdeal ↥N₁ ≤ (maximalIdeal ↥N₀).map (Subring.inclusion h01) ⊔ Ideal.span {⟨w, hw⟩}) :
    ∀ (f : ↥N₁) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < x.ord (R.residue ⟨f, h⟩)) :=
  RegularProlongationPosAscentSol.reg_pos A R x N₀ N₁ h01 hN₁ hreg₀ hreg₁ w hw hwres hmax

end S_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span (solution)
