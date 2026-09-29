-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1222b9b4-6b6c-5c59-82cb-ab2d79a57597

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

section PertGeneric
variable {K₂ F₂ : Type*} [Field K₂] [Field F₂] [Algebra K₂ F₂]

theorem PerturbAux.ord_add_of_lt {v : Place K₂ F₂} {x y : F₂} (hx : x ≠ 0) (hy : y = 0 ∨ v.ord x < v.ord y) :
    x + y ≠ 0 ∧ v.ord (x + y) = v.ord x := by
  by_cases hy0 : y = 0
  · subst hy0
    simpa using hx
  have hlt : v.ord x < v.ord y := hy.resolve_left hy0
  have hval : v.adicValuation y < v.adicValuation x := by
    rw [v.adicValuation_eq_exp_neg_ord hx, v.adicValuation_eq_exp_neg_ord hy0, WithZero.exp_lt_exp]
    omega
  have hsum : v.adicValuation (x + y) = v.adicValuation x := v.adicValuation.map_add_eq_of_lt_left hval
  refine ⟨fun h0 => v.adicValuation_ne_zero hx ?_, ?_⟩
  · rw [← hsum, h0, map_zero]
  · simp only [Place.ord, hsum]

end PertGeneric

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R₁ R₂ : RegularProlongation A F Fb)
    (E : Divisor L F) (V₀ : Place L F) (hEV₀ : E V₀ = 0)
    (v₁ v₂ : Place K Fb)
    (hlaw : ∀ (g : F) (hg₁ : g ∈ R₁.integers) (hg₂ : g ∈ R₂.integers),
      g ∈ riemannRochSpace (E + Finsupp.single V₀ 1) →
        R₁.residue ⟨g, hg₁⟩ ≠ 0 → R₂.residue ⟨g, hg₂⟩ ≠ 0 →
          -1 ≤ v₁.ord (R₁.residue ⟨g, hg₁⟩) + v₂.ord (R₂.residue ⟨g, hg₂⟩))
    (p₁ : F) (hp₁E : p₁ ∈ riemannRochSpace E) (hp₁₁ : p₁ ∈ R₁.integers) (hp₁₂ : p₁ ∈ R₂.integers)
    (hp₁ : R₁.residue ⟨p₁, hp₁₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨p₁, hp₁₁⟩) = 0 ∧
      (R₂.residue ⟨p₁, hp₁₂⟩ = 0 ∨ 0 ≤ v₂.ord (R₂.residue ⟨p₁, hp₁₂⟩)))
    (p₂ : F) (hp₂E : p₂ ∈ riemannRochSpace E) (hp₂₁ : p₂ ∈ R₁.integers) (hp₂₂ : p₂ ∈ R₂.integers)
    (hp₂ : R₂.residue ⟨p₂, hp₂₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨p₂, hp₂₂⟩) = 0 ∧
      (R₁.residue ⟨p₂, hp₂₁⟩ = 0 ∨ 0 ≤ v₁.ord (R₁.residue ⟨p₂, hp₂₁⟩)))
    (f : F) (hfE : f ∈ riemannRochSpace (E + Finsupp.single V₀ 1))
    (hfV₀ : V₀.ord f = -1) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers)
    (hviol : (R₁.residue ⟨f, hf₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨f, hf₁⟩) < 0) ∨
      (R₂.residue ⟨f, hf₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨f, hf₂⟩) < 0)) :
    ∃ (g : F) (hg₁ : g ∈ R₁.integers) (hg₂ : g ∈ R₂.integers),
      g ∈ riemannRochSpace (E + Finsupp.single V₀ 1) ∧ V₀.ord g = -1 ∧
      R₁.residue ⟨g, hg₁⟩ ≠ 0 ∧ R₂.residue ⟨g, hg₂⟩ ≠ 0 ∧
      ((v₁.ord (R₁.residue ⟨g, hg₁⟩) = -1 ∧ v₂.ord (R₂.residue ⟨g, hg₂⟩) = 0) ∨
        (v₁.ord (R₁.residue ⟨g, hg₁⟩) = 0 ∧ v₂.ord (R₂.residue ⟨g, hg₂⟩) = -1)) := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hfV₀
    omega
  have hmemp : ∀ {p : F}, p ∈ riemannRochSpace E →
      p ∈ riemannRochSpace (E + Finsupp.single V₀ 1) := by
    intro p hp
    rw [mem_riemannRochSpace_iff] at hp ⊢
    intro v
    refine (hp v).imp_right fun h => le_trans ?_ h
    have h1 : 0 ≤ (Finsupp.single V₀ (1 : ℤ)) v := by
      rw [Finsupp.single_apply]
      split_ifs <;> omega
    simp only [Finsupp.coe_add, Pi.add_apply]
    omega
  have hordp : ∀ {p : F}, p ∈ riemannRochSpace E → V₀.ord (f + p) = -1 := by
    intro p hp
    have h1 : p = 0 ∨ V₀.ord f < V₀.ord p := by
      refine (mem_riemannRochSpace_iff.mp hp V₀).imp_right fun h => ?_
      rw [hEV₀] at h
      omega
    exact (PerturbAux.ord_add_of_lt hf0 h1).2.trans hfV₀
  have hne₁ : ∀ x : R₁.integers, R₁.residue x ≠ 0 → R₁.residue x ≠ 0 := fun x h => h
  have hne₂ : ∀ x : R₂.integers, R₂.residue x ≠ 0 → R₂.residue x ≠ 0 := fun x h => h
  rcases hviol with ⟨hr₁, ha⟩ | ⟨hr₂, hb⟩
  ·
    by_cases hunit : R₂.residue ⟨f, hf₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨f, hf₂⟩) = 0
    · refine ⟨f, hf₁, hf₂, hfE, hfV₀, hne₁ _ hr₁, hne₂ _ hunit.1, Or.inl ⟨?_, hunit.2⟩⟩
      have hl := hlaw f hf₁ hf₂ hfE (hne₁ _ hr₁) (hne₂ _ hunit.1)
      omega
    by_cases hneg : R₂.residue ⟨f, hf₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨f, hf₂⟩) < 0
    · exfalso
      have hl := hlaw f hf₁ hf₂ hfE (hne₁ _ hr₁) (hne₂ _ hneg.1)
      omega
    have hpos : R₂.residue ⟨f, hf₂⟩ = 0 ∨ v₂.ord (R₂.residue ⟨p₂, hp₂₂⟩) < v₂.ord (R₂.residue ⟨f, hf₂⟩) := by
      by_cases h0 : R₂.residue ⟨f, hf₂⟩ = 0
      · exact Or.inl h0
      · right
        rw [hp₂.2.1]
        have h1 : ¬ v₂.ord (R₂.residue ⟨f, hf₂⟩) = 0 := fun h => hunit ⟨h0, h⟩
        have h2 : ¬ v₂.ord (R₂.residue ⟨f, hf₂⟩) < 0 := fun h => hneg ⟨h0, h⟩
        omega
    have hreg : R₁.residue ⟨p₂, hp₂₁⟩ = 0 ∨ v₁.ord (R₁.residue ⟨f, hf₁⟩) < v₁.ord (R₁.residue ⟨p₂, hp₂₁⟩) :=
      hp₂.2.2.imp_right fun h => by omega
    have e₁ : R₁.residue ⟨f + p₂, add_mem hf₁ hp₂₁⟩ = R₁.residue ⟨f, hf₁⟩ + R₁.residue ⟨p₂, hp₂₁⟩ :=
      map_add R₁.residue ⟨f, hf₁⟩ ⟨p₂, hp₂₁⟩
    have e₂ : R₂.residue ⟨f + p₂, add_mem hf₂ hp₂₂⟩ = R₂.residue ⟨p₂, hp₂₂⟩ + R₂.residue ⟨f, hf₂⟩ :=
      (map_add R₂.residue ⟨f, hf₂⟩ ⟨p₂, hp₂₂⟩).trans (add_comm _ _)
    have s₁ := PerturbAux.ord_add_of_lt hr₁ hreg
    have s₂ := PerturbAux.ord_add_of_lt hp₂.1 hpos
    have hg₁' : R₁.residue ⟨f + p₂, add_mem hf₁ hp₂₁⟩ ≠ 0 := by
      rw [e₁]
      exact s₁.1
    have hg₂' : R₂.residue ⟨f + p₂, add_mem hf₂ hp₂₂⟩ ≠ 0 := by
      rw [e₂]
      exact s₂.1
    have hmem : f + p₂ ∈ riemannRochSpace (E + Finsupp.single V₀ 1) := add_mem hfE (hmemp hp₂E)
    have hl := hlaw (f + p₂) (add_mem hf₁ hp₂₁) (add_mem hf₂ hp₂₂) hmem (hne₁ _ hg₁') (hne₂ _ hg₂')
    rw [e₁, e₂, s₁.2, s₂.2, hp₂.2.1] at hl
    refine ⟨f + p₂, add_mem hf₁ hp₂₁, add_mem hf₂ hp₂₂, hmem, hordp hp₂E, hne₁ _ hg₁', hne₂ _ hg₂',
      Or.inl ⟨?_, ?_⟩⟩
    · rw [e₁, s₁.2]
      omega
    · rw [e₂, s₂.2, hp₂.2.1]
  ·
    by_cases hunit : R₁.residue ⟨f, hf₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨f, hf₁⟩) = 0
    · refine ⟨f, hf₁, hf₂, hfE, hfV₀, hne₁ _ hunit.1, hne₂ _ hr₂, Or.inr ⟨hunit.2, ?_⟩⟩
      have hl := hlaw f hf₁ hf₂ hfE (hne₁ _ hunit.1) (hne₂ _ hr₂)
      omega
    by_cases hneg : R₁.residue ⟨f, hf₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨f, hf₁⟩) < 0
    · exfalso
      have hl := hlaw f hf₁ hf₂ hfE (hne₁ _ hneg.1) (hne₂ _ hr₂)
      omega
    have hpos : R₁.residue ⟨f, hf₁⟩ = 0 ∨ v₁.ord (R₁.residue ⟨p₁, hp₁₁⟩) < v₁.ord (R₁.residue ⟨f, hf₁⟩) := by
      by_cases h0 : R₁.residue ⟨f, hf₁⟩ = 0
      · exact Or.inl h0
      · right
        rw [hp₁.2.1]
        have h1 : ¬ v₁.ord (R₁.residue ⟨f, hf₁⟩) = 0 := fun h => hunit ⟨h0, h⟩
        have h2 : ¬ v₁.ord (R₁.residue ⟨f, hf₁⟩) < 0 := fun h => hneg ⟨h0, h⟩
        omega
    have hreg : R₂.residue ⟨p₁, hp₁₂⟩ = 0 ∨ v₂.ord (R₂.residue ⟨f, hf₂⟩) < v₂.ord (R₂.residue ⟨p₁, hp₁₂⟩) :=
      hp₁.2.2.imp_right fun h => by omega
    have e₁ : R₁.residue ⟨f + p₁, add_mem hf₁ hp₁₁⟩ = R₁.residue ⟨p₁, hp₁₁⟩ + R₁.residue ⟨f, hf₁⟩ :=
      (map_add R₁.residue ⟨f, hf₁⟩ ⟨p₁, hp₁₁⟩).trans (add_comm _ _)
    have e₂ : R₂.residue ⟨f + p₁, add_mem hf₂ hp₁₂⟩ = R₂.residue ⟨f, hf₂⟩ + R₂.residue ⟨p₁, hp₁₂⟩ :=
      map_add R₂.residue ⟨f, hf₂⟩ ⟨p₁, hp₁₂⟩
    have s₁ := PerturbAux.ord_add_of_lt hp₁.1 hpos
    have s₂ := PerturbAux.ord_add_of_lt hr₂ hreg
    have hg₁' : R₁.residue ⟨f + p₁, add_mem hf₁ hp₁₁⟩ ≠ 0 := by
      rw [e₁]
      exact s₁.1
    have hg₂' : R₂.residue ⟨f + p₁, add_mem hf₂ hp₁₂⟩ ≠ 0 := by
      rw [e₂]
      exact s₂.1
    have hmem : f + p₁ ∈ riemannRochSpace (E + Finsupp.single V₀ 1) := add_mem hfE (hmemp hp₁E)
    have hl := hlaw (f + p₁) (add_mem hf₁ hp₁₁) (add_mem hf₂ hp₁₂) hmem (hne₁ _ hg₁') (hne₂ _ hg₂')
    rw [e₁, e₂, s₁.2, s₂.2, hp₁.2.1] at hl
    refine ⟨f + p₁, add_mem hf₁ hp₁₁, add_mem hf₂ hp₁₂, hmem, hordp hp₁E, hne₁ _ hg₁', hne₂ _ hg₂',
      Or.inr ⟨?_, ?_⟩⟩
    · rw [e₁, s₁.2, hp₁.2.1]
    · rw [e₂, s₂.2]
      omega

end S_AlgebraicCurve_RegularProlongation_exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw (solution)
