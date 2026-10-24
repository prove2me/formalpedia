-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:53:05.861972+00:00
-- url     : https://prove2.me/submissions/801e007a-78fb-4dac-a1b5-7ea9c67d3eaf

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control

open MeasureTheory Set Filter Topology Matrix

open AtaBarjesteh23.Workload in
theorem solution (M : Model) (hM : M.Standing) (x : ℝ) :
    IsLeast {q : ℝ | ∃ ζ : Fin M.K → ℝ, M.m ⬝ᵥ ζ = x ∧ q = ζ ⬝ᵥ (M.H *ᵥ ζ)} (x ^ 2 / M.a) ∧
    M.m ⬝ᵥ ((x / M.a) • (M.H⁻¹ *ᵥ M.m)) = x ∧
    (x / M.a) • (M.H⁻¹ *ᵥ M.m) ⬝ᵥ (M.H *ᵥ ((x / M.a) • (M.H⁻¹ *ᵥ M.m))) = x ^ 2 / M.a ∧
    (∀ ζ : Fin M.K → ℝ, M.m ⬝ᵥ ζ = x → ζ ⬝ᵥ (M.H *ᵥ ζ) = x ^ 2 / M.a →
      ζ = (x / M.a) • (M.H⁻¹ *ᵥ M.m)) ∧
    M.cost x = x ^ 2 / M.a := by
  obtain ⟨hK, hm, -, -, -, hH, -, -⟩ := hM
  have hHinv : M.H⁻¹.PosDef := hH.inv
  have hmne : M.m ≠ 0 := by
    intro h
    have := hm ⟨0, hK⟩
    rw [h] at this
    simp at this
  have ha : 0 < M.a := by
    have := hHinv.dotProduct_mulVec_pos hmne
    simpa [Model.a] using this
  have hHH : M.H *ᵥ (M.H⁻¹ *ᵥ M.m) = M.m := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hH.isUnit), one_mulVec]
  have hT : M.Hᵀ = M.H := by
    have := hH.isHermitian
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hsymm : ∀ u w : Fin M.K → ℝ, u ⬝ᵥ (M.H *ᵥ w) = w ⬝ᵥ (M.H *ᵥ u) := by
    intro u w
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  set a := M.a with ha_def
  set ζ0 : Fin M.K → ℝ := (x / a) • (M.H⁻¹ *ᵥ M.m) with hζ0
  have hma : M.m ⬝ᵥ (M.H⁻¹ *ᵥ M.m) = a := rfl
  have hHζ0 : M.H *ᵥ ζ0 = (x / a) • M.m := by
    rw [hζ0, mulVec_smul, hHH]
  have hmζ0 : M.m ⬝ᵥ ζ0 = x := by
    rw [hζ0, dotProduct_smul, hma, smul_eq_mul]
    field_simp
  have hζ0ζ0 : ζ0 ⬝ᵥ (M.H *ᵥ ζ0) = x ^ 2 / a := by
    rw [hHζ0, dotProduct_smul, dotProduct_comm, hmζ0, smul_eq_mul]
    field_simp
  have hexp : ∀ ζ : Fin M.K → ℝ, M.m ⬝ᵥ ζ = x →
      ζ ⬝ᵥ (M.H *ᵥ ζ) = x ^ 2 / a + (ζ - ζ0) ⬝ᵥ (M.H *ᵥ (ζ - ζ0)) := by
    intro ζ hζ
    set d := ζ - ζ0 with hd
    have hζe : ζ = ζ0 + d := by rw [hd]; abel
    have hmd : M.m ⬝ᵥ d = 0 := by
      rw [hd, dotProduct_sub, hζ, hmζ0, sub_self]
    have hcross : d ⬝ᵥ (M.H *ᵥ ζ0) = 0 := by
      rw [hHζ0, dotProduct_smul, dotProduct_comm, hmd, smul_zero]
    have hcross2 : ζ0 ⬝ᵥ (M.H *ᵥ d) = 0 := by rw [hsymm, hcross]
    rw [hζe, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross, hcross2,
      hζ0ζ0]
    ring
  have hnonneg : ∀ d : Fin M.K → ℝ, 0 ≤ d ⬝ᵥ (M.H *ᵥ d) := by
    intro d
    by_cases h : d = 0
    · simp [h]
    · have := hH.dotProduct_mulVec_pos h
      simpa using this.le
  have hleast : IsLeast {q : ℝ | ∃ ζ : Fin M.K → ℝ, M.m ⬝ᵥ ζ = x ∧ q = ζ ⬝ᵥ (M.H *ᵥ ζ)}
      (x ^ 2 / a) := by
    refine ⟨⟨ζ0, hmζ0, hζ0ζ0.symm⟩, ?_⟩
    rintro q ⟨ζ, hζ, rfl⟩
    rw [hexp ζ hζ]
    linarith [hnonneg (ζ - ζ0)]
  refine ⟨hleast, hmζ0, hζ0ζ0, ?_, ?_⟩
  · intro ζ hζ hq
    rw [hexp ζ hζ] at hq
    have h0 : (ζ - ζ0) ⬝ᵥ (M.H *ᵥ (ζ - ζ0)) = 0 := by linarith
    by_contra hne
    have hne' : ζ - ζ0 ≠ 0 := sub_ne_zero.mpr hne
    have := hH.dotProduct_mulVec_pos hne'
    rw [star_trivial] at this
    linarith
  · exact hleast.csInf_eq
