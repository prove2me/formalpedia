-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_smul_mem_integers_and_residue_ne_zero_or
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a5aff71e-20f5-5edb-816b-b2ad19bd1bc2

import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (R₁ R₂ : AlgebraicCurve.RegularProlongation A F Fbar) {f : F} (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ (h₁ : c • f ∈ R₁.integers) (h₂ : c • f ∈ R₂.integers),
      R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∨ R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by
  obtain ⟨c₁, h₁, hr₁⟩ := R₁.exists_smul_mem f hf
  obtain ⟨c₂, h₂, hr₂⟩ := R₂.exists_smul_mem f hf
  have hc₁ : c₁ ≠ 0 := R₁.smul_const_ne_zero h₁ hr₁
  have hc₂ : c₂ ≠ 0 := R₂.smul_const_ne_zero h₂ hr₂
  rcases A.mem_or_inv_mem (c₁ / c₂) with h | h
  · have e : c₁ • f = algebraMap L F (c₁ / c₂) * (c₂ • f) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    have h₁₂ : c₁ • f ∈ R₂.integers := by
      rw [e]
      exact mul_mem ((R₂.algebraMap_mem_iff _).mpr h) h₂
    exact ⟨c₁, hc₁, h₁, h₁₂, Or.inl hr₁⟩
  · rw [inv_div] at h
    have e : c₂ • f = algebraMap L F (c₂ / c₁) * (c₁ • f) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    have h₂₁ : c₂ • f ∈ R₁.integers := by
      rw [e]
      exact mul_mem ((R₁.algebraMap_mem_iff _).mpr h) h₁
    exact ⟨c₂, hc₂, h₂₁, h₂, Or.inr hr₂⟩

end S_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or (solution)
