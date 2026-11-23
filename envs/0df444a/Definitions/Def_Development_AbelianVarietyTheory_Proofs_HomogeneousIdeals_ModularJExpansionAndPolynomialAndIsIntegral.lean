-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:16.443095+00:00
-- url     : https://prove2.me/theorems/62d8aeed-913b-436b-bbe0-70eeb90d428f
-- title:
--   Modular JExpansion And Polynomial And Is Integral
-- statement:
--   Definitions and structural lemmas for Modular JExpansion And Polynomial And Is Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Theorems.Thm_GlobalTheory_HasQExpansion_add
import Theorems.Thm_GlobalTheory_HasQExpansion_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
namespace GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
def integralSeries : Subring ℂ⟦X⟧ where
  carrier := {ψ | ∀ k, IsIntegral ℤ (coeff k ψ)}
  mul_mem' {φ ψ} hφ hψ k := by
    rw [coeff_mul]
    exact IsIntegral.sum _ fun x _ ↦ (hφ _).mul (hψ _)
  one_mem' k := by
    rw [coeff_one]
    split_ifs
    exacts [isIntegral_one, isIntegral_zero]
  add_mem' {φ ψ} hφ hψ k := by simpa using (hφ k).add (hψ k)
  zero_mem' k := by simpa using isIntegral_zero
  neg_mem' {φ} hφ k := by simpa using (hφ k).neg
def HasUnitLeadingExpansion (n : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ (e : ℕ) (ψ : ℂ⟦X⟧), ψ ∈ integralSeries ∧ constantCoeff ψ ≠ 0 ∧
    IsIntegral ℤ (constantCoeff ψ)⁻¹ ∧ HasQExpansion n (fun τ ↦ 𝕢 n τ ^ e * f τ) ψ
def fixedDetToGL {n : ℕ} (hn : n ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ n) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix A.1) (by
    rw [← RingHom.map_det, A.2]; simpa using hn)
def halfOneAddSqrtNeg (d : ℕ) (hd : d ≠ 0) : ℍ :=
  ⟨(1 + √d * Complex.I) / 2, by
    have : (0 : ℝ) < √d := Real.sqrt_pos.mpr (by positivity)
    simpa using this⟩
end GlobalTheory


