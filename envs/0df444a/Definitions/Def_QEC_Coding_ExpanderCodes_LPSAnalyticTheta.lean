-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
-- name    : QEC_Coding_ExpanderCodes_LPSAnalyticTheta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:38:41.956091+00:00
-- url     : https://prove2.me/theorems/0ee008f9-99b9-407d-9573-10cdbda2ba50
-- title:
--   LPSAnalytic Theta
-- statement:
--   Definitions and structural lemmas for LPSAnalytic Theta, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
theorem natAbs_sq_eq_iff_mem_integerSquareRoots
    (n : ℕ) (z : ℤ) :
    z.natAbs ^ 2 = n ↔ z ∈ integerSquareRoots n := by
  rw [mem_integerSquareRoots_iff]
  constructor
  · intro h
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    simpa only [Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h'
  · intro h
    apply Nat.cast_injective (R := ℤ)
    simpa only [Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h
noncomputable instance integerSquareFibreFintype (n : ℕ) :
    Fintype {z : ℤ // z.natAbs ^ 2 = n} :=
  Fintype.ofEquiv {z : ℤ // z ∈ integerSquareRoots n}
    (Equiv.subtypeEquivRight
      (natAbs_sq_eq_iff_mem_integerSquareRoots n)).symm
theorem scaledNatAbs_sq_eq_iff_mem_scaledIntegerSquareRoots
    (m n : ℕ) (hm : 0 < m) (z : ℤ) :
    m ^ 2 * z.natAbs ^ 2 = n ↔ z ∈ scaledIntegerSquareRoots m n := by
  rw [mem_scaledIntegerSquareRoots_iff hm]
  constructor
  · intro h
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h'
  · intro h
    apply Nat.cast_injective (R := ℤ)
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, sq_abs] using h
@[instance_reducible] noncomputable def scaledIntegerSquareFibreFintype
    (m n : ℕ) (hm : 0 < m) :
    Fintype {z : ℤ // m ^ 2 * z.natAbs ^ 2 = n} :=
  Fintype.ofEquiv {z : ℤ // z ∈ scaledIntegerSquareRoots m n}
    (Equiv.subtypeEquivRight
      (scaledNatAbs_sq_eq_iff_mem_scaledIntegerSquareRoots m n hm)).symm
noncomputable def lpsAnalyticThetaProduct (r : ℕ) (τ : ℂ) : ℂ :=
  jacobiTheta τ * (jacobiTheta (((2 * r) ^ 2 : ℕ) * τ)) ^ 3
theorem differentiableAt_lpsAnalyticThetaProduct
    (r : ℕ) (hr : 0 < r) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (lpsAnalyticThetaProduct r) τ := by
  let m : ℕ := (2 * r) ^ 2
  have hm : 0 < (((m : ℕ) : ℂ) * τ).im := by
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    have hr : 0 < m := by
      dsimp [m]
      exact pow_pos (Nat.mul_pos (by omega) hr) 2
    exact mul_pos (Nat.cast_pos.mpr hr) hτ
  have hScaled : DifferentiableAt ℂ
      (fun z : ℂ => jacobiTheta ((m : ℂ) * z)) τ := by
    exact (differentiableAt_jacobiTheta hm).comp τ
      (differentiableAt_id.const_mul _)
  unfold lpsAnalyticThetaProduct
  exact (differentiableAt_jacobiTheta hτ).mul (hScaled.pow 3)
noncomputable def lpsStandardTheta (r : ℕ) (z : ℂ) : ℂ :=
  lpsAnalyticThetaProduct r (2 * z)
theorem differentiableAt_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (lpsStandardTheta r) z := by
  have hUpper : 0 < ((2 : ℂ) * z).im := by
    rw [Complex.mul_im]
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hz)
  unfold lpsStandardTheta
  exact (differentiableAt_lpsAnalyticThetaProduct r hr hUpper).comp z
    (differentiableAt_id.const_mul _)
theorem mdifferentiable_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) :
    MDiff (fun z : ℍ => lpsStandardTheta r z) := by
  intro z
  exact (differentiableAt_lpsStandardTheta r hr z.2).mdifferentiableAt.comp
    z z.mdifferentiable_coe
noncomputable def lpsStandardThetaContinuousMap
    (r : ℕ) (hr : 0 < r) : C(ℍ, ℂ) :=
  ⟨fun z => lpsStandardTheta r z,
    (mdifferentiable_lpsStandardTheta r hr).continuous⟩
end QEC.Coding.TannerLiftedProduct


