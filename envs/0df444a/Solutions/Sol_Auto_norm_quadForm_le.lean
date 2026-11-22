-- Prove2me | solution 1 for Auto.norm_quadForm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:26.707716+00:00
-- url     : https://prove2.me/submissions/2de0a7cf-ae43-4220-951e-6868bf25d347

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace Auto
theorem _root_.solution {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (v : κ → ℂ) :
    ‖∑ j, ∑ k, star (v j) * D j k * v k‖ ≤ d * ∑ j, ‖v j‖ ^ 2 := by
  set w : κ → ℂ := D *ᵥ v
  have e1 : ∑ j, ∑ k, star (v j) * D j k * v k = ∑ j, star (v j) * w j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hw : ∑ j, ‖w j‖ ^ 2 ≤ d ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hDd).2 v
    have e2 : star v ⬝ᵥ ((((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ)) - D * D) *ᵥ v) = ((d ^ 2 * ∑ j, ‖v j‖ ^
        2 - ∑ j, ‖w j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec]
      have ha : star v ⬝ᵥ ((d ^ 2 : ℝ) • v) = ((d ^ 2 * ∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Pi.smul_apply, Pi.star_apply, Complex.real_smul, RCLike.star_def]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, Complex.conj_mul']
      have hb : star v ⬝ᵥ (D *ᵥ (D *ᵥ v)) = ((∑ j, ‖w j‖ ^ 2 : ℝ) : ℂ) := by
        rw [Matrix.dotProduct_mulVec, show star v ᵥ* D = star w by
          rw [Matrix.star_mulVec, hD.eq]]
        simp only [dotProduct, Pi.star_apply, RCLike.star_def]
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm, Complex.mul_conj']
      rw [ha, hb]; push_cast; ring
    rw [e2] at hq
    have := (Complex.nonneg_iff.1 hq).1
    simp only [Complex.ofReal_re] at this
    linarith
  rw [e1]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, norm_star]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have hS : 0 ≤ ∑ j, ‖v j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc √(∑ j, ‖v j‖ ^ 2) * √(∑ j, ‖w j‖ ^ 2) ≤ √(∑ j, ‖v j‖ ^ 2) * √(d ^ 2 * ∑ j, ‖v j‖ ^ 2) :=
        by gcongr
    _ = d * ∑ j, ‖v j‖ ^ 2 := by
        rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd, ← mul_assoc, mul_comm _ d, mul_assoc,
          Real.mul_self_sqrt hS]
end Auto
