-- Prove2me | solution 1 for Auto.cyclic_trace_control
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:35:40.141809+00:00
-- url     : https://prove2.me/submissions/cae15535-868c-458b-867c-93fd692738b6

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_cyc_cube_trace
public import Theorems.Thm_Auto_cyc_backward_conj
public import Theorems.Thm_Auto_cyc_cube_le
public import Theorems.Thm_Auto_rowMat_cost_unitary
public import Theorems.Thm_Auto_phaseBlocks_unitary

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
namespace Auto
theorem _root_.solution (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian)
    (hD2 : D2.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ENNReal.ofReal ‖(D0 * W0 * D1 * W1 * D2 * W2).trace‖ ≤ ENNReal.ofReal (5 / 3 * d) * (matCost
      ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) + matCost ((rowMat W1
      W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) + matCost ((rowMat W2 W1)ᴴ *
      rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1)) := by
  set t := (D0 * W0 * D1 * W1 * D2 * W2).trace
  by_cases ht : t = 0
  · rw [ht, norm_zero, ENNReal.ofReal_zero]; exact zero_le
  set c : ℂ := star t / (‖t‖ : ℂ)
  have htn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ht
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg t)]
    exact div_self (norm_ne_zero_iff.2 ht)
  have hct : c * t = (‖t‖ : ℂ) := by
    simp only [c]
    rw [div_mul_eq_mul_div, RCLike.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  set W0' := c • W0
  have ht' : (D0 * W0' * D1 * W1 * D2 * W2).trace = (‖t‖ : ℂ) := by
    simp only [W0', Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    exact hct
  have hcube := cyc_cube_trace W0' W1 W2 D0 D1 D2
  rw [cyc_backward_conj W0' W1 W2 D0 D1 D2 hD0 hD1 hD2, ht'] at hcube
  have h6 : ‖((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0' W1 W2)) ^ 3).trace‖ = 6 * ‖t‖ := by
    rw [hcube, RCLike.star_def, Complex.conj_ofReal]
    rw [show (3 : ℂ) * (‖t‖ : ℂ) + 3 * (‖t‖ : ℂ) = ((6 * ‖t‖ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmain := cyc_cube_le W0' W1 W2 D0 D1 D2 hD0 hD1 hD2 hd h0 h1 h2
  rw [h6] at hmain
  have hR0 : rowMat W0' W2 = rowMat W0 W2 * Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1 := by
    rw [show rowMat W0 W2 * Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1 =
      Matrix.fromCols (W0 * (c • 1) + W2ᴴ * 0) (W0 * 0 + W2ᴴ * 1) from
        Matrix.fromCols_mul_fromBlocks _ _ _ _ _ _]
    simp [rowMat, W0']
  have hR1 : rowMat W1 W0' =
      rowMat W1 W0 * Matrix.fromBlocks 1 0 0 (star c • (1 : Matrix ι ι ℂ)) := by
    rw [show rowMat W1 W0 * Matrix.fromBlocks 1 0 0 (star c • (1 : Matrix ι ι ℂ)) =
      Matrix.fromCols (W1 * 1 + W0ᴴ * 0) (W1 * 0 + W0ᴴ * (star c • 1)) from
        Matrix.fromCols_mul_fromBlocks _ _ _ _ _ _]
    simp [rowMat, W0', Matrix.conjTranspose_smul]
  have hc' : ‖star c‖ = 1 := by rw [norm_star, hc]
  have e0 : matCost ((rowMat W0' W2)ᴴ * rowMat W0' W2) ((rowMat W0' W2)ᴴ * D0 * rowMat W0' W2) =
      matCost ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) := by
    rw [hR0]; exact rowMat_cost_unitary _ _ (by simpa using phaseBlocks_unitary hc true) _
  have e1 : matCost ((rowMat W1 W0')ᴴ * rowMat W1 W0') ((rowMat W1 W0')ᴴ * D1 * rowMat W1 W0') =
      matCost ((rowMat W1 W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) := by
    rw [hR1]; exact rowMat_cost_unitary _ _ (by simpa using phaseBlocks_unitary hc' false) _
  rw [e0, e1] at hmain
  have h6' : ENNReal.ofReal (6 * ‖t‖) = ENNReal.ofReal 6 * ENNReal.ofReal ‖t‖ :=
    ENNReal.ofReal_mul (by norm_num)
  rw [h6'] at hmain
  have h10 : ENNReal.ofReal (10 * d) = ENNReal.ofReal 6 * ENNReal.ofReal (5 / 3 * d) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  rw [h10, mul_assoc] at hmain
  exact (ENNReal.mul_le_mul_iff_right (by simp) ENNReal.ofReal_ne_top).1 hmain
end Auto
