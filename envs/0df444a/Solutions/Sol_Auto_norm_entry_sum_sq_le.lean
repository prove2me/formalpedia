-- Prove2me | solution 1 for Auto.norm_entry_sum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:08:28.250452+00:00
-- url     : https://prove2.me/submissions/94c9319a-205e-47a9-bc8b-12ecf1f02340

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_re_diag_le_of_sub_posSemidef

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
theorem _root_.solution {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ}
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (i : κ) :
    ∑ j, ‖D i j‖ ^ 2 ≤ d ^ 2 := by
  have h := re_diag_le_of_sub_posSemidef hDd i
  have e : ((D * D) i i).re = ∑ j, ‖D i j‖ ^ 2 := by
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hD.apply j i, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [e] at h
  simpa [Matrix.smul_apply, Matrix.one_apply_eq, ← Complex.ofReal_pow] using h
end Auto
