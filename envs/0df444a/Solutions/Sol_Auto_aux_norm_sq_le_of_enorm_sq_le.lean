-- Prove2me | solution 1 for Auto.aux_norm_sq_le_of_enorm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:42.970382+00:00
-- url     : https://prove2.me/submissions/eb4b6617-ce22-4178-ad46-54bf1db3ad65

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (K : ℝ) (hK : 0 ≤ K) (y : F) (x : ∀ i, E i)
    (h : ‖y‖ₑ ^ 2 ≤ ENNReal.ofReal K * ∏ i, ‖x i‖ₑ ^ 2) :
    ‖y‖ ^ 2 ≤ K * ∏ i, ‖x i‖ ^ 2 := by
  have hleft : ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hright : ENNReal.ofReal K * ∏ i, ‖x i‖ₑ ^ 2 =
      ENNReal.ofReal (K * ∏ i, ‖x i‖ ^ 2) := by
    rw [ENNReal.ofReal_mul hK,
      ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ sq_nonneg (‖x i‖))]
    apply congrArg (fun z : ℝ≥0∞ ↦ ENNReal.ofReal K * z)
    apply Finset.prod_congr rfl
    intro i _
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  rw [hleft, hright] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hK (Finset.prod_nonneg fun i _ ↦ sq_nonneg (‖x i‖)))).mp h
end Auto
