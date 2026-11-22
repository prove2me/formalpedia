-- Prove2me | solution 1 for Auto.continuous_Kern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:38:26.80616+00:00
-- url     : https://prove2.me/submissions/070d2c50-0062-4e3c-9061-df93f6375a96

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_Kern_eq
public import Theorems.Thm_Auto_continuousOn_kernIntegrand_joint

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
open Auto
noncomputable section
namespace Auto
theorem _root_.solution (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Continuous (Kern m a b) := by
  have e : Kern m a b = fun t => ∫ s in a..b, kernIntegrand m (max a s) t := by
    funext t
    rw [Kern_eq]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hab] at hs
    simp [max_eq_right hs.1]
  rw [e]
  have hc : Continuous fun z : ℝ × ℝ => kernIntegrand m (max a z.2) z.1 :=
    (continuousOn_kernIntegrand_joint m).comp_continuous
      ((continuous_const.max continuous_snd).prodMk continuous_fst)
      fun z => lt_of_lt_of_le ha (le_max_left _ _)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun t s => kernIntegrand m (max a s) t) hc a b
end Auto
