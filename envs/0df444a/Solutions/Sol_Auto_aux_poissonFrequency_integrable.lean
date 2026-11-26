-- Prove2me | solution 1 for Auto.aux_poissonFrequency_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:37:08.970073+00:00
-- url     : https://prove2.me/submissions/77ac0cce-c668-4102-9636-0bcd57249aad

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution : Integrable aux_poissonFrequency := by
  have hleft : IntegrableOn aux_poissonFrequency (Set.Iic (0 : ℝ)) := by
    refine (integrableOn_exp_Iic 0).congr_fun ?_ measurableSet_Iic
    intro ξ hξ
    have hξ' : ξ ≤ 0 := hξ
    simp [aux_poissonFrequency, abs_of_nonpos hξ']
  have hright : IntegrableOn aux_poissonFrequency (Set.Ioi (0 : ℝ)) := by
    refine (integrableOn_exp_neg_Ioi 0).congr_fun ?_ measurableSet_Ioi
    intro ξ hξ
    have hξ' : 0 < ξ := hξ
    simp [aux_poissonFrequency, abs_of_pos hξ']
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi]
  exact hleft.union hright
end Auto
