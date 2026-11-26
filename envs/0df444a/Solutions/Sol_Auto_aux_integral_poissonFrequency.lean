-- Prove2me | solution 1 for Auto.aux_integral_poissonFrequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:30.54241+00:00
-- url     : https://prove2.me/submissions/bc12668f-3c66-4b14-a75b-986e64b41f3a

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
theorem _root_.solution : ∫ ξ : ℝ, aux_poissonFrequency ξ = 2 := by
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
  have hleft_value : (∫ ξ in Set.Iic (0 : ℝ), aux_poissonFrequency ξ) = 1 := by
    calc
      (∫ ξ in Set.Iic (0 : ℝ), aux_poissonFrequency ξ) =
          ∫ ξ in Set.Iic (0 : ℝ), Real.exp ξ := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro ξ hξ
        have hξ' : ξ ≤ 0 := hξ
        simp [aux_poissonFrequency, abs_of_nonpos hξ']
      _ = 1 := integral_exp_Iic_zero
  have hright_value : (∫ ξ in Set.Ioi (0 : ℝ), aux_poissonFrequency ξ) = 1 := by
    calc
      (∫ ξ in Set.Ioi (0 : ℝ), aux_poissonFrequency ξ) =
          ∫ ξ in Set.Ioi (0 : ℝ), Real.exp (-ξ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro ξ hξ
        have hξ' : 0 < ξ := hξ
        simp [aux_poissonFrequency, abs_of_pos hξ']
      _ = 1 := integral_exp_neg_Ioi_zero
  calc
    (∫ ξ : ℝ, aux_poissonFrequency ξ) =
        ∫ ξ in Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ), aux_poissonFrequency ξ := by
      rw [Set.Iic_union_Ioi, setIntegral_univ]
    _ = (∫ ξ in Set.Iic (0 : ℝ), aux_poissonFrequency ξ) +
          ∫ ξ in Set.Ioi (0 : ℝ), aux_poissonFrequency ξ :=
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hleft hright
    _ = 2 := by rw [hleft_value, hright_value]; norm_num
end Auto
