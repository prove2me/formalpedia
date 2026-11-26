-- Prove2me | solution 1 for Auto.sqrtGaussianDecay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:18:34.134891+00:00
-- url     : https://prove2.me/submissions/7a116287-cc20-4487-a0a4-6129d9ef17e9

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
public import Theorems.Thm_Auto_aux_sqrtGaussianDecayKernel_le_seventeen_bracket_sq
public import Theorems.Thm_Auto_aux_sqrtGaussianDecayKernel_nonneg
public import Theorems.Thm_Auto_aux_sqrtGaussianDecayKernel_memW0

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    MemW0 aux_sqrtGaussianDecayKernel ∧
      ∀ x : ℝ, 0 ≤ aux_sqrtGaussianDecayKernel x ∧
        aux_sqrtGaussianDecayKernel x ≤
          C_squareRootGaussianDecay * bracketBump x ^ 2 := by
  refine ⟨aux_sqrtGaussianDecayKernel_memW0, ?_⟩
  intro x
  refine ⟨aux_sqrtGaussianDecayKernel_nonneg x, ?_⟩
  rw [C_squareRootGaussianDecay]
  exact aux_sqrtGaussianDecayKernel_le_seventeen_bracket_sq x
end Auto
