-- Prove2me | solution 1 for Auto.aux_sqrtGaussianDecayKernel_memW0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:28.323924+00:00
-- url     : https://prove2.me/submissions/77f3f49d-fe96-4928-b596-353145180e83

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
public import Theorems.Thm_Auto_aux_sqrtGaussianKernel_continuous
public import Theorems.Thm_Auto_aux_bracketBump_sq_le_inv_one_add_sq
public import Theorems.Thm_Auto_aux_wienerEnvelope_sqrtGaussianDecayKernel_le_hundredSixty_bracket_sq
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_continuous_wienerEnvelope


set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution : MemW0 aux_sqrtGaussianDecayKernel := by
  have hcont : Continuous aux_sqrtGaussianDecayKernel := by
    exact Complex.continuous_re.comp aux_sqrtGaussianKernel_continuous
  refine ⟨hcont, ?_⟩
  have hmajorant : Integrable (fun x : ℝ => 160 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 160
  refine hmajorant.mono_nonneg
    (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hcont zero_le_one x)
    (ae_of_all _ fun x => ?_)
  calc
    wienerEnvelope aux_sqrtGaussianDecayKernel 1 x ≤
        160 * bracketBump x ^ 2 :=
      aux_wienerEnvelope_sqrtGaussianDecayKernel_le_hundredSixty_bracket_sq x
    _ ≤ 160 * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (aux_bracketBump_sq_le_inv_one_add_sq x) (by norm_num)
end Auto
