-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:35:52.097991+00:00
-- url     : https://prove2.me/theorems/7403a107-e00e-4e8b-8c43-5fa2dd3f2bd1
-- title:
--   Gaussian smoothing of a Borell density
-- statement:
--   For a finite-dimensional inner-product space $V$, `kernel s x` is the unnormalized Gaussian $e^{-s\|x\|^2}$, `mass s=(\pi/s)^{\dim(V)/2}$, and `normalizedKernel` is the corresponding probability density for $s>0$. `gaussianLaw` and `smoothedLaw` define the normalized Gaussian law and its convolution with a measure, with the stated probability and density identities. For a probability law with Borell density $\rho$, `raw` and `normalizedRaw` are the extended-real convolution integrals, `normalizedDensity` is the `toReal` of `normalizedRaw`, and the bundle proves positivity, finiteness, measurability, log-concavity, continuity, and smoothness of the resulting density and convexity of `potential=-\log(\text{normalizedDensity})$; it also includes the auxiliary derivative and uniform-derivative estimates.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Basic.lean#L33-L1143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace GaussianSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
/-- Unnormalized Gaussian smoothing kernel with inverse variance parameter `s`. -/
def kernel (s : ℝ) (x : V) : ℝ := Real.exp (-s * ‖x‖ ^ 2)
/-- The Gaussian kernel has the usual finite-dimensional mass, including
the zero-dimensional case. -/
theorem integral_kernel {s : ℝ} (hs : 0 < s) :
    ∫ x : V, kernel s x = (Real.pi / s) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  simpa only [kernel] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) hs
theorem integrable_kernel {s : ℝ} (hs : 0 < s) :
    Integrable (kernel (V := V) s) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (s : ℂ))
    (by simpa using hs) 0 (0 : V)
  have hnorm := h.norm
  convert hnorm using 1
  funext x
  simp [kernel, Complex.norm_exp]
  left
  norm_cast
/-- Total mass of the unnormalized Gaussian at inverse variance `s`. -/
def mass (s : ℝ) : ℝ :=
  (Real.pi / s) ^ ((Module.finrank ℝ V : ℝ) / 2)
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem mass_pos {s : ℝ} (hs : 0 < s) : 0 < mass (V := V) s := by
  unfold mass
  positivity
/-- The explicit nonnegative Gaussian probability density. -/
def normalizedKernel (s : ℝ) (x : V) : ℝ := kernel s x / mass (V := V) s
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem normalizedKernel_pos {s : ℝ} (hs : 0 < s) (x : V) :
    0 < normalizedKernel s x :=
  div_pos (Real.exp_pos _) (mass_pos hs)
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem normalizedKernel_le_inv_mass {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedKernel s x ≤ (mass (V := V) s)⁻¹ := by
  have hk : kernel s x ≤ 1 := by
    unfold kernel
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (sq_nonneg _)
  calc
    normalizedKernel s x = kernel s x / mass (V := V) s := rfl
    _ ≤ 1 / mass (V := V) s := div_le_div_of_nonneg_right hk (mass_pos hs).le
    _ = _ := one_div _
theorem integrable_normalizedKernel {s : ℝ} (hs : 0 < s) :
    Integrable (normalizedKernel (V := V) s) :=
  (integrable_kernel hs).div_const _
theorem integral_normalizedKernel {s : ℝ} (hs : 0 < s) :
    ∫ x : V, normalizedKernel s x = 1 := by
  rw [show (fun x : V => normalizedKernel s x) =
    (fun x => kernel s x / mass (V := V) s) from rfl,
    integral_div, integral_kernel hs]
  exact div_self (mass_pos hs).ne'
omit [FiniteDimensional ℝ V] in
theorem normalizedKernel_measurable (s : ℝ) :
    Measurable (normalizedKernel (V := V) s) := by
  unfold normalizedKernel kernel
  fun_prop
/-- The centered Gaussian law with inverse variance parameter `s`. -/
def gaussianLaw (s : ℝ) : Measure V :=
  (volume : Measure V).withDensity
    (fun x => ENNReal.ofReal (normalizedKernel s x))
theorem gaussianLaw_probability {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (gaussianLaw (V := V) s) := by
  rw [isProbabilityMeasure_iff]
  change (volume : Measure V).withDensity
    (fun x => ENNReal.ofReal (normalizedKernel s x)) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_normalizedKernel hs)
    (Filter.Eventually.of_forall fun x => (normalizedKernel_pos hs x).le)]
  rw [integral_normalizedKernel hs]
  simp
/-- Convolution of a law with the normalized Gaussian law. -/
def smoothedLaw (ν : Measure V) (s : ℝ) : Measure V :=
  ν.conv (gaussianLaw s)
theorem smoothedLaw_probability {ν : Measure V} [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (smoothedLaw ν s) := by
  let _ := gaussianLaw_probability (V := V) hs
  unfold smoothedLaw
  infer_instance
/-- The normalized convolution law has its actual Haar density. -/
theorem smoothedLaw_eq_withDensity {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) :
    smoothedLaw ν s = (volume : Measure V).withDensity
      (lconvolution (fun x => ENNReal.ofReal (ρ x))
        (fun x => ENNReal.ofReal (normalizedKernel s x)) volume) := by
  unfold smoothedLaw gaussianLaw
  rw [← hρ.withDensity_eq]
  exact conv_withDensity_eq_lconvolution hρ.measurable.ennreal_ofReal
    (normalizedKernel_measurable s).ennreal_ofReal
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem kernel_pos (s : ℝ) (x : V) : 0 < kernel s x := Real.exp_pos _
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem kernel_measurable (s : ℝ) : Measurable (kernel (V := V) s) := by
  unfold kernel
  fun_prop
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Gaussian factor is log-concave for every nonnegative inverse variance. -/
theorem kernel_logConcave {s : ℝ} (hs : 0 ≤ s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    kernel s x ^ t * kernel s y ^ (1 - t) ≤
      kernel s (t • x + (1 - t) • y) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  have hcv : ConvexOn ℝ univ (fun z : V => ‖z‖ ^ 2) :=
    (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2)
  have hnorm := hcv.2 (mem_univ x) (mem_univ y) ht0.le ht1'
    (by linarith : t + (1 - t) = 1)
  have hmul := mul_le_mul_of_nonneg_left hnorm hs
  simp only [smul_eq_mul] at hmul
  have harg : (-s * ‖x‖ ^ 2) * t + (-s * ‖y‖ ^ 2) * (1 - t) ≤
      -s * ‖t • x + (1 - t) • y‖ ^ 2 := by
    calc
      (-s * ‖x‖ ^ 2) * t + (-s * ‖y‖ ^ 2) * (1 - t)
          = -(s * (t * ‖x‖ ^ 2 + (1 - t) * ‖y‖ ^ 2)) := by ring
      _ ≤ -(s * ‖t • x + (1 - t) • y‖ ^ 2) := neg_le_neg hmul
      _ = _ := by ring
  unfold kernel
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr harg
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem normalizedKernel_logConcave {s : ℝ} (hs : 0 < s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedKernel s x ^ t * normalizedKernel s y ^ (1 - t) ≤
      normalizedKernel s (t • x + (1 - t) • y) := by
  let m := mass (V := V) s
  have hm : 0 < m := mass_pos hs
  have hden : m ^ t * m ^ (1 - t) = m := by
    rw [← Real.rpow_add hm]
    simp
  unfold normalizedKernel
  rw [Real.div_rpow (kernel_pos s x).le hm.le,
    Real.div_rpow (kernel_pos s y).le hm.le]
  calc
    kernel s x ^ t / m ^ t * (kernel s y ^ (1 - t) / m ^ (1 - t))
        = (kernel s x ^ t * kernel s y ^ (1 - t)) /
            (m ^ t * m ^ (1 - t)) := by ring
    _ = (kernel s x ^ t * kernel s y ^ (1 - t)) / m := by rw [hden]
    _ ≤ kernel s (t • x + (1 - t) • y) / m :=
      div_le_div_of_nonneg_right (kernel_logConcave hs.le x y ht0 ht1) hm.le
/-- The extended-real Gaussian factor, in the convention of the convolution integral. -/
def ekernel (s : ℝ) (x : V) : ENNReal := ENNReal.ofReal (kernel s x)
/-- The extended-real normalized Gaussian factor. -/
def normalizedEkernel (s : ℝ) (x : V) : ENNReal :=
  ENNReal.ofReal (normalizedKernel s x)
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem ekernel_pos (s : ℝ) (x : V) : 0 < ekernel s x :=
  ENNReal.ofReal_pos.mpr (kernel_pos s x)
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem ekernel_le_one {s : ℝ} (hs : 0 ≤ s) (x : V) : ekernel s x ≤ 1 := by
  rw [ekernel, ENNReal.ofReal_le_one]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _)
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem ekernel_measurable (s : ℝ) : Measurable (ekernel (V := V) s) :=
  (kernel_measurable s).ennreal_ofReal
omit [FiniteDimensional ℝ V] in
theorem normalizedEkernel_measurable (s : ℝ) :
    Measurable (normalizedEkernel (V := V) s) :=
  (normalizedKernel_measurable s).ennreal_ofReal
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem normalizedEkernel_logConcave {s : ℝ} (hs : 0 < s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedEkernel s x ^ t * normalizedEkernel s y ^ (1 - t) ≤
      normalizedEkernel s (t • x + (1 - t) • y) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  rw [normalizedEkernel, normalizedEkernel, normalizedEkernel,
    ENNReal.ofReal_rpow_of_nonneg (normalizedKernel_pos hs x).le ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (normalizedKernel_pos hs y).le ht1',
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (normalizedKernel_pos hs x).le t)]
  exact ENNReal.ofReal_le_ofReal (normalizedKernel_logConcave hs x y ht0 ht1)
/-- The raw Gaussian convolution of a Borell density. It is kept extended-valued
until pointwise finite mass has been separately proved. -/
def raw (ρ : V → ℝ) (s : ℝ) (x : V) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (ρ y) * ekernel s (x - y) ∂(volume : Measure V)
/-- The pointwise density of the convolution with the normalized Gaussian. -/
def normalizedRaw (ρ : V → ℝ) (s : ℝ) (x : V) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (ρ y) * normalizedEkernel s (x - y) ∂(volume : Measure V)
theorem normalizedRaw_eq_raw_div {ρ : V → ℝ} (hρ : Measurable ρ)
    {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedRaw ρ s x = raw ρ s x / ENNReal.ofReal (mass (V := V) s) := by
  have hm := mass_pos (V := V) hs
  have hf : Measurable (fun y : V => ENNReal.ofReal (ρ y) * ekernel s (x - y)) :=
    hρ.ennreal_ofReal.mul
      ((ekernel_measurable s).comp (measurable_const.sub measurable_id))
  unfold normalizedRaw raw
  simp_rw [normalizedEkernel, normalizedKernel]
  simp_rw [ENNReal.ofReal_div_of_pos hm]
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  simp only [ekernel] at hf ⊢
  rw [lintegral_mul_const _ hf]
/-- The normalized pointwise convolution is the density of the probability-law
convolution, rather than only a formal integral. -/
theorem smoothedLaw_eq_withDensity_normalizedRaw {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) :
    smoothedLaw ν s = (volume : Measure V).withDensity (normalizedRaw ρ s) := by
  rw [smoothedLaw_eq_withDensity hρ s]
  congr 1
  funext x
  unfold normalizedRaw lconvolution
  refine lintegral_congr fun y => ?_
  congr 1
  simp [normalizedEkernel, sub_eq_add_neg, add_comm]
theorem raw_measurable {ρ : V → ℝ} (hρ : Measurable ρ) (s : ℝ) :
    Measurable (raw ρ s) := by
  have hprod : Measurable (fun p : V × V =>
      ENNReal.ofReal (ρ p.2) * ekernel s (p.1 - p.2)) :=
    (hρ.comp measurable_snd).ennreal_ofReal.mul
      ((ekernel_measurable s).comp (measurable_fst.sub measurable_snd))
  exact hprod.lintegral_prod_right
theorem normalizedRaw_measurable {ρ : V → ℝ} (hρ : Measurable ρ)
    {s : ℝ} (hs : 0 < s) : Measurable (normalizedRaw ρ s) := by
  have hEq : normalizedRaw ρ s =
      fun x => raw ρ s x / ENNReal.ofReal (mass (V := V) s) := by
    funext x
    exact normalizedRaw_eq_raw_div hρ hs x
  rw [hEq]
  exact (raw_measurable hρ s).div_const _
/-- The raw convolution can be integrated against the original law. -/
theorem raw_eq_lintegral {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) (x : V) :
    raw ρ s x = ∫⁻ y, ekernel s (x - y) ∂ν := by
  have hm : Measurable (fun y : V => ekernel s (x - y)) :=
    (ekernel_measurable s).comp (measurable_const.sub measurable_id)
  rw [← hρ.withDensity_eq,
    lintegral_withDensity_eq_lintegral_mul (volume : Measure V)
      hρ.measurable.ennreal_ofReal hm]
  rfl
theorem normalizedRaw_eq_lintegral {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) (x : V) :
    normalizedRaw ρ s x = ∫⁻ y, normalizedEkernel s (x - y) ∂ν := by
  have hm : Measurable (fun y : V => normalizedEkernel s (x - y)) :=
    (normalizedEkernel_measurable s).comp (measurable_const.sub measurable_id)
  rw [← hρ.withDensity_eq,
    lintegral_withDensity_eq_lintegral_mul (volume : Measure V)
      hρ.measurable.ennreal_ofReal hm]
  rfl
/-- Gaussian convolution of a probability density has finite value at every point. -/
theorem raw_le_one {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 ≤ s) (x : V) :
    raw ρ s x ≤ 1 := by
  rw [raw_eq_lintegral hρ]
  calc
    (∫⁻ y, ekernel s (x - y) ∂ν) ≤ ∫⁻ _ : V, (1 : ENNReal) ∂ν :=
      lintegral_mono (fun y => ekernel_le_one hs (x - y))
    _ = 1 := by simp
/-- Gaussian convolution of a probability density is positive at every point. -/
theorem raw_pos {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) (x : V) :
    0 < raw ρ s x := by
  rw [raw_eq_lintegral hρ]
  have hm : Measurable (fun y : V => ekernel s (x - y)) :=
    (ekernel_measurable s).comp (measurable_const.sub measurable_id)
  rw [lintegral_pos_iff_support hm]
  have hsupp : Function.support (fun y : V => ekernel s (x - y)) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ekernel_pos s (x - y)).ne'
  rw [hsupp]
  simp
theorem raw_lt_top {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 ≤ s) (x : V) :
    raw ρ s x < ⊤ :=
  lt_of_le_of_lt (raw_le_one hρ hs x) (by simp)
theorem normalizedRaw_pos {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    0 < normalizedRaw ρ s x := by
  rw [normalizedRaw_eq_raw_div hρ.measurable hs]
  exact ENNReal.div_pos (raw_pos hρ s x).ne'
    ENNReal.ofReal_ne_top
theorem normalizedRaw_lt_top {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedRaw ρ s x < ⊤ := by
  rw [normalizedRaw_eq_raw_div hρ.measurable hs]
  exact ENNReal.div_lt_top (raw_lt_top hρ hs.le x).ne
    (ENNReal.ofReal_pos.mpr (mass_pos hs)).ne'
/-- Real density of the normalized convolution probability law. -/
def normalizedDensity (ρ : V → ℝ) (s : ℝ) (x : V) : ℝ :=
  (normalizedRaw ρ s x).toReal
theorem normalizedDensity_pos {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    0 < normalizedDensity ρ s x :=
  ENNReal.toReal_pos (normalizedRaw_pos hρ hs x).ne'
    (normalizedRaw_lt_top hρ hs x).ne
theorem normalizedDensity_measurable {ρ : V → ℝ} (hρ : Measurable ρ)
    {s : ℝ} (hs : 0 < s) : Measurable (normalizedDensity ρ s) :=
  (normalizedRaw_measurable hρ hs).ennreal_toReal
theorem normalizedDensity_eq_integral {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedDensity ρ s x = ∫ y, normalizedKernel s (x - y) ∂ν := by
  have hm : Measurable (fun y : V => normalizedKernel s (x - y)) :=
    (normalizedKernel_measurable s).comp (measurable_const.sub measurable_id)
  have h := integral_eq_lintegral_of_nonneg_ae
    (μ := ν) (f := fun y : V => normalizedKernel s (x - y))
    (Filter.Eventually.of_forall fun y => (normalizedKernel_pos hs (x - y)).le)
    hm.aestronglyMeasurable
  simpa only [normalizedDensity, normalizedRaw_eq_lintegral hρ s x,
    normalizedEkernel] using h.symm
theorem normalizedDensity_continuous {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : Continuous (normalizedDensity ρ s) := by
  have hk : Continuous (normalizedKernel (V := V) s) := by
    unfold normalizedKernel kernel
    fun_prop
  have hcont : Continuous (fun x : V =>
      ∫ y, normalizedKernel s (x - y) ∂ν) := by
    apply continuous_of_dominated
      (bound := fun _ : V => (mass (V := V) s)⁻¹)
    · intro x
      exact ((normalizedKernel_measurable s).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (normalizedKernel_pos hs (x - y))]
        exact normalizedKernel_le_inv_mass hs (x - y)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y =>
        hk.comp (continuous_id.sub continuous_const)
  have heq : (fun x : V => ∫ y, normalizedKernel s (x - y) ∂ν) =
      normalizedDensity ρ s := by
    funext x
    exact (normalizedDensity_eq_integral hρ hs x).symm
  rw [heq] at hcont
  exact hcont
theorem normalizedRaw_logConcave {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s)
    (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedRaw ρ s x ^ t * normalizedRaw ρ s y ^ (1 - t) ≤
      normalizedRaw ρ s (t • x + (1 - t) • y) := by
  let p : V → ENNReal := fun z => ENNReal.ofReal (ρ z)
  have hpLC (a b : V) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
      p a ^ u * p b ^ (1 - u) ≤ p (u • a + (1 - u) • b) := by
    have hu1' : 0 ≤ 1 - u := by linarith
    dsimp [p]
    rw [ENNReal.ofReal_rpow_of_nonneg (hρ.nonneg a) hu0.le,
      ENNReal.ofReal_rpow_of_nonneg (hρ.nonneg b) hu1',
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hρ.nonneg a) u)]
    exact ENNReal.ofReal_le_ofReal (hρ.logConcave a b u hu0 hu1)
  exact Analysis.lintegral_mul_translate_logConcave hρ.measurable.ennreal_ofReal
    (normalizedEkernel_measurable s) hpLC
    (normalizedEkernel_logConcave hs) x y ht0 ht1
theorem normalizedDensity_logConcave {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedDensity ρ s x ^ t * normalizedDensity ρ s y ^ (1 - t) ≤
      normalizedDensity ρ s (t • x + (1 - t) • y) := by
  unfold normalizedDensity
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (normalizedRaw_lt_top hρ hs _).ne
    (normalizedRaw_logConcave hρ hs x y ht0 ht1)
/-- The real, strictly positive, log-concave function is the density of the
normalized Gaussian convolution probability law. -/
theorem smoothedLaw_eq_withDensity_normalizedDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    smoothedLaw ν s = (volume : Measure V).withDensity
      (fun x => ENNReal.ofReal (normalizedDensity ρ s x)) := by
  rw [smoothedLaw_eq_withDensity_normalizedRaw hρ s]
  congr 1
  funext x
  exact (ENNReal.ofReal_toReal (normalizedRaw_lt_top hρ hs x).ne).symm
/-- The Gaussian convolution probability law has a continuous, everywhere
positive Borell density representative. This does not assert smoothness. -/
theorem normalizedDensity_isBorellDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    IsBorellDensity (smoothedLaw ν s) volume (normalizedDensity ρ s) := by
  refine ⟨normalizedDensity_measurable hρ.measurable hs,
    (fun x => (normalizedDensity_pos hρ hs x).le),
    (normalizedDensity_continuous hρ hs).upperSemicontinuous,
    (fun x y t ht0 ht1 => normalizedDensity_logConcave hρ hs x y ht0 ht1), ?_⟩
  exact (smoothedLaw_eq_withDensity_normalizedDensity hρ hs).symm
/-- The normalized Gaussian convolution as a probability measure object. -/
def smoothedProbabilityLaw (ν : ProbabilityMeasure V) (s : ℝ)
    (hs : 0 < s) : ProbabilityMeasure V :=
  ⟨smoothedLaw (ν : Measure V) s, smoothedLaw_probability hs⟩
/-- Continuous convex potential for the normalized Gaussian convolution law. -/
def potential (ρ : V → ℝ) (s : ℝ) (x : V) : ℝ :=
  -Real.log (normalizedDensity ρ s x)
theorem potential_convex {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ConvexOn ℝ univ (potential ρ s) := by
  have hB := normalizedDensity_isBorellDensity hρ hs
  have hpos : {x : V | 0 < normalizedDensity ρ s x} = univ := by
    ext x
    simp [normalizedDensity_pos hρ hs x]
  have hconc := hB.concaveOn_log
  rw [hpos] at hconc
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hconc.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  dsimp [potential]
  linarith
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
 theorem kernel_hasFDerivAt (s : ℝ) (z : V) :
    HasFDerivAt (normalizedKernel (V := V) s)
      ((-2 * s * normalizedKernel s z) • innerSL ℝ z) z := by
  have h0 : HasFDerivAt (fun z : V => ‖z‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h1 : HasFDerivAt (fun z : V => -s * ‖z‖ ^ 2)
      (-s • (2 • innerSL ℝ z)) z := h0.const_mul (-s)
  have h2 := h1.exp
  have h3 := h2.const_mul ((mass (V := V) s)⁻¹)
  have hfun : normalizedKernel (V := V) s =
      (fun y => (mass (V := V) s)⁻¹ * Real.exp (-s * ‖y‖ ^ 2)) := by
    funext y
    simp [normalizedKernel, kernel, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have heq : ((-2 * s * normalizedKernel s z) • innerSL ℝ z) =
      ((mass (V := V) s)⁻¹ • Real.exp (-s * ‖z‖ ^ 2) • -s • 2 • innerSL ℝ z) := by
    ext w
    simp only [smul_apply, smul_eq_mul]
    simp [normalizedKernel, kernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hfun] at heq
  rw [heq]
  exact h3
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
 theorem kernel_fderiv_norm_le (s : ℝ) (hs : 0 < s) (z : V) :
    ‖fderiv ℝ (normalizedKernel (V := V) s) z‖ ≤
      2 * s / mass (V := V) s * (Real.sqrt s)⁻¹ := by
  rw [(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_hasFDerivAt s z).fderiv, norm_smul, Real.norm_eq_abs,
    show -2 * s * normalizedKernel s z = -(2 * s * normalizedKernel s z) by ring,
    abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * s),
    abs_of_pos (normalizedKernel_pos hs z), innerSL_apply_norm]
  have hb := Real.abs_mulExpNegMulSq_le hs (x := ‖z‖)
  change |‖z‖ * Real.exp (-(s * ‖z‖ * ‖z‖))| ≤ (Real.sqrt s)⁻¹ at hb
  have hb' : ‖z‖ * Real.exp (-(s * ‖z‖ * ‖z‖)) ≤ (Real.sqrt s)⁻¹ :=
    (le_abs_self _).trans hb
  calc
    2 * s * normalizedKernel s z * ‖z‖ =
        (2 * s / mass (V := V) s) *
          (‖z‖ * Real.exp (-(s * ‖z‖ * ‖z‖))) := by
            simp [normalizedKernel, kernel]; ring_nf
    _ ≤ (2 * s / mass (V := V) s) * (Real.sqrt s)⁻¹ :=
      mul_le_mul_of_nonneg_left hb' (div_nonneg (by positivity) (mass_pos hs).le)
 def kernelDerivative (s : ℝ) (z : V) : V →L[ℝ] ℝ :=
  (-2 * s * normalizedKernel s z) • innerSL ℝ z
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
 theorem kernelDerivative_continuous (s : ℝ) :
    Continuous (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative (V := V) s) := by
  unfold FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative normalizedKernel kernel
  fun_prop
 theorem density_hasFDerivAt {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) (x : V) :
    HasFDerivAt (normalizedDensity ρ s)
      (∫ y, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x - y) ∂ν) x := by
  have hInt (x : V) : Integrable (fun y : V => normalizedKernel s (x - y)) ν := by
    apply Integrable.mono' (integrable_const ((mass (V := V) s)⁻¹))
      ((normalizedKernel_measurable s).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      change ‖normalizedKernel s (x-y)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (normalizedKernel_pos hs (x-y))]
      exact normalizedKernel_le_inv_mass hs (x-y)
  have hDeriv (x y : V) : HasFDerivAt
      (fun x : V => normalizedKernel s (x-y)) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x-y)) x := by
    have h := (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_hasFDerivAt s (x-y)).comp x (hasFDerivAt_sub_const y)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative] using h
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y : V => normalizedKernel s (x-y))
    (F' := fun x y => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x-y))
    (s := Set.univ) (bound := fun _ : V =>
      2 * s / mass (V := V) s * (Real.sqrt s)⁻¹)
    (μ := ν) (x₀ := x)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x =>
      ((normalizedKernel_measurable s).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (hInt x)
    ((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative_continuous s).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y x _ => by
      simpa only [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative, ← (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_hasFDerivAt s (x-y)).fderiv] using
        FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_fderiv_norm_le s hs (x-y))
    (integrable_const _)
    (Filter.Eventually.of_forall fun y x _ => hDeriv x y)
  have heq : normalizedDensity ρ s =
      (fun x => ∫ y, normalizedKernel s (x-y) ∂ν) := by
    funext x
    exact normalizedDensity_eq_integral hρ hs x
  rw [heq]
  exact h
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
 theorem kernelDerivative_fderiv_norm_le (s : ℝ) (hs : 0 < s) (z : V) :
    ‖fderiv ℝ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s) z‖ ≤ 6 * s / mass (V := V) s := by
  have hc := (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_hasFDerivAt s z).const_mul (-2 * s)
  have hi := (innerSL ℝ : V →L[ℝ] (V →L[ℝ] ℝ)).hasFDerivAt (x := z)
  rw [show fderiv ℝ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s) z = _ from (hc.smul hi).fderiv]
  have hc_bound : |-2 * s * normalizedKernel s z| ≤
      2 * s / mass (V := V) s := by
    rw [show -2 * s * normalizedKernel s z = -(2 * s * normalizedKernel s z) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) (normalizedKernel_pos hs z).le)]
    simpa [div_eq_mul_inv, mul_assoc] using
      (mul_le_mul_of_nonneg_left (normalizedKernel_le_inv_mass hs z) (by positivity : 0 ≤ 2 * s))
  have hfirst : ‖(-2 * s * normalizedKernel s z) • (innerSL ℝ : V →L[ℝ] (V →L[ℝ] ℝ))‖ ≤
      2 * s / mass (V := V) s := by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (by positivity) (mass_pos hs).le) ?_
    intro w
    change ‖(-2 * s * normalizedKernel s z) • innerSL ℝ w‖ ≤
      (2 * s / mass (V := V) s) * ‖w‖
    rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_right hc_bound (norm_nonneg _)
  have htail : s * ‖z‖ ^ 2 * normalizedKernel s z ≤
      (mass (V := V) s)⁻¹ := by
    have ht : s * ‖z‖ ^ 2 ≤ Real.exp (s * ‖z‖ ^ 2) := by
      nlinarith [Real.add_one_le_exp (s * ‖z‖ ^ 2)]
    have hmul : (s * ‖z‖ ^ 2) * Real.exp (-(s * ‖z‖ ^ 2)) ≤ 1 := by
      rw [Real.exp_neg]
      exact (div_le_one (Real.exp_pos _)).mpr ht
    calc
      s * ‖z‖ ^ 2 * normalizedKernel s z =
          ((s * ‖z‖ ^ 2) * Real.exp (-(s * ‖z‖ ^ 2))) / mass (V := V) s := by
            simp [normalizedKernel, kernel]; ring_nf
      _ ≤ 1 / mass (V := V) s :=
        div_le_div_of_nonneg_right hmul (mass_pos hs).le
      _ = _ := one_div _
  have hsecond : ‖((-2 * s) • ((-2 * s * normalizedKernel s z) • innerSL ℝ z)).smulRight
      (innerSL ℝ z)‖ ≤ 4 * s / mass (V := V) s := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, innerSL_apply_norm,
      show -2 * s = -(2 * s) by ring, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ 2 * s),
      abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * s),
      abs_of_pos (normalizedKernel_pos hs z)]
    calc
      2 * s * (2 * s * normalizedKernel s z * ‖z‖) * ‖z‖ =
          4 * s * (s * ‖z‖ ^ 2 * normalizedKernel s z) := by ring
      _ ≤ 4 * s * (mass (V := V) s)⁻¹ :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = 4 * s / mass (V := V) s := by ring
  calc
    _ ≤ ‖(-2 * s * normalizedKernel s z) • (innerSL ℝ : V →L[ℝ] (V →L[ℝ] ℝ))‖ +
        ‖((-2 * s) • ((-2 * s * normalizedKernel s z) • innerSL ℝ z)).smulRight
          (innerSL ℝ z)‖ := by
      let A : V →L[ℝ] (V →L[ℝ] ℝ) := (-2 * s * normalizedKernel s z) • innerSL ℝ
      let B : V →L[ℝ] (V →L[ℝ] ℝ) :=
        ((-2 * s) • ((-2 * s * normalizedKernel s z) • innerSL ℝ z)).smulRight
          (innerSL ℝ z)
      change ‖A + B‖ ≤ ‖A‖ + ‖B‖
      exact norm_add_le A B
    _ ≤ (2 * s / mass (V := V) s) + (4 * s / mass (V := V) s) :=
      add_le_add hfirst hsecond
    _ = 6 * s / mass (V := V) s := by ring
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
 theorem kernelDerivative_contDiff (s : ℝ) :
    ContDiff ℝ 2 (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative (V := V) s) := by
  have hn : ContDiff ℝ 2 (fun z : V => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hnorm : ContDiff ℝ 2 (fun z : V => -s * ‖z‖ ^ 2) := by
    simpa only [smul_eq_mul] using (ContDiff.const_smul (-s) hn)
  have he : ContDiff ℝ 2 (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) :=
    Real.contDiff_exp.comp hnorm
  have hk : ContDiff ℝ 2 (normalizedKernel (V := V) s) := by
    have h := he.div_const (mass (V := V) s)
    have hfun : normalizedKernel (V := V) s =
        (fun z : V => Real.exp (-s * ‖z‖ ^ 2) / mass (V := V) s) := by
      funext z
      rfl
    rw [hfun]
    exact h
  unfold FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative
  exact ((ContDiff.const_smul (-2 * s) hk).smul (innerSL ℝ).contDiff)
 theorem derivativeIntegral_contDiff_one {ν : Measure V} [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 1 (fun x : V => ∫ y, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x-y) ∂ν) := by
  let K : ℝ := 6 * s / mass (V := V) s
  have hkcont : Continuous (fun z : V => fderiv ℝ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s) z) :=
    (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative_contDiff s).continuous_fderiv (by norm_num)
  have hbound (z : V) : ‖FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s z‖ ≤
      2 * s / mass (V := V) s * (Real.sqrt s)⁻¹ := by
    simpa only [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative, ← (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_hasFDerivAt s z).fderiv] using
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_fderiv_norm_le s hs z
  have hint (x : V) : Integrable (fun y : V => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x-y)) ν := by
    apply Integrable.mono' (integrable_const (2 * s / mass (V := V) s * (Real.sqrt s)⁻¹))
      (((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative_continuous s).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => hbound (x-y)
  have hdiff (x y : V) : HasFDerivAt
      (fun x : V => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x-y))
      (fderiv ℝ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s) (x-y)) x := by
    have h := ((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative_contDiff s).differentiable (by norm_num) (x-y)).hasFDerivAt.comp
      x (hasFDerivAt_sub_const y)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h
  have hAt (x : V) : HasFDerivAt
      (fun x : V => ∫ y, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x-y) ∂ν)
      (∫ y, fderiv ℝ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s) (x-y) ∂ν) x := by
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x y : V => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s (x-y))
      (F' := fun x y => fderiv ℝ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s) (x-y))
      (s := Set.univ) (bound := fun _ : V => K)
      (μ := ν) (x₀ := x)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun x =>
        (((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative_continuous s).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable))
      (hint x)
      ((hkcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y x _ => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative_fderiv_norm_le s hs (x-y))
      (integrable_const _)
      (Filter.Eventually.of_forall fun y x _ => hdiff x y)
  have hcont : Continuous (fun x : V =>
      ∫ y, fderiv ℝ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative s) (x-y) ∂ν) := by
    apply continuous_of_dominated (bound := fun _ : V => K)
    · intro x
      exact (hkcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun y => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernelDerivative_fderiv_norm_le s hs (x-y)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y =>
        hkcont.comp (continuous_id.sub continuous_const)
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨_, hcont, hAt⟩
/-- The actual normalized Gaussian convolution density is twice continuously differentiable. -/
theorem normalizedDensity_contDiff_two {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ 2 (normalizedDensity ρ s) := by
  change ContDiff ℝ (1 + 1) (normalizedDensity ρ s)
  exact contDiff_succ_iff_hasFDerivAt.mpr
    ⟨_, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.derivativeIntegral_contDiff_one hs, fun x => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density_hasFDerivAt hρ hs x⟩
/-- The logarithmic potential of the actual convolution is twice continuously differentiable. -/
theorem potential_contDiff_two {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ 2 (potential ρ s) := by
  unfold potential
  exact ((normalizedDensity_contDiff_two hρ hs).log
    (fun x => (normalizedDensity_pos hρ hs x).ne')).neg
section AllOrderRegularity
open Filter Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
 theorem pow_mul_exp_neg_sq_bounded (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → r ^ n * Real.exp (-b * r ^ 2) ≤ C := by
  let F : ℝ → ℝ := fun r => |r| ^ n * Real.exp (-b * r ^ 2)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hlim : Tendsto F (cocompact ℝ) (𝓝 0) := by
    convert tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (n : ℝ) using 1
    ext r
    simp [F, Real.rpow_natCast]
  have hF1 : 0 < F 1 := by simp [F]; positivity
  have hev : ∀ᶠ r in cocompact ℝ, F r ≤ F 1 := by
    filter_upwards [hlim.eventually (eventually_lt_nhds hF1)] with r hr
    exact hr.le
  obtain ⟨r₀, hr₀⟩ := hF.exists_forall_ge' 1 hev
  refine ⟨F r₀, fun r hr => ?_⟩
  simpa [F, abs_of_nonneg hr] using hr₀ r
 theorem one_add_pow_mul_exp_neg_sq_bounded (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ n * Real.exp (-b * r ^ 2) ≤ C := by
  obtain ⟨C0, h0⟩ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.pow_mul_exp_neg_sq_bounded b hb 0
  obtain ⟨Cn, hn⟩ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.pow_mul_exp_neg_sq_bounded b hb n
  refine ⟨(2 : ℝ) ^ n * (C0 + Cn), fun r hr => ?_⟩
  have hpow : (1 + r) ^ n ≤ (2 : ℝ) ^ n * (1 + r ^ n) := by
    rcases le_total r 1 with h | h
    · calc
        (1 + r) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
        _ ≤ (2 : ℝ) ^ n * (1 + r ^ n) := by
          have hh : (1 : ℝ) ≤ 1 + r ^ n := by nlinarith [pow_nonneg hr n]
          simpa using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (2 : ℝ) ^ n)
    · calc
        (1 + r) ^ n ≤ (2 * r) ^ n := by gcongr; linarith
        _ = (2 : ℝ) ^ n * r ^ n := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ n * (1 + r ^ n) := by gcongr; simp
  have he : 0 ≤ Real.exp (-b * r ^ 2) := (Real.exp_pos _).le
  calc
    _ ≤ ((2 : ℝ) ^ n * (1 + r ^ n)) * Real.exp (-b * r ^ 2) :=
      mul_le_mul_of_nonneg_right hpow he
    _ = (2 : ℝ) ^ n * (Real.exp (-b * r ^ 2) +
      r ^ n * Real.exp (-b * r ^ 2)) := by ring
    _ ≤ (2 : ℝ) ^ n * (C0 + Cn) := by
      gcongr
      · simpa using h0 r hr
      · exact hn r hr
section StructuredSpace
variable {V : Type*}
variable [NormedAddCommGroup V]
section InnerProduct
variable [InnerProductSpace ℝ V]
 theorem gaussian_deriv_poly_bound (s : ℝ) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : V,
      ‖iteratedFDeriv ℝ n (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) z‖ ≤
        C * (1 + ‖z‖) ^ k * Real.exp (-s * ‖z‖ ^ 2) := by
  let f : V → ℝ := fun z => -s * ‖z‖ ^ 2
  have hf : f.HasTemperateGrowth := by
    dsimp [f]
    fun_prop
  obtain ⟨k, C, hC, hbound⟩ := hf.norm_iteratedFDeriv_le_uniform n
  refine ⟨k * n, n.factorial * (1 + C) ^ n, by positivity, fun z => ?_⟩
  have houter : ∀ i, i ≤ n →
      ‖iteratedFDeriv ℝ i Real.exp (f z)‖ ≤ Real.exp (f z) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp]
    simp
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i f z‖ ≤ ((1 + C) * (1 + ‖z‖) ^ k) ^ i := by
    intro i hi hi'
    calc
      _ ≤ C * (1 + ‖z‖) ^ k := hbound i hi' z
      _ ≤ (1 + C) * (1 + ‖z‖) ^ k := by gcongr; simp
      _ ≤ ((1 + C) * (1 + ‖z‖) ^ k) ^ i := by
        apply le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC])
          (by simp [one_le_pow₀]))
        omega
  have h := norm_iteratedFDeriv_comp_le (N := (↑(⊤ : ℕ∞))) Real.contDiff_exp hf.1
    (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) z houter hinner
  convert h using 1
  · rfl
  · simp only [mul_pow, pow_mul, mul_assoc]
    ring
 theorem gaussian_deriv_bound (s : ℝ) (hs : 0 < s) (n : ℕ) :
    ∃ B : ℝ, ∀ z : V,
      ‖iteratedFDeriv ℝ n (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) z‖ ≤ B := by
  obtain ⟨k, C, hC, hpoly⟩ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_deriv_poly_bound (V := V) s n
  obtain ⟨B, hB⟩ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.one_add_pow_mul_exp_neg_sq_bounded s hs k
  refine ⟨C * B, fun z => (hpoly z).trans ?_⟩
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (hB ‖z‖ (norm_nonneg z)) hC)
end InnerProduct
 theorem smooth_integral_of_uniform_derivatives [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [IsProbabilityMeasure ν] (g : V → ℝ)
    (hg : ContDiff ℝ ∞ g)
    (hB : ∀ n : ℕ, ∃ B : ℝ, ∀ z : V,
      ‖iteratedFDeriv ℝ n g z‖ ≤ B) :
    ContDiff ℝ ∞ (fun x : V => ∫ y, g (x-y) ∂ν) := by
  let J (n : ℕ) (x : V) := ∫ y, iteratedFDeriv ℝ n g (x-y) ∂ν
  have hcont (n : ℕ) : Continuous (iteratedFDeriv ℝ n g) :=
    hg.continuous_iteratedFDeriv (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
  have hint (n : ℕ) (x : V) :
      Integrable (fun y : V => iteratedFDeriv ℝ n g (x-y)) ν := by
    obtain ⟨B, hbound⟩ := hB n
    apply Integrable.mono' (integrable_const B)
      ((hcont n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => hbound (x-y)
  have hJn : ∀ m : ℕ, ∀ n : ℕ, ContDiff ℝ m (J n) := by
    intro m
    induction m with
    | zero =>
        intro n
        apply contDiff_zero.mpr
        dsimp [J]
        obtain ⟨B, hbound⟩ := hB n
        apply continuous_of_dominated (bound := fun _ : V => B)
        · intro x
          exact ((hcont n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        · intro x
          exact Filter.Eventually.of_forall fun y => hbound (x-y)
        · exact integrable_const _
        · exact Filter.Eventually.of_forall fun y =>
            (hcont n).comp (continuous_id.sub continuous_const)
    | succ m ih =>
        intro n
        letI : NormedAddCommGroup (V [×(n+1)]→L[ℝ] ℝ) :=
          ContinuousMultilinearMap.normedAddCommGroup'
        letI : NormedSpace ℝ (V [×(n+1)]→L[ℝ] ℝ) :=
          ContinuousMultilinearMap.normedSpace'
        letI : NormedAddCommGroup (V [×n]→L[ℝ] ℝ) :=
          ContinuousMultilinearMap.normedAddCommGroup'
        letI : NormedSpace ℝ (V [×n]→L[ℝ] ℝ) :=
          ContinuousMultilinearMap.normedSpace'
        let L : (V [×(n+1)]→L[ℝ] ℝ) →L[ℝ]
            (V →L[ℝ] (V [×n]→L[ℝ] ℝ)) :=
          { toFun := ContinuousMultilinearMap.curryLeft
            map_add' := by intros; rfl
            map_smul' := by intros; rfl
            cont := (continuousMultilinearCurryLeftEquiv ℝ
              (fun _ : Fin (n+1) => V) ℝ).continuous }
        have hderiv_cont : ContDiff ℝ m (fun x => L (J (n+1) x)) := by
          simpa only [Function.comp_def] using L.contDiff.comp (ih (n+1))
        have hAt (x : V) : HasFDerivAt (J n)
            (L (J (n+1) x)) x := by
          have hfcont : Continuous (fun z : V => fderiv ℝ (iteratedFDeriv ℝ n g) z) := by
            rw [fderiv_iteratedFDeriv]
            exact L.continuous.comp (hcont (n+1))
          have hfbound (z : V) :
              ‖fderiv ℝ (iteratedFDeriv ℝ n g) z‖ ≤ (hB (n+1)).choose := by
            rw [norm_fderiv_iteratedFDeriv]
            exact (hB (n+1)).choose_spec z
          have hdiff (x y : V) : HasFDerivAt
              (fun x : V => iteratedFDeriv ℝ n g (x-y))
              (fderiv ℝ (iteratedFDeriv ℝ n g) (x-y)) x := by
            have hreg : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
              hg.differentiable_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n))
            have h := (hreg (x-y)).hasFDerivAt.comp x (hasFDerivAt_sub_const y)
            simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h
          have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
            (F := fun x y : V => iteratedFDeriv ℝ n g (x-y))
            (F' := fun x y => fderiv ℝ (iteratedFDeriv ℝ n g) (x-y))
            (s := Set.univ) (bound := fun _ : V => (hB (n+1)).choose)
            (μ := ν) (x₀ := x)
            Filter.univ_mem
            (Filter.Eventually.of_forall fun x =>
              ((hcont n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
            (hint n x)
            ((hfcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
            (Filter.Eventually.of_forall fun y x _ => hfbound (x-y))
            (integrable_const _)
            (Filter.Eventually.of_forall fun y x _ => hdiff x y)
          have heq : (∫ y, fderiv ℝ (iteratedFDeriv ℝ n g) (x-y) ∂ν) =
              L (J (n+1) x) := by
            calc
              _ = ∫ y, L (iteratedFDeriv ℝ (n+1) g (x-y)) ∂ν := by
                congr 1
              _ = L (J (n+1) x) := by
                exact L.integral_comp_comm (hint (n+1) x)
          rw [heq] at h
          exact h
        exact contDiff_succ_iff_hasFDerivAt.mpr ⟨_, hderiv_cont, hAt⟩
  apply contDiff_infty.mpr
  intro m
  letI : NormedAddCommGroup (V [×0]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.normedAddCommGroup'
  letI : NormedSpace ℝ (V [×0]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.normedSpace'
  let e := continuousMultilinearCurryFin0 ℝ V ℝ
  have hc : ContDiff ℝ m (fun x => e (J 0 x)) := by
    simpa only [Function.comp_def] using e.contDiff.comp (hJn m 0)
  have heq : (fun x => e (J 0 x)) = (fun x : V => ∫ y, g (x-y) ∂ν) := by
    funext x
    dsimp [J]
    change (∫ y, iteratedFDeriv ℝ 0 g (x-y) ∂ν) (0 : Fin 0 → V) = _
    rw [ContinuousMultilinearMap.integral_apply (hint 0 x)]
    simp only [iteratedFDeriv_zero_apply]
  rw [← heq]
  exact hc
end StructuredSpace
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
 theorem kernel_contDiff_infty (s : ℝ) :
    ContDiff ℝ ∞ (kernel (V := V) s) := by
  have hn : ContDiff ℝ ∞ (fun z : V => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hnorm : ContDiff ℝ ∞ (fun z : V => -s * ‖z‖ ^ 2) := by
    simpa only [smul_eq_mul] using (ContDiff.const_smul (-s) hn)
  exact Real.contDiff_exp.comp hnorm
/-- The actual normalized convolution density is smooth at every positive
inverse variance, with no moment or regularity assumption on the source law. -/
theorem normalizedDensity_contDiff_infty {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (normalizedDensity ρ s) := by
  have hconv : ContDiff ℝ ∞ (fun x : V => ∫ y, kernel s (x-y) ∂ν) := by
    apply FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smooth_integral_of_uniform_derivatives ν (kernel s) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.kernel_contDiff_infty s)
    intro n
    change ∃ B : ℝ, ∀ z : V,
      ‖iteratedFDeriv ℝ n (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) z‖ ≤ B
    exact FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_deriv_bound (V := V) s hs n
  have heq : normalizedDensity ρ s =
      (fun x => (∫ y, kernel s (x-y) ∂ν) / mass (V := V) s) := by
    funext x
    rw [normalizedDensity_eq_integral hρ hs x]
    simp only [normalizedKernel, div_eq_mul_inv, integral_mul_const]
  rw [heq]
  exact hconv.div_const _
/-- The negative logarithm of the actual normalized convolution is smooth,
including on a zero-dimensional ambient space. -/
theorem potential_contDiff_infty {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (potential ρ s) := by
  unfold potential
  exact ((normalizedDensity_contDiff_infty hρ hs).log
    (fun x => (normalizedDensity_pos hρ hs x).ne')).neg
end AllOrderRegularity
end GaussianSmoothing
end LogConcave
end KLS
end FunctionalInequalities


