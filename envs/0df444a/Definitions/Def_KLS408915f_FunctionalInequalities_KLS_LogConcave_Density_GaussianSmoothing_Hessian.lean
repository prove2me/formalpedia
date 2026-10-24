-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Hessian
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Hessian
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:37:07.18102+00:00
-- url     : https://prove2.me/theorems/b087fa95-07f6-4571-a2e0-b5d739a8c5ea
-- title:
--   Hessian and posterior variance identities for Gaussian smoothing
-- statement:
--   For a probability law with Borell density and $s>0$, the Gaussian posterior is $P_x=\mu.\operatorname{tilted}(-s\|x-\cdot\|^2)$, and the bundle proves that the smoothed potential satisfies $D^2V_s(x)[v,v]=2s\|v\|^2-\operatorname{Var}_{P_x}(2s\langle\cdot-x,v\rangle)=2s\|v\|^2-4s^2\operatorname{Var}_{P_x}(\langle\cdot,v\rangle)$. Consequently, `bilinearIteratedFDerivTwo_potential_le` gives the upper Hessian bound $D^2V_s(x)[v,v]\le2s\|v\|^2$, while `variance_inner_posterior_le` gives $\operatorname{Var}_{P_x}\langle\cdot,v\rangle\le\|v\|^2/(2s)$. Auxiliary declarations establish posterior integrability, exponential moments, and finite second moments.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Hessian.lean#L35-L306 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Hessian`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Hessian`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
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
import Mathlib.Analysis.Calculus.Deriv.Inv
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace GaussianSmoothing
universe u_2
variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
 theorem gaussian_shift_identity (s t : ℝ) (x y v : E) :
    Real.exp (-s * ‖x - y‖ ^ 2) * Real.exp (t * (2 * s * ⟪y - x, v⟫)) =
      Real.exp (s * t ^ 2 * ‖v‖ ^ 2) * Real.exp (-s * ‖x + t • v - y‖ ^ 2) := by
  have heq : x + t • v - y = (x - y) + t • v := by abel
  have hn : ‖x + t • v - y‖ ^ 2 =
      ‖x - y‖ ^ 2 + 2 * t * ⟪x - y, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
    rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  have hi : ⟪y - x, v⟫ = -⟪x - y, v⟫ := by
    rw [show y - x = -(x - y) by abel]
    simp only [inner_neg_left]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hn, hi]
  ring
section PosteriorProbability
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem integrable_shiftedKernel (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x : E) :
    Integrable (fun y => Real.exp (-s * ‖x - y‖ ^ 2)) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    ((by fun_prop : Continuous (fun y : E => Real.exp (-s * ‖x - y‖ ^ 2))).aestronglyMeasurable) ?_
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hs.le) (sq_nonneg _))
theorem isProbabilityMeasure_posterior (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x : E) :
    IsProbabilityMeasure (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) :=
  isProbabilityMeasure_tilted (integrable_shiftedKernel μ hs x)
end PosteriorProbability
section ScoreExponentialMoments
omit [FiniteDimensional ℝ E]
/-- Completing the square gives every signed exponential moment of the score `2s⟪y-x,v⟫` under the
Gaussian posterior `μ.tilted (-s‖x-·‖²)`; no exponential moment of `μ` is needed. -/
theorem integrable_exp_score_posterior (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x v : E) (t : ℝ) :
    Integrable (fun y => Real.exp (t * (2 * s * ⟪y - x, v⟫)))
      (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) := by
  rw [integrable_tilted_iff (integrable_shiftedKernel μ hs x)]
  simpa only [smul_eq_mul, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_shift_identity] using
    (integrable_shiftedKernel μ hs (x + t • v)).const_mul (Real.exp (s * t ^ 2 * ‖v‖ ^ 2))
theorem integrableExpSet_score_posterior (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x v : E) :
    integrableExpSet (fun y => 2 * s * ⟪y - x, v⟫)
      (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact integrable_exp_score_posterior μ hs x v t
end ScoreExponentialMoments
 theorem normalizedDensity_eq_gaussian_weight {μ : Measure E}
    [IsProbabilityMeasure μ] {ρ : E → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x : E) :
    normalizedDensity ρ s x =
      (∫ y, Real.exp (-s * ‖x - y‖ ^ 2) ∂μ) / mass (V := E) s := by
  rw [normalizedDensity_eq_integral hρ hs]
  change (∫ y, Real.exp (-s * ‖x - y‖ ^ 2) / mass (V := E) s ∂μ) = _
  exact integral_div _ _
/-- Along a line, the normalized smoothed density factors into its value at the base point, a
scalar Gaussian factor and the moment generating function of the score under the posterior. -/
theorem normalizedDensity_line_factorization {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x v : E) (t : ℝ) :
    normalizedDensity ρ s (x + t • v) = normalizedDensity ρ s x *
      Real.exp (-s * t ^ 2 * ‖v‖ ^ 2) *
        mgf (fun y => 2 * s * ⟪y - x, v⟫)
          (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) t := by
  let Z : E → ℝ := fun z => ∫ y, Real.exp (-s * ‖z - y‖ ^ 2) ∂μ
  have hZ : 0 < Z x := integral_exp_pos (integrable_shiftedKernel μ hs x)
  have hm : 0 < mass (V := E) s := mass_pos hs
  have hmgf : mgf (fun y => 2 * s * ⟪y - x, v⟫)
      (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) t =
        (Z x)⁻¹ * Real.exp (s * t ^ 2 * ‖v‖ ^ 2) * Z (x + t • v) := by
    unfold mgf
    rw [integral_tilted]
    have heq : (fun y : E => (Real.exp (-s * ‖x - y‖ ^ 2) /
        (∫ z, Real.exp (-s * ‖x - z‖ ^ 2) ∂μ)) •
          Real.exp (t * (2 * s * ⟪y - x, v⟫))) =
        fun y => (Z x)⁻¹ * (Real.exp (s * t ^ 2 * ‖v‖ ^ 2) *
          Real.exp (-s * ‖x + t • v - y‖ ^ 2)) := by
      funext y
      rw [smul_eq_mul, div_eq_mul_inv]
      rw [mul_comm (Real.exp (-s * ‖x - y‖ ^ 2)), mul_assoc, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_shift_identity]
    rw [heq, integral_const_mul, integral_const_mul]
    dsimp [Z]
    ring
  rw [hmgf, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_eq_gaussian_weight hρ hs,
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_eq_gaussian_weight hρ hs]
  change Z (x + t • v) / mass (V := E) s =
    Z x / mass (V := E) s * Real.exp (-s * t ^ 2 * ‖v‖ ^ 2) *
      ((Z x)⁻¹ * Real.exp (s * t ^ 2 * ‖v‖ ^ 2) * Z (x + t • v))
  rw [show -s * t ^ 2 * ‖v‖ ^ 2 = -(s * t ^ 2 * ‖v‖ ^ 2) by ring, Real.exp_neg]
  field_simp [hZ.ne', hm.ne']
theorem potential_line_cgf {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x v : E) (t : ℝ) :
    potential ρ s (x + t • v) = potential ρ s x + s * t ^ 2 * ‖v‖ ^ 2 -
      cgf (fun y => 2 * s * ⟪y - x, v⟫) (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) t := by
  let _ : IsProbabilityMeasure (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) :=
    isProbabilityMeasure_posterior μ hs x
  have hmgf : 0 < mgf (fun y => 2 * s * ⟪y - x, v⟫)
      (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) t :=
    mgf_pos' (NeZero.ne _) (integrable_exp_score_posterior μ hs x v t)
  rw [potential, normalizedDensity_line_factorization hρ hs,
    Real.log_mul (mul_ne_zero (normalizedDensity_pos hρ hs x).ne' (Real.exp_ne_zero _)) hmgf.ne',
    Real.log_mul (normalizedDensity_pos hρ hs x).ne' (Real.exp_ne_zero _), Real.log_exp]
  simp only [potential, cgf]
  ring
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
 theorem directional_second_eq_hessian {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 =
      bilinearIteratedFDerivTwo ℝ f x v v := by
  have hline (t : ℝ) : HasDerivAt (fun u : ℝ => x + u • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
  have hderiv : deriv (fun t : ℝ => f (x + t • v)) =
      fun t => fderiv ℝ f (x + t • v) v := by
    funext t
    exact ((hf.differentiable (by norm_num) (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  have hd : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y v) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).clm_apply
      (differentiableAt_const v)
  have hdline : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v) v)
      (fderiv ℝ (fun y : E => fderiv ℝ f y v) x v) 0 := by
    exact hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline 0) (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv, hdline.deriv]
  exact (bilinearIteratedFDerivTwo_eq_fderiv_apply hf x v v).symm
theorem bilinearIteratedFDerivTwo_potential_eq_sub_variance_score {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x v : E) :
    bilinearIteratedFDerivTwo ℝ (potential ρ s) x v v = 2 * s * ‖v‖ ^ 2 -
      variance (fun y => 2 * s * ⟪y - x, v⟫) (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) := by
  let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
  let X : E → ℝ := fun y => 2 * s * ⟪y - x, v⟫
  let _ : IsProbabilityMeasure P := isProbabilityMeasure_posterior μ hs x
  have hset : integrableExpSet X P = Set.univ := integrableExpSet_score_posterior μ hs x v
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X P) := by rw [hset]; simp
  have hvar : iteratedDeriv 2 (cgf X P) 0 = variance X P := by
    have h := variance_tilted_mul h0
    simpa only [zero_mul, tilted_const] using h.symm
  have hfun : (fun t : ℝ => potential ρ s (x + t • v)) =
      fun t => potential ρ s x + s * t ^ 2 * ‖v‖ ^ 2 - cgf X P t := by
    funext t
    exact potential_line_cgf hρ hs x v t
  have hcgf : ContDiff ℝ ∞ (cgf X P) := by
    apply contDiff_iff_contDiffAt.2
    intro t
    exact (analyticAt_cgf (by rw [hset]; simp)).contDiffAt
  have hsecond : iteratedDeriv 2
      (fun t : ℝ => potential ρ s x + s * t ^ 2 * ‖v‖ ^ 2 - cgf X P t) 0 =
        2 * s * ‖v‖ ^ 2 - iteratedDeriv 2 (cgf X P) 0 := by
    have hpoly : ContDiff ℝ ∞ (fun t : ℝ => potential ρ s x + s * t ^ 2 * ‖v‖ ^ 2) := by fun_prop
    rw [iteratedDeriv_fun_sub (hpoly.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      (hcgf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
    congr 1
    have heq : (fun t : ℝ => potential ρ s x + s * t ^ 2 * ‖v‖ ^ 2) =
        fun t => potential ρ s x + (s * ‖v‖ ^ 2) * t ^ 2 := by funext t; ring
    rw [heq, iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ))]
    rw [iteratedDeriv_const_mul_field]
    norm_num [iteratedDeriv_pow, Nat.descFactorial]
    ring
  rw [← FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.directional_second_eq_hessian (potential_contDiff_two hρ hs) x v, hfun, hsecond, hvar]
/-- Hessian of the smoothed potential as `2s‖v‖² − 4s² Var_P ⟪·,v⟫` for the posterior `P`. -/
theorem bilinearIteratedFDerivTwo_potential_eq_sub_variance_inner {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x v : E) :
    bilinearIteratedFDerivTwo ℝ (potential ρ s) x v v = 2 * s * ‖v‖ ^ 2 -
      4 * s ^ 2 * variance (fun y => ⟪y, v⟫) (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) := by
  let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
  let _ : IsProbabilityMeasure P := isProbabilityMeasure_posterior μ hs x
  have hshift : variance (fun y : E => ⟪y - x, v⟫) P = variance (fun y : E => ⟪y, v⟫) P := by
    have hY : AEStronglyMeasurable (fun y : E => ⟪y, v⟫) P :=
      ((by fun_prop : Continuous (fun y : E => ⟪y, v⟫))).aestronglyMeasurable
    simpa only [inner_sub_left, Pi.sub_apply] using variance_sub_const hY ⟪x, v⟫
  rw [bilinearIteratedFDerivTwo_potential_eq_sub_variance_score hρ hs, variance_const_mul, hshift]
  ring
/-- **Upper Hessian bound of the smoothed potential** (BKL Section 2, p. 5, regular approximation:
`∇²V_ε ≤ ε⁻¹ Id` for the Gaussian convolution of variance `ε`; here the kernel `e^{-s‖x-y‖²}` has
variance `ε = 1/(2s)`, so the bound is `2s`). Proved from the covariance identity by nonnegativity of
the posterior variance; no moment hypothesis on `μ` beyond being a probability law. -/
theorem bilinearIteratedFDerivTwo_potential_le {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x v : E) :
    bilinearIteratedFDerivTwo ℝ
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential ρ s) x v v ≤
      2 * s * ‖v‖ ^ 2 := by
  rw [bilinearIteratedFDerivTwo_potential_eq_sub_variance_inner hρ hs]
  exact sub_le_self _ (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) (variance_nonneg _ _))
/-- Posterior variance bound `Var_P ⟪·,v⟫ ≤ ‖v‖²/(2s)`, from convexity of the smoothed potential and
the Hessian identity. -/
theorem variance_inner_posterior_le {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x v : E) :
    variance (fun y => ⟪y, v⟫) (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) ≤
      ‖v‖ ^ 2 / (2 * s) := by
  have hpos : 0 < 2 * s := mul_pos (by norm_num) hs
  have hlo := bilinearIteratedFDerivTwo_nonneg_of_convexOn
    (potential_contDiff_two hρ hs) (potential_convex hρ hs) x v
  rw [bilinearIteratedFDerivTwo_potential_eq_sub_variance_inner hρ hs] at hlo
  apply (le_div_iff₀ hpos).2
  apply le_of_mul_le_mul_left ?_ hpos
  nlinarith only [hlo]
section PosteriorSecondMoments
omit [FiniteDimensional ℝ E]
/-- The score is square integrable under the posterior (from its full exponential domain). -/
theorem memLp_two_score_posterior (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x v : E) :
    MemLp (fun y => 2 * s * ⟪y - x, v⟫) 2 (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) := by
  let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
  let X : E → ℝ := fun y => 2 * s * ⟪y - x, v⟫
  let _ : IsProbabilityMeasure P := isProbabilityMeasure_posterior μ hs x
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X P) := by
    rw [show integrableExpSet X P = Set.univ from integrableExpSet_score_posterior μ hs x v]
    simp
  have h := memLp_tilted_mul h0 (2 : NNReal)
  simpa only [zero_mul, tilted_const, ENNReal.coe_ofNat] using h
theorem memLp_two_inner_posterior (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x v : E) :
    MemLp (fun y => ⟪y, v⟫) 2 (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) := by
  let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
  let _ : IsProbabilityMeasure P := isProbabilityMeasure_posterior μ hs x
  have hscore := memLp_two_score_posterior μ hs x v
  have hshift : MemLp (fun y : E => ⟪y - x, v⟫) 2 P := by
    have h := hscore.mul_const (2 * s)⁻¹
    convert h using 1
    funext y
    field_simp [hs.ne']
  have h := hshift.add (memLp_const ⟪x, v⟫)
  simpa only [Pi.add_def, inner_sub_left, sub_add_cancel] using h
end PosteriorSecondMoments
/-- The posterior has a finite second moment: sum the scalar projections over an orthonormal basis
(including dimension zero). -/
theorem memLp_two_id_posterior (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x : E) :
    MemLp id 2 (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) := by
  let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
  let b := stdOrthonormalBasis ℝ E
  have hsq (i : Fin (Module.finrank ℝ E)) : Integrable (fun y : E => ⟪y, b i⟫ ^ 2) P :=
    (memLp_two_iff_integrable_sq (memLp_two_inner_posterior μ hs x (b i)).aestronglyMeasurable).1
      (memLp_two_inner_posterior μ hs x (b i))
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  have heq : (fun y : E => ‖id y‖ ^ 2) = fun y => ∑ i, ⟪y, b i⟫ ^ 2 := by
    funext y
    exact (b.sum_sq_inner_left y).symm
  rw [heq]
  exact integrable_finsetSum Finset.univ (fun i _ => hsq i)
end GaussianSmoothing
end LogConcave
end KLS
end FunctionalInequalities


