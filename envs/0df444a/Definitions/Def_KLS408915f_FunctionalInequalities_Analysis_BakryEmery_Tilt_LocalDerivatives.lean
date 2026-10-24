-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:42:49.808047+00:00
-- url     : https://prove2.me/theorems/37420ee0-8d21-40b5-8860-0cb40b758777
-- title:
--   All-order derivatives of weighted exponential integrals
-- statement:
--   For finite-dimensional real inner-product space $E$, `integrable_exp_inner_smul_of_lt` gives integrability of $x\mapsto e^{\langle z,x\rangle}\,g(x)$ when $\|z\|<r$ and $\int e^{t\|x\|}\|g(x)\|\,d\mu<\infty$ for every $t<r$. Under the same hypotheses, `iteratedFDeriv_weightedExp_integral_of_lt` identifies the $d$-th Fréchet derivative of $z\mapsto\int e^{\langle z,x\rangle}g(x)\,d\mu$ with $\int e^{\langle z,x\rangle}\prod_j\langle x,h_j\rangle g(x)\,d\mu$ for $\|z\|<r$. For a probability measure with one positive exponential moment, `iteratedFDeriv_laplace_zero` specializes this at $z=0$, and `norm_iteratedFDeriv_laplace_zero_le` bounds its operator norm by $\int\|x\|^d\,d\mu$; private auxiliary results establish polynomial moment integrability and the product norm estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/LocalDerivatives.lean#L23-L164 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.IntegrableExpMul

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] in
/-- Inside the exponential radius the weighted integrand `e^{⟪z,x⟫} g(x)` is integrable. -/
theorem integrable_exp_inner_smul_of_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ)
    {z : E} (hz : ‖z‖ < r) : Integrable (fun x => Real.exp ⟪z, x⟫ • g x) μ := by
  refine (hgi ‖z‖ hz).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable.smul hg
  · filter_upwards [] with x
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    gcongr
    exact real_inner_le_norm z x
/-- **All-order derivatives of `z ↦ ∫ e^{⟪z,x⟫} g(x) dμ` inside the exponential radius**: for `‖z‖ < r`,
`D^d(…)(z)(h) = ∫ e^{⟪z,x⟫} ∏_j ⟪x, h_j⟫ g(x) dμ`, given `∫ e^{t‖x‖}‖g‖ < ∞` for all `t < r`. -/
theorem iteratedFDeriv_weightedExp_integral_of_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ)
    (d : ℕ) (z : E) (hz : ‖z‖ < r) (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) z h =
      ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by
  classical
  induction d generalizing g with
  | zero => simp
  | succ d IH =>
    let N : E → F := fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ
    let a := h (Fin.last d)
    let ev : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F a
    let g' : E → F := fun x => weightedExpD g x a
    have hg' : AEStronglyMeasurable g' μ :=
      ev.continuous.comp_aestronglyMeasurable (weightedExpD_meas hg)
    have hgi' : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g' x‖) μ := by
      intro t htr
      refine ((weightedExpD_integrable_lt hg hgi t htr).const_mul ‖a‖).mono' ?_ ?_
      · exact (by fun_prop : Continuous (fun x : E => Real.exp (t * ‖x‖))).aestronglyMeasurable.mul hg'.norm
      · filter_upwards [] with x
        rw [Real.norm_of_nonneg (by positivity)]
        calc
          Real.exp (t * ‖x‖) * ‖g' x‖ ≤
              Real.exp (t * ‖x‖) * (‖weightedExpD g x‖ * ‖a‖) := by
            gcongr
            exact (weightedExpD g x).le_opNorm a
          _ = ‖a‖ * (Real.exp (t * ‖x‖) * ‖weightedExpD g x‖) := by ring
    have hzmem : z ∈ Metric.ball (0 : E) r := by simpa using hz
    have hball : Metric.ball (0 : E) r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hzmem
    have hN : ContDiffAt ℝ ∞ N z :=
      (weighted_integral_contDiffOn μ hg hgi).contDiffAt hball
    have heval : ev ∘ fderiv ℝ N =ᶠ[𝓝 z]
        fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ := by
      filter_upwards [hball] with w hw
      have hw' : ‖w‖ < r := by simpa using hw
      rw [Function.comp_apply, (weightedExp_integral_hasFDerivAt_of_lt μ hg hgi hw').fderiv]
      change (∫ x, Real.exp ⟪w, x⟫ • weightedExpD g x ∂μ) a = _
      rw [ContinuousLinearMap.integral_apply
        (integrable_exp_inner_smul_of_lt μ (weightedExpD_meas hg) (weightedExpD_integrable_lt hg hgi) hw')]
      rfl
    have hevalD : iteratedFDeriv ℝ d (ev ∘ fderiv ℝ N) z =
        iteratedFDeriv ℝ d (fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ) z := by
      have heval' : ev ∘ fderiv ℝ N =ᶠ[𝓝[Set.univ] z]
          fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ := by simpa using heval
      simpa only [iteratedFDerivWithin_univ] using
        heval'.iteratedFDerivWithin_eq heval.self_of_nhds d
    rw [iteratedFDeriv_succ_apply_right]
    change ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) = _
    calc
      ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) =
          iteratedFDeriv ℝ d (ev ∘ fderiv ℝ N) z (Fin.init h) := by
        have hN' : ContDiffAt ℝ ∞ (fderiv ℝ N) z := hN.fderiv_right (by simp)
        have H := ev.iteratedFDeriv_comp_left hN' (i := d)
          (by exact_mod_cast le_top (a := (d : ℕ∞)))
        exact (congrArg (fun T => T (Fin.init h)) H).symm
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, Fin.init h j⟫) • g' x ∂μ := by
        rw [hevalD]
        exact IH hg' hgi' (Fin.init h)
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g', weightedExpD, ContinuousLinearMap.smulRight_apply,
          innerSL_apply_apply, smul_smul]
        rw [Fin.prod_univ_castSucc]
        simp only [a, Fin.init_def, mul_assoc]
/-- The `d`-th derivative of the Laplace transform at `0` is the degree-`d` moment tensor
`h ↦ ∫ ∏_j ⟪x, h_j⟫ dμ`, given one exponential moment `∫ e^{r‖x‖} dμ < ∞`. -/
theorem iteratedFDeriv_laplace_zero (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (d : ℕ) (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) 0 h =
      ∫ x, ∏ j, ⟪x, h j⟫ ∂μ := by
  have hgi : ∀ t < r, Integrable (fun x : E => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
    intro t ht
    refine hexp.mono' (by fun_prop) ?_
    filter_upwards [] with x
    simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ht.le (norm_nonneg x))
  simpa only [smul_eq_mul, mul_one, inner_zero_left, Real.exp_zero, one_mul] using
    iteratedFDeriv_weightedExp_integral_of_lt μ measurable_const.aestronglyMeasurable hgi d 0
      (by simpa using hr) h
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
 theorem moment_product_norm_le (d : ℕ) (h : Fin d → E) (x : E) :
    ‖∏ j, ⟪x, h j⟫‖ ≤ ‖x‖ ^ d * ∏ j, ‖h j‖ := by
  rw [norm_prod]
  calc
    ∏ j, ‖⟪x, h j⟫‖ ≤ ∏ j, ‖x‖ * ‖h j‖ := by
      apply Finset.prod_le_prod
      · intro j _; exact norm_nonneg _
      · intro j _; exact norm_inner_le_norm _ _
    _ = ‖x‖ ^ d * ∏ j, ‖h j‖ := by rw [Finset.prod_mul_distrib]; simp
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem norm_moment_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ d) μ := by
  have hneg : Integrable (fun x : E => Real.exp (-r * ‖x‖)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hr.le) (norm_nonneg x))
  simpa only [abs_norm] using
    ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul hr.ne' hexp hneg d
/-- `‖D^d L_μ(0)‖ ≤ ∫ ‖x‖^d dμ` (operator norm; `d = 0` gives `1`). -/
theorem norm_iteratedFDeriv_laplace_zero_le (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) 0‖ ≤ ∫ x, ‖x‖ ^ d ∂μ := by
  have hm : Integrable (fun x : E => ‖x‖ ^ d) μ :=
    FunctionalInequalities.Analysis.BakryEmery.norm_moment_integrable μ hr hexp d
  apply ContinuousMultilinearMap.opNorm_le_bound (integral_nonneg fun x => pow_nonneg (norm_nonneg x) d)
  intro h
  rw [iteratedFDeriv_laplace_zero μ hr hexp d h]
  have hpi : Integrable (fun x : E => ∏ j, ⟪x, h j⟫) μ :=
    (hm.mul_const (∏ j, ‖h j‖)).mono' (by fun_prop)
      (ae_of_all _ fun x => FunctionalInequalities.Analysis.BakryEmery.moment_product_norm_le d h x)
  calc
    ‖∫ x, ∏ j, ⟪x, h j⟫ ∂μ‖ ≤ ∫ x, ‖∏ j, ⟪x, h j⟫‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂μ :=
      integral_mono hpi.norm (hm.mul_const _) (fun x => FunctionalInequalities.Analysis.BakryEmery.moment_product_norm_le d h x)
    _ = (∫ x, ‖x‖ ^ d ∂μ) * ∏ j, ‖h j‖ := integral_mul_const _ _
end BakryEmery
end Analysis
end FunctionalInequalities


