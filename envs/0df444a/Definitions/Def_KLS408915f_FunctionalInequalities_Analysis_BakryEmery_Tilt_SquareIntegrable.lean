-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:03:39.468184+00:00
-- url     : https://prove2.me/theorems/57d8d520-e61e-49bc-9dbb-dbaef2cf652c
-- title:
--   Exponential-weight differentiation under global moment bounds
-- statement:
--   `weightedExpD g x` is the continuous linear map $v\mapsto\langle v,x\rangle g(x)$, and the associated declarations establish its measurability and the integrability of exponential multiples under the hypothesis that $e^{r\|x\|}\|g(x)\|$ is integrable for every real $r$. The theorem `weightedExp_integral_hasFDeriv` identifies the derivative of $z\mapsto\int e^{\langle z,x\rangle}g(x)\,d\mu$ with the corresponding integral involving `weightedExpD`, while `contDiff_integral_exp_inner_smul_of_integrable` gives $C^\infty$ regularity. The theorem `memLp_exp_inner` states that all exponential moments imply $e^{\langle z,\cdot\rangle}\in L^2(\mu)$; `ENNReal` exponent parameters and the stated a.e. measurability conditions are retained.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L27-L623 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
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

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The derivative amplitude `x ↦ ⟪·, x⟫ • g x` of `w ↦ e^{⟪w, x⟫} g(x)`. -/
def weightedExpD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (x : E) : E →L[ℝ] F :=
  (innerSL ℝ x).smulRight (g x)
section IntegralCalculus
omit [CompleteSpace E]
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Measurability of the derivative amplitude. -/
theorem weightedExpD_meas
    {μ : Measure E} {g : E → F} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (weightedExpD g) μ := by
  exact (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp_aestronglyMeasurable
    ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.aestronglyMeasurable.prodMk hg)
 theorem weightedExpD_integrable {μ : Measure E} {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) :
    ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖weightedExpD g x‖) μ := by
  intro r
  refine (hgi (r + 1)).mono' ?_ ?_
  · exact ((by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖))).aestronglyMeasurable).mul
      (weightedExpD_meas hg).norm
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (by positivity)]
    have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
      le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
    calc
      Real.exp (r * ‖x‖) * ‖weightedExpD g x‖ =
          Real.exp (r * ‖x‖) * (‖x‖ * ‖g x‖) := by
        simp [weightedExpD, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      _ ≤ Real.exp (r * ‖x‖) * (Real.exp ‖x‖ * ‖g x‖) := by gcongr
      _ = Real.exp ((r + 1) * ‖x‖) * ‖g x‖ := by
        rw [add_mul, one_mul, Real.exp_add]
        ring
omit [FiniteDimensional ℝ E] in
/-- Integrability of `e^{⟪z, x⟫} g(x)` under integrability against every exponential weight. -/
theorem weightedExp_integrable (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫ • g x) μ := by
  refine (hgi ‖z‖).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable.smul hg
  · filter_upwards [] with x
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    gcongr
    exact real_inner_le_norm z x
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise derivative of `w ↦ e^{⟪w, x⟫} g(x)`. -/
theorem weightedExp_hasFDeriv (g : E → F) (x z : E) :
    HasFDerivAt (fun w => Real.exp ⟪w, x⟫ • g x)
      (Real.exp ⟪z, x⟫ • weightedExpD g x) z := by
  have hl : HasFDerivAt (fun w : E => ⟪w, x⟫) (innerSL ℝ x) z := by
    convert (innerSL ℝ x).hasFDerivAt (x := z) using 1
    ext w
    simpa only [innerSL_apply_apply] using (real_inner_comm w x).symm
  convert hl.exp.smul_const (g x) using 1
  ext y
  simp [weightedExpD, ContinuousLinearMap.smulRight_apply, mul_smul]
/-- Differentiation under the integral sign for exponential weights (first derivative): the
derivative of `z ↦ ∫ e^{⟪z, x⟫} g(x) dμ` at `z` is `∫ e^{⟪z, x⟫} (⟪x, ·⟫ g(x)) dμ`. -/
theorem weightedExp_integral_hasFDeriv [CompleteSpace F] (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (z : E) :
    HasFDerivAt (fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • weightedExpD g x ∂μ) z := by
  have hdi := FunctionalInequalities.Analysis.BakryEmery.weightedExpD_integrable hg hgi
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun w x => Real.exp ⟪w, x⟫ • g x)
    (F' := fun w x => Real.exp ⟪w, x⟫ • weightedExpD g x)
    (bound := fun x => Real.exp ((‖z‖ + 2) * ‖x‖) * ‖g x‖)
    (Metric.ball_mem_nhds z zero_lt_one)
    ?_ (weightedExp_integrable μ hg hgi z) ?_ ?_ (hgi _) ?_
  · exact Eventually.of_forall fun w => (weightedExp_integrable μ hg hgi w).1
  · exact (weightedExp_integrable μ (weightedExpD_meas hg) hdi z).1
  · filter_upwards with x w hw
    have hd : ‖w - z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have := norm_le_insert' w z
      linarith
    have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
      le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
    calc
      ‖Real.exp ⟪w, x⟫ • weightedExpD g x‖ =
          Real.exp ⟪w, x⟫ * (‖x‖ * ‖g x‖) := by
        simp [weightedExpD, norm_smul, ContinuousLinearMap.norm_smulRight_apply,
          innerSL_apply_norm, Real.norm_of_nonneg (Real.exp_pos _).le]
      _ ≤ Real.exp ((‖z‖ + 1) * ‖x‖) * (Real.exp ‖x‖ * ‖g x‖) := by
        gcongr
        exact (real_inner_le_norm w x).trans
          (mul_le_mul_of_nonneg_right hw' (norm_nonneg _))
      _ = Real.exp ((‖z‖ + 2) * ‖x‖) * ‖g x‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · exact ae_of_all μ (fun x w _ => weightedExp_hasFDeriv g x w)
end NormedSpace
 theorem weightedExp_integral_contDiff_nat.{v} {F : Type (max u v)}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (n : ℕ) {g : E → F} (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) :
    ContDiff ℝ n (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2
      (fun z => (weightedExp_integral_hasFDeriv μ hg hgi z).continuousAt))
  | succ n IH =>
    apply contDiff_succ_iff_hasFDerivAt.2
    refine ⟨(fun z => ∫ x, Real.exp ⟪z, x⟫ • weightedExpD g x ∂μ), ?_, ?_⟩
    · exact IH (weightedExpD_meas hg) (FunctionalInequalities.Analysis.BakryEmery.weightedExpD_integrable hg hgi)
    · exact weightedExp_integral_hasFDeriv μ hg hgi
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- Differentiation under the integral sign for exponential weights, for integrands integrable
against every exponential weight. -/
theorem contDiff_integral_exp_inner_smul_of_integrable (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) :
    ContDiff ℝ ∞ (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  let L : ULift.{u} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  have hgl : AEStronglyMeasurable (fun x => L.symm (g x)) μ :=
    L.symm.toContinuousLinearEquiv.toContinuousLinearMap.continuous.comp_aestronglyMeasurable hg
  have hgil : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖) * ‖L.symm (g x)‖) μ := by
    simpa only [L.symm.norm_map] using hgi
  have hs := (contDiff_infty.2 (fun n =>
    FunctionalInequalities.Analysis.BakryEmery.weightedExp_integral_contDiff_nat μ n hgl hgil)).continuousLinearMap_comp
      L.toContinuousLinearEquiv.toContinuousLinearMap
  have heq :
      (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) =
        (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
    funext z
    change L.toContinuousLinearEquiv.toContinuousLinearMap
      (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ) = _
    rw [← L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (weightedExp_integrable μ hgl hgil z)]
    simp
  change ContDiff ℝ ∞
    (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) at hs
  rwa [heq] at hs
end NormedSpace
end IntegralCalculus
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- With all exponential moments, `e^{⟪z, ·⟫} ∈ L²(μ)`. -/
theorem memLp_exp_inner (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    MemLp (fun x => Real.exp ⟪z, x⟫) 2 μ := by
  have hc : Continuous fun x : E => Real.exp ⟪z, x⟫ := by fun_prop
  refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 ?_
  refine (hexp (2 * ‖z‖)).mono' (hc.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have := real_inner_le_norm z x
  push_cast
  nlinarith
end NormedSpace
end ScalarLp
end Lp
end BakryEmery
end Analysis
end FunctionalInequalities


