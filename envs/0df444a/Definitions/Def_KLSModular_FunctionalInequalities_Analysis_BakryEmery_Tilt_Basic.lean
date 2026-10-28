-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:20:39.734111+00:00
-- url     : https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a
-- title:
--   Exponential tilts and smooth tilt integrals
-- statement:
--   For a measure $\mu$ on a finite-dimensional real inner-product space, `expTilt μ z` is the tilted measure with exponent $x\mapsto\langle z,x\rangle$, `tiltAverage μ f z` is $\int f\,d(\operatorname{expTilt}(\mu,z))$, and `taylorTensor μ f d` is $(d!)^{-1}$ times the $d$th iterated Fréchet derivative of this tilt average at $0$, as a continuous multilinear map. The auxiliary private declarations control measurability, exponential growth, integrability, and differentiation under the integral sign; in particular `contDiff_integral_exp_inner_smul` gives smoothness of $z\mapsto\int e^{\langle z,x\rangle}g(x)\,d\mu$ under finiteness, all exponential moments, and the stated polynomial growth bound. The definitions are total, so without integrability the tilted measure and associated integrals may be the zero-measure or totalized values supplied by Mathlib.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
--   import Mathlib.MeasureTheory.Measure.Tilted
--   import FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative
--   import FunctionalInequalities.Analysis.Tensor.Coefficients
--   import Mathlib.Analysis.Calculus.ParametricIntegral
--   import Mathlib.MeasureTheory.Function.L2Space
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def expTilt (μ : Measure E) (z : E) : Measure E :=
--     μ.tilted fun x => ⟪z, x⟫
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/IntegrationByParts/Basic`](https://prove2.me/theorems/63cbd0f3-2def-4aae-8836-ba5c303c076a), [`Analysis/BakryEmery/IteratedDerivative`](https://prove2.me/theorems/ec55966f-66a5-4e3f-9fc7-b3e724ac29c7), [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f).
--
--   Theorems in source order:
--
--   - [`gradient_sub_inner`](https://prove2.me/theorems/6e39480b-596b-4064-876c-d786d322b2b9)
--   - [`expTilt_tilted`](https://prove2.me/theorems/b77ce921-0d7b-4b31-ac8b-28afb215f4d2)
--   - [`integrable_gradient_expTilt`](https://prove2.me/theorems/4ce78d47-f6fb-43d4-9cf4-e4a847a5b302)
--   - [`tiltAverage_neg_weightedLaplacian`](https://prove2.me/theorems/2049b0ee-2e67-44f2-a194-81ea5ae5e577)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean) · `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E2628. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L40-L431 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The exponential tilt `μ_z` of `μ` in direction `z`: density `e^{⟪z, x⟫} / ∫ e^{⟪z, y⟫} dμ(y)`
(BKL (26)). -/
def expTilt (μ : Measure E) (z : E) : Measure E :=
  μ.tilted fun x => ⟪z, x⟫
/-- The tilt average `F_f(z) = ∫ f dμ_z` (BKL (27)), for functions with values in a real Banach
space. -/
def tiltAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (f : E → F) (z : E) : F :=
  ∫ x, f x ∂(expTilt μ z)
/-- The Taylor tensor `T_d f = (1/d!) ∇^d F_f(0)` (BKL (28)), as a continuous `d`-linear map (its
norm is the operator norm, not the source's Hilbert–Schmidt norm). -/
def taylorTensor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (f : E → F) (d : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) F :=
  ((d.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ d (tiltAverage μ f) 0
variable (m : Measure E) [m.IsAddHaarMeasure]
open Filter Topology
universe v
 def expD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (x : E) : E →L[ℝ] F :=
  (innerSL ℝ x).smulRight (g x)
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [CompleteSpace E] in
 theorem expD_meas
    {μ : Measure E} {g : E → F} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (FunctionalInequalities.Analysis.BakryEmery.expD g) μ := by
  exact
    (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp_aestronglyMeasurable
      ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.aestronglyMeasurable.prodMk hg)
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
 theorem expD_bound
    {g : E → F} {M a : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) :
    ∀ x, ‖FunctionalInequalities.Analysis.BakryEmery.expD g x‖ ≤ M * Real.exp ((a + 1) * ‖x‖) := by
  intro x
  have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
    le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
  calc
    ‖FunctionalInequalities.Analysis.BakryEmery.expD g x‖ = ‖x‖ * ‖g x‖ := by
      simp [FunctionalInequalities.Analysis.BakryEmery.expD, ContinuousLinearMap.norm_smulRight_apply,
        innerSL_apply_norm]
    _ ≤ Real.exp ‖x‖ * (M * Real.exp (a * ‖x‖)) := by
      gcongr
      exact hb x
    _ = M * Real.exp ((a + 1) * ‖x‖) := by
      rw [add_mul, Real.exp_add, one_mul]
      ring
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
 theorem exp_smul_bound
    {g : E → F} {M a : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖))
    (z x : E) {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖Real.exp ⟪z, x⟫ • g x‖ ≤ M * Real.exp ((R + a) * ‖x‖) := by
  calc
    ‖Real.exp ⟪z, x⟫ • g x‖ =
        Real.exp ⟪z, x⟫ * ‖g x‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (R * ‖x‖) * (M * Real.exp (a * ‖x‖)) := by
      gcongr
      · exact
          (real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
      · exact hb x
    _ = M * Real.exp ((R + a) * ‖x‖) := by
      rw [add_mul, Real.exp_add]
      ring
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
 theorem exp_smul_int
    (μ : Measure E)
    (hexp : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → F} (hg : AEStronglyMeasurable g μ)
    {M a : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫ • g x) μ := by
  refine ((hexp (‖z‖ + a)).const_mul M).mono' ?_ ?_
  · exact
      (by fun_prop : Continuous (fun x => Real.exp ⟪z, x⟫)).aestronglyMeasurable.smul hg
  · exact ae_of_all μ (fun x => FunctionalInequalities.Analysis.BakryEmery.exp_smul_bound hM hb z x le_rfl)
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
 theorem exp_smul_hasFDeriv
    (g : E → F) (x z : E) :
    HasFDerivAt (fun w => Real.exp ⟪w, x⟫ • g x)
      (Real.exp ⟪z, x⟫ • FunctionalInequalities.Analysis.BakryEmery.expD g x) z := by
  have hl : HasFDerivAt (fun w : E => ⟪w, x⟫) (innerSL ℝ x) z := by
    convert (innerSL ℝ x).hasFDerivAt (x := z) using 1
    ext w
    simpa only [innerSL_apply_apply] using (real_inner_comm w x).symm
  convert hl.exp.smul_const (g x) using 1
  ext y
  simp [FunctionalInequalities.Analysis.BakryEmery.expD, ContinuousLinearMap.smulRight_apply, mul_smul]
omit [CompleteSpace E] in
 theorem exp_integral_hasFDeriv [CompleteSpace F]
    (μ : Measure E)
    (hexp : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → F} (hg : AEStronglyMeasurable g μ)
    {M a : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) (z : E) :
    HasFDerivAt (fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • FunctionalInequalities.Analysis.BakryEmery.expD g x ∂μ) z := by
  have hbd := FunctionalInequalities.Analysis.BakryEmery.expD_bound hM hb
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun w x => Real.exp ⟪w, x⟫ • g x)
    (F' := fun w x => Real.exp ⟪w, x⟫ • FunctionalInequalities.Analysis.BakryEmery.expD g x)
    (bound := fun x =>
      M * Real.exp (((‖z‖ + 1) + (a + 1)) * ‖x‖))
    (Metric.ball_mem_nhds z zero_lt_one)
    ?_ (FunctionalInequalities.Analysis.BakryEmery.exp_smul_int μ hexp hg hM hb z) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun w =>
      (FunctionalInequalities.Analysis.BakryEmery.exp_smul_int μ hexp hg hM hb w).1
  · exact (FunctionalInequalities.Analysis.BakryEmery.exp_smul_int μ hexp (FunctionalInequalities.Analysis.BakryEmery.expD_meas hg) hM hbd z).1
  · filter_upwards with x w hw
    apply FunctionalInequalities.Analysis.BakryEmery.exp_smul_bound hM hbd w x
    have hd : ‖w - z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    calc
      ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        simpa [add_comm] using norm_le_insert' w z
      _ ≤ ‖z‖ + 1 := by linarith
  · exact (hexp _).const_mul M
  · exact ae_of_all μ (fun x w _ => FunctionalInequalities.Analysis.BakryEmery.exp_smul_hasFDeriv g x w)
omit [CompleteSpace E] in
 theorem exp_integral_contDiff_nat
    {F : Type (max u v)}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E)
    (hexp : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (n : ℕ) {g : E → F} (hg : AEStronglyMeasurable g μ)
    {M a : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) :
    ContDiff ℝ n (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  induction n generalizing F M a with
  | zero =>
      exact contDiff_zero.2
        (continuous_iff_continuousAt.2
          (fun z => (FunctionalInequalities.Analysis.BakryEmery.exp_integral_hasFDeriv μ hexp hg hM hb z).continuousAt))
  | succ n IH =>
      apply contDiff_succ_iff_hasFDerivAt.2
      refine ⟨(fun z => ∫ x, Real.exp ⟪z, x⟫ • FunctionalInequalities.Analysis.BakryEmery.expD g x ∂μ), ?_, ?_⟩
      · exact IH (FunctionalInequalities.Analysis.BakryEmery.expD_meas hg) hM (FunctionalInequalities.Analysis.BakryEmery.expD_bound hM hb)
      · exact FunctionalInequalities.Analysis.BakryEmery.exp_integral_hasFDeriv μ hexp hg hM hb
section CompleteSpace
variable [CompleteSpace F]
omit [CompleteSpace E] in
/-- Differentiation under the integral sign for exponential weights: if `μ` is finite with all
exponential moments and `g` grows at most polynomially, `z ↦ ∫ e^{⟪z, x⟫} g(x) dμ(x)` is smooth. -/
theorem contDiff_integral_exp_inner_smul (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {M : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ M * (1 + ‖x‖) ^ k) :
    ContDiff ℝ ∞ (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  let L : ULift.{u} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  have hb : ∀ x, ‖g x‖ ≤ |M| * Real.exp ((k : ℝ) * ‖x‖) := by
    intro x
    calc
      ‖g x‖ ≤ M * (1 + ‖x‖) ^ k := hgb x
      _ ≤ |M| * (Real.exp ‖x‖) ^ k := by
        apply mul_le_mul
        · exact le_abs_self M
        · exact pow_le_pow_left₀ (by positivity)
            (by simpa [add_comm] using Real.add_one_le_exp ‖x‖) k
        · positivity
        · positivity
      _ = |M| * Real.exp ((k : ℝ) * ‖x‖) := by
        rw [Real.exp_nat_mul]
  have hgl : AEStronglyMeasurable (fun x => L.symm (g x)) μ :=
    L.symm.toContinuousLinearEquiv.toContinuousLinearMap.continuous.comp_aestronglyMeasurable hg
  have hbl : ∀ x,
      ‖L.symm (g x)‖ ≤ |M| * Real.exp ((k : ℝ) * ‖x‖) := by
    simpa only [L.symm.norm_map] using hb
  have hnat : ∀ n : ℕ, ContDiff ℝ n
      (fun z => ∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ) :=
    fun n => FunctionalInequalities.Analysis.BakryEmery.exp_integral_contDiff_nat μ hexp n hgl (abs_nonneg M) hbl
  have hs :=
    (contDiff_infty.2 hnat).continuousLinearMap_comp
      L.toContinuousLinearEquiv.toContinuousLinearMap
  have heq :
      (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) =
      (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
    funext z
    change L.toContinuousLinearEquiv.toContinuousLinearMap
      (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ) = _
    rw [← L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (FunctionalInequalities.Analysis.BakryEmery.exp_smul_int μ hexp hgl (abs_nonneg M) hbl z)]
    simp
  change ContDiff ℝ ∞
    (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) at hs
  rwa [heq] at hs
end CompleteSpace
end NormedSpace
end BakryEmery
end Analysis
end FunctionalInequalities


