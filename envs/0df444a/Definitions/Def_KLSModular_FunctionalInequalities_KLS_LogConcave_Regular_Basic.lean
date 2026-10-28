-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:50:25.095651+00:00
-- url     : https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342
-- title:
--   Regular potentials and their laws
-- statement:
--   `RegularPotential V a b` requires temperate growth of $V$, $a>0$, and the pointwise Hessian bounds $a\|v\|^2\le D^2V(x)[v,v]\le b\|v\|^2$ for all $x,v$. It implies a quadratic lower bound, Gaussian domination and integrability of $e^{-V}$, so `law` defines the probability measure `volume.tilted (-V)`. The bundle also includes the quadratic regularization construction `of_convexOn_hasTemperateGrowth` and affine curvature constants `affineLowerConstant` and `affineUpperConstant`, with positivity of the former and preservation under `comp_affine`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Inverse
--   import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure RegularPotential (V : E → ℝ) (a b : ℝ) : Prop where
--     temperate : V.HasTemperateGrowth
--     pos : 0 < a
--     lower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v
--     upper : ∀ x v, bilinearIteratedFDerivTwo ℝ V x v v ≤ b * ‖v‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Bochner/Tensor`](https://prove2.me/theorems/2bbabe12-7a5f-4cb2-b87b-f8d542aebce2), [`KLS/LogConcave/HeatSemigroup/Inverse`](https://prove2.me/theorems/fb0b02c9-17f0-4cad-9390-4ccd11bc29f3).
--
--   Theorems in source order:
--
--   - [`integrable_exp_mul_norm`](https://prove2.me/theorems/648161d3-ee7c-4a57-800c-c9037b227a1d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Basic.lean) · `FunctionalInequalities.KLS.LogConcave.Regular.Basic` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Basic.lean#L31-L457 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Regular.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Tensor
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The source's regular potential (BKL (12)): `V` smooth with every derivative of polynomial growth
(Mathlib's `HasTemperateGrowth`) and `a ‖v‖² ≤ ∇²V(x)(v, v) ≤ b ‖v‖²` with `a > 0`. The source also
asks `b > 0`; in positive dimension it follows from the two Hessian bounds (`a ≤ b`), while in
dimension `0` the structure allows any `b`. -/
structure RegularPotential (V : E → ℝ) (a b : ℝ) : Prop where
  temperate : V.HasTemperateGrowth
  pos : 0 < a
  lower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v
  upper : ∀ x v, bilinearIteratedFDerivTwo ℝ V x v v ≤ b * ‖v‖ ^ 2
namespace RegularPotential
variable {V : E → ℝ} {a b : ℝ}
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Strong convexity, as the tangent bound at the base point `0`:
`V x ≥ V 0 + ⟪∇V(0), x⟫ + (a/2) ‖x‖²`. -/
theorem quadratic_lower (hV : RegularPotential V a b) (x : E) :
    V 0 + ⟪gradient V 0, x⟫ + a / 2 * ‖x‖ ^ 2 ≤ V x := by
  let f : ℝ → ℝ := fun t => V (t • x)
  let c : ℝ := a / 2 * ‖x‖ ^ 2
  let q : ℝ → ℝ := fun t => f t - c * t ^ 2
  have hV2 : ContDiff ℝ 2 V :=
    hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have hf (t : ℝ) : HasDerivAt f (fderiv ℝ V (t • x) x) t :=
    (hV2.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hq (t : ℝ) : HasDerivAt q (fderiv ℝ V (t • x) x - c * (2 * t)) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hf t).fun_sub ((hasDerivAt_pow 2 t).const_mul c)
  have hqderiv : deriv q = fun t => fderiv ℝ V (t • x) x - c * (2 * t) :=
    funext fun t => (hq t).deriv
  have hq2 (t : ℝ) :
      HasDerivAt (deriv q) (bilinearIteratedFDerivTwo ℝ V (t • x) x x - 2 * c) t := by
    rw [hqderiv]
    have hsecond := (differentiable_fderiv_apply hV2 x (t • x)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hV2] at hsecond
    convert hsecond.sub (((hasDerivAt_id t).const_mul 2).const_mul c) using 1 <;>
      first | rfl | ring
  have hconv : ConvexOn ℝ Set.univ q :=
    convexOn_of_deriv2_nonneg' convex_univ
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
      (fun t _ => (hq2 t).differentiableAt.differentiableWithinAt)
      (fun t _ => by
        rw [Function.iterate_succ_apply, Function.iterate_one, (hq2 t).deriv]
        have hh := hV.lower (t • x) x
        dsimp [c]
        linarith)
  have hs := hconv.le_slope_of_hasDerivAt (by simp) (by simp)
    (show (0 : ℝ) < 1 by norm_num) (hq 0)
  simp [slope_def_field, q, f, c] at hs
  rw [inner_gradient_left]
  linarith
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Gaussian domination of the density: `e^{-V(x)} ≤ C e^{-(a/4)‖x‖²}`. -/
theorem exp_neg_le_gaussian (hV : RegularPotential V a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, Real.exp ((-V) x) ≤ C * Real.exp (-(a / 4) * ‖x‖ ^ 2) := by
    refine ⟨Real.exp (-V 0 + ‖gradient V 0‖ ^ 2 / a), le_of_lt (Real.exp_pos _), ?_⟩
    intro x
    have hinner' := real_inner_le_norm (-gradient V 0) x
    have hinner :
        -⟪gradient V 0, x⟫ ≤ ‖gradient V 0‖ * ‖x‖ := by
      simpa using hinner'
    have hamgm :
        ‖gradient V 0‖ * ‖x‖ ≤
          ‖gradient V 0‖ ^ 2 / a + a / 4 * ‖x‖ ^ 2 := by
      have hs :
          0 ≤ (a * ‖x‖ - 2 * ‖gradient V 0‖) ^ 2 :=
        sq_nonneg (a * ‖x‖ - 2 * ‖gradient V 0‖)
      have ha : a ≠ 0 := ne_of_gt hV.pos
      calc
        ‖gradient V 0‖ * ‖x‖ ≤
            (‖gradient V 0‖ ^ 2 + a ^ 2 / 4 * ‖x‖ ^ 2) / a := by
          apply (le_div_iff₀ hV.pos).2
          nlinarith [hs]
        _ = ‖gradient V 0‖ ^ 2 / a + a / 4 * ‖x‖ ^ 2 := by
          field_simp [ha]
    have hexp :
        (-V) x ≤
          -V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2 := by
      change -V x ≤
        -V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2
      have hq := hV.quadratic_lower x
      linarith
    calc
      Real.exp ((-V) x) ≤
          Real.exp (-V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2) :=
        Real.exp_le_exp.mpr hexp
      _ = Real.exp (-V 0 + ‖gradient V 0‖ ^ 2 / a) *
          Real.exp (-(a / 4) * ‖x‖ ^ 2) := by
        rw [show
          -V 0 + ‖gradient V 0‖ ^ 2 / a - (a / 4) * ‖x‖ ^ 2 =
            (-V 0 + ‖gradient V 0‖ ^ 2 / a) +
              (-(a / 4) * ‖x‖ ^ 2) by ring]
        rw [Real.exp_add]
/-- `e^{-V}` is Lebesgue integrable. -/
theorem integrable_exp_neg (hV : RegularPotential V a b) :
    Integrable (fun x => Real.exp ((-V) x)) (volume : Measure E) := by
  obtain ⟨C, hC0, hC⟩ := hV.exp_neg_le_gaussian
  have ha4 : 0 < a / 4 := by linarith [hV.pos]
  have hb : 0 < ((a / 4 : ℝ) : ℂ).re := by simpa using ha4
  have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) hb 0 0).norm
  have hgauss : Integrable (fun x : E => Real.exp (-(a / 4) * ‖x‖ ^ 2)) (volume : Measure E) := by
    refine hg.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have hcont : Continuous fun x => Real.exp ((-V) x) :=
    Real.continuous_exp.comp hV.temperate.1.continuous.neg
  refine (hgauss.const_mul C).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hC x
/-- The regular law `volume.tilted (-V)` is a probability measure. -/
theorem isProbabilityMeasure (hV : RegularPotential V a b) :
    IsProbabilityMeasure ((volume : Measure E).tilted (-V)) := by
    exact MeasureTheory.isProbabilityMeasure_tilted (integrable_exp_neg hV)
/-- The regular law as a probability measure. -/
def law (hV : RegularPotential V a b) : ProbabilityMeasure E :=
  ⟨(volume : Measure E).tilted (-V), hV.isProbabilityMeasure⟩
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Regular potential from a convex temperate potential with bounded Hessian**: if `f` is convex with
`Function.HasTemperateGrowth` and `∇²f ≤ B`, then `f + δ/2‖·‖²` is a regular potential with curvature
bounds `δ ≤ ∇² ≤ B + δ` (BKL Section 2, p. 5, the quadratic tilt step of the regular approximation). -/
theorem of_convexOn_hasTemperateGrowth {f : E → ℝ} (hf : f.HasTemperateGrowth)
    (hc : ConvexOn ℝ Set.univ f) {B δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ x v, bilinearIteratedFDerivTwo ℝ f x v v ≤ B * ‖v‖ ^ 2) :
    RegularPotential (fun y => f y + δ / 2 * ‖y‖ ^ 2) δ (B + δ) where
  temperate := by
    have hq := (Function.HasTemperateGrowth.const (δ / 2 : ℝ)).mul
      (Function.hasTemperateGrowth_norm_sq E)
    exact hf.add hq
  pos := hδ
  lower x v := by
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_add_quadratic (hf.1.of_le (WithTop.coe_le_coe.mpr le_top))]
    have h := Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn (hf.1.of_le (WithTop.coe_le_coe.mpr le_top)) hc x v
    linarith
  upper x v := by
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_add_quadratic (hf.1.of_le (WithTop.coe_le_coe.mpr le_top))]
    have h := hb x v
    nlinarith
/-- Lower curvature constant of `V ∘ (L · + c)`: `a / (1 + ‖L⁻¹‖)²` (positive in every dimension). -/
noncomputable def affineLowerConstant (a : ℝ) (L : E ≃L[ℝ] E) : ℝ :=
  a / (1 + ‖(L.symm : E →L[ℝ] E)‖) ^ 2
/-- Upper curvature constant of `V ∘ (L · + c)`: `max b 1 · (1 + ‖L‖)²`. -/
noncomputable def affineUpperConstant (b : ℝ) (L : E ≃L[ℝ] E) : ℝ :=
  max b 1 * (1 + ‖(L : E →L[ℝ] E)‖) ^ 2
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem affineLowerConstant_pos {a : ℝ} (ha : 0 < a) (L : E ≃L[ℝ] E) :
    0 < affineLowerConstant a L := by
  unfold affineLowerConstant
  exact div_pos ha (sq_pos_of_pos (by positivity))
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Regular potentials are preserved by affine changes of variables**: `V ∘ (L · + c)` is regular with
constants `affineLowerConstant a L`, `affineUpperConstant b L` (positive also in dimension zero). -/
theorem comp_affine {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃L[ℝ] E) (c : E) :
    KLS.RegularPotential (fun x => V (L x + c)) (affineLowerConstant a L) (affineUpperConstant b L) := by
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨?_, affineLowerConstant_pos hV.pos L, ?_, ?_⟩
  · exact hV.temperate.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))
  · intro x v
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_affine hV2 L c x v v]
    have hbase := hV.lower (L x + c) (L v)
    have hinv : ‖v‖ ≤ (1 + ‖(L.symm : E →L[ℝ] E)‖) * ‖L v‖ := by
      calc
        ‖v‖ = ‖L.symm (L v)‖ := by rw [L.symm_apply_apply]
        _ ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖L v‖ := (L.symm : E →L[ℝ] E).le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hsq : ‖v‖ ^ 2 ≤ (1 + ‖(L.symm : E →L[ℝ] E)‖) ^ 2 * ‖L v‖ ^ 2 := by
      simpa only [← pow_two, mul_pow] using mul_self_le_mul_self (norm_nonneg v) hinv
    have hdiv : ‖v‖ ^ 2 / (1 + ‖(L.symm : E →L[ℝ] E)‖) ^ 2 ≤ ‖L v‖ ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity))).2
      simpa only [mul_comm] using hsq
    have hmul := mul_le_mul_of_nonneg_left hdiv hV.pos.le
    apply le_trans _ hbase
    simpa only [affineLowerConstant, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  · intro x v
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_affine hV2 L c x v v]
    have hbase := hV.upper (L x + c) (L v)
    have hnorm : ‖L v‖ ≤ (1 + ‖(L : E →L[ℝ] E)‖) * ‖v‖ :=
      ((L : E →L[ℝ] E).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    have hsq : ‖L v‖ ^ 2 ≤ (1 + ‖(L : E →L[ℝ] E)‖) ^ 2 * ‖v‖ ^ 2 := by
      simpa only [← pow_two, mul_pow] using mul_self_le_mul_self (norm_nonneg _) hnorm
    calc
      bilinearIteratedFDerivTwo ℝ V (L x + c) (L v) (L v) ≤ b * ‖L v‖ ^ 2 := hbase
      _ ≤ max b 1 * ‖L v‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left b 1) (sq_nonneg _)
      _ ≤ max b 1 * ((1 + ‖(L : E →L[ℝ] E)‖) ^ 2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (le_trans zero_le_one (le_max_right b 1))
      _ = affineUpperConstant b L * ‖v‖ ^ 2 := by unfold affineUpperConstant; ring
end RegularPotential
end KLS
end FunctionalInequalities


