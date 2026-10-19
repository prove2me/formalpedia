-- Prove2me | Definitions.Def_OAIQWZT002
-- name    : OAIQWZT002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:32:04.368731+00:00
-- url     : https://prove2.me/theorems/a045c882-6fb6-4e72-8597-31d270c6cd54
-- title:
--   OpenAI zero-temperature SK split: definitions bundle 3 (control problem, diffusion, moments)
-- statement:
--   The third definitions bundle of the split of OpenAI's proof of `OAI.ZeroTemperatureSK.full_support`. It holds OpenAI's Lean definitions from `lean/OAI/Probability/SKSupport` (OpenAI, *Full support of the zero-temperature Sherrington-Kirkpatrick order parameter*, OpenAI Math Release, September 27, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. It holds the rest of OpenAI's definitions: tilted means and semigroups, the backward equation, the finite control grids, the constructed optimal diffusion `diffusion`, the Burgers and density constructions, and the moment curves such as `curvatureMoment`. Several definitions are built from theorems (by choice of witnesses), so the bundle contains those theorems' proofs, with one exception: the Gaussian heat equation and its Cole–Hopf form are not re-proved here, the bundle imports them as the published statements `OAI.ZeroTemperatureSK.Heat.gaussian_heat_equation` and `OAI.ZeroTemperatureSK.Heat.gaussian_cole_hopf` of this split (OpenAI's `varianceHeat_equation` and `logarithmic_heat_equation` are one-line restatements of them). It imports the published bundle `Def_SKFullSupport` (for `Time`, `extend`, `OrderParameter`, `BrownianSystem`, `incrementFiltration`, `Control`, `controlPayoff`, `value`, `gradient`, `curvature`, `parisi`, `IsMinimizer`, `IsStieltjesMeasure`, `IsDiffusion`, `squareMoment`, `FullSupportConclusion`) and the definitions bundle `OAIQWZT001`.
--
--   The theorems that the definitions do not need are proved in the solutions of this split: the two published heat-equation statements (whose proofs import no bundle of the split), the intermediate statement `OAI.ZeroTemperatureSK.positive_gap_curvature`, and the external goal `OAI.ZeroTemperatureSK.full_support`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Full support of the zero-temperature Sherrington-Kirkpatrick order parameter, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 281; Apache License 2.0); definitions carved from lean/OAI/Probability/SKSupport at commit adc7f12

import Mathlib
import Definitions.Def_SKFullSupport
import Definitions.Def_OAIQWZT001
import Theorems.Thm_OAI_ZeroTemperatureSK_Heat_gaussian_cole_hopf
import Theorems.Thm_OAI_ZeroTemperatureSK_Heat_gaussian_heat_equation

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
namespace OAI
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434
end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Semigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def semigroup (h : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f (x+y) ∂gaussianReal 0 h

def logSemigroup (c : ℝ) (h : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if c = 0 then semigroup h f x else Real.log (semigroup h (fun z => Real.exp (c*f z)) x) / c

lemma integrable_translate_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (h : ℝ≥0) (x : ℝ) :
    Integrable (fun y => f (x+y)) (gaussianReal 0 h) := by
  apply Integrable.mono' ((integrable_const ‖f x‖).add
    (((memLp_id_gaussianReal (μ := 0) (v := h) 1).integrable (by simp)).norm.const_mul (K:ℝ)))
    (hf.continuous.measurable.comp (measurable_const.add measurable_id) |>.aestronglyMeasurable)
  filter_upwards [] with y
  have hb := hf.norm_sub_le (x+y) x
  have hh := norm_sub_le (f (x+y)) (f x)
  have hh' := norm_add_le (f (x+y)-f x) (f x)
  simp only [add_sub_cancel_left, sub_add_cancel] at hb hh'
  change ‖f (x+y)‖ ≤ ‖f x‖+(K:ℝ)*‖y‖
  linarith

lemma integrable_exp_translate_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    Integrable (fun y => Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
  apply Integrable.mono' ((integrable_exp_abs (|c| * (K:ℝ)) 0 h).const_mul (Real.exp (c*f x)))
    ((measurable_const.mul (hf.continuous.measurable.comp (measurable_const.add measurable_id))).exp.aestronglyMeasurable)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ := hf.norm_sub_le (x+y) x
  simp only [Real.norm_eq_abs, add_sub_cancel_left] at h₁
  have h₂ : c*(f (x+y)-f x) ≤ |c| * |f (x+y)-f x| := by
    calc
      _ ≤ |c*(f (x+y)-f x)| := le_abs_self _
      _ = _ := abs_mul _ _
  have h₃ := mul_le_mul_of_nonneg_left h₁ (abs_nonneg c)
  change c*f (x+y) ≤ c*f x+(|c| * (K:ℝ))*|y|
  nlinarith

lemma semigroup_exp_pos {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    0 < semigroup h (fun z => Real.exp (c*f z)) x := by
  unfold semigroup
  exact integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
    (integrable_exp_translate_of_lipschitz hf c h x) |>.mpr (by simp [Function.support])

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma semigroup_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (h : ℝ≥0) : LipschitzWith K (semigroup h f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, Real.dist_eq]
  unfold semigroup
  rw [← integral_sub (integrable_translate_of_lipschitz hf h x)
    (integrable_translate_of_lipschitz hf h z)]
  calc
    _ ≤ ∫ y, |f (x+y)-f (z+y)| ∂gaussianReal 0 h := abs_integral_le_integral_abs
    _ ≤ ∫ _y, (K:ℝ)*|x-z| ∂gaussianReal 0 h := by
      apply integral_mono ((integrable_translate_of_lipschitz hf h x).sub
        (integrable_translate_of_lipschitz hf h z)).abs (integrable_const _)
      intro y
      change |f (x+y)-f (z+y)| ≤ (K:ℝ)*|x-z|
      simpa only [Real.norm_eq_abs, add_sub_add_right_eq_sub] using hf.norm_sub_le (x+y) (z+y)
    _ = _ := by simp

lemma logSemigroup_sub_le {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {c : ℝ} (hc : 0 < c) (h : ℝ≥0) (x z : ℝ) :
    logSemigroup c h f x-logSemigroup c h f z ≤ (K:ℝ)*|x-z| := by
  have hx := semigroup_exp_pos hf c h x
  have hz := semigroup_exp_pos hf c h z
  have hE : semigroup h (fun w => Real.exp (c*f w)) x ≤
      Real.exp (c*((K:ℝ)*|x-z|))*semigroup h (fun w => Real.exp (c*f w)) z := by
    unfold semigroup
    rw [← integral_const_mul]
    apply integral_mono (integrable_exp_translate_of_lipschitz hf c h x)
      ((integrable_exp_translate_of_lipschitz hf c h z).const_mul _)
    intro y
    change Real.exp (c*f (x+y)) ≤ Real.exp (c*((K:ℝ)*|x-z|))*Real.exp (c*f (z+y))
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := hf.norm_sub_le (x+y) (z+y)
    simp only [Real.norm_eq_abs, add_sub_add_right_eq_sub] at hh
    have hh' := (le_abs_self (f (x+y)-f (z+y))).trans hh
    nlinarith
  have hlog := Real.log_le_log hx hE
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hz), Real.log_exp] at hlog
  simp only [logSemigroup, ne_of_gt hc, ↓reduceIte]
  rw [← sub_div, div_le_iff₀ hc]
  nlinarith

lemma logSemigroup_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    LipschitzWith K (logSemigroup c h f) := by
  by_cases hc0 : c = 0
  · subst c
    have he : logSemigroup 0 h f = semigroup h f := by
      funext x
      simp only [logSemigroup, ↓reduceIte]
    rw [he]
    exact semigroup_lipschitz hf h
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    apply LipschitzWith.of_dist_le_mul
    intro x z
    rw [Real.dist_eq, Real.dist_eq, abs_le]
    constructor
    · have he := logSemigroup_sub_le hf hcp h z x
      rw [abs_sub_comm z x] at he
      linarith
    · exact logSemigroup_sub_le hf hcp h x z

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.ExpTranslateLocalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma exp_translate_local_bound {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (x z y : ℝ)
    (hz : |z-x| ≤ 1) :
    Real.exp (c*f (z+y)) ≤
      Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hfz := hf.norm_sub_le (z+y) x
  simp only [Real.norm_eq_abs] at hfz
  have hz' : |z+y-x| ≤ 1+|y| := by
    have he : z+y-x = (z-x)+y := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  have h₁ := mul_le_mul_of_nonneg_left hz' K.coe_nonneg
  have h₂ := (le_abs_self (f (z+y)-f x)).trans (hfz.trans h₁)
  nlinarith [mul_le_mul_of_nonneg_left h₂ hc]

lemma hasDerivAt_semigroup_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (semigroup h (fun z => Real.exp (c*f z)))
      (∫ y, c*deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) x := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  let bound (y : ℝ) := c*(K:ℝ)*Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|)
  have hb : Integrable bound (gaussianReal 0 h) :=
    (integrable_exp_abs (c*(K:ℝ)) 0 h).const_mul _
  have hi := integrable_exp_translate_of_lipschitz hLip c h x
  have hm : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (fun y => Real.exp (c*f (z+y))) (gaussianReal 0 h) :=
    Filter.Eventually.of_forall (fun z => by
      exact (measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp.aestronglyMeasurable)
  have hdm : AEStronglyMeasurable
      (fun y => c*deriv f (x+y)*Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
    exact ((measurable_const.mul (hdf.measurable.comp (measurable_const.add measurable_id))).mul
      (measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      ‖c*deriv f (z+y)*Real.exp (c*f (z+y))‖ ≤ bound y := by
    filter_upwards [] with y z hz
    have hz' : |z-x| ≤ 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using le_of_lt hz
    have hD : |deriv f (z+y)| ≤ K := by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := z+y) hLip
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc,
      abs_of_pos (Real.exp_pos _)]
    change c*|deriv f (z+y)| * Real.exp (c*f (z+y)) ≤
      c*(K:ℝ)*Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|)
    calc
      _ ≤ c*(K:ℝ)*Real.exp (c*f (z+y)) := by gcongr
      _ ≤ _ := by
        have he := mul_le_mul_of_nonneg_left (exp_translate_local_bound hLip hc x z y hz')
          (mul_nonneg hc K.coe_nonneg)
        simpa only [mul_assoc] using he
  have hdiff : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => Real.exp (c*f (w+y)))
        (c*deriv f (z+y)*Real.exp (c*f (z+y))) z := by
    filter_upwards [] with y z hz
    have h1 : HasDerivAt (fun w => f (w+y)) (deriv f (z+y)) z := by
      convert (hf.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
        ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
    have h2 := (h1.const_mul c).exp
    convert h2 using 1 <;> try rfl
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)) hm hi hdm hbound hb hdiff).2

lemma hasDerivAt_logSemigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 < c)
    (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (logSemigroup c h f)
      ((∫ y, deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) /
        semigroup h (fun z => Real.exp (c*f z)) x) x := by
  have hd := hasDerivAt_semigroup_exp hf hLip hc.le h x
  have he : (∫ y, c*deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) =
      c*(∫ y, deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [he] at hd
  have hh := ((hd.log (ne_of_gt (semigroup_exp_pos hLip c h x))).div_const c)
  have hfun : logSemigroup c h f = fun z =>
      Real.log (semigroup h (fun w => Real.exp (c*f w)) z)/c := by
    funext z
    simp only [logSemigroup, ne_of_gt hc, ↓reduceIte]
  rw [hfun]
  convert hh using 1 <;> try rfl
  first | rfl | field_simp [ne_of_gt hc]

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma integrable_weight_exp_translate {f g : ℝ → ℝ} {K G : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Measurable g) (hG : ∀ z, |g z| ≤ G)
    (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    Integrable (fun y => g (x+y)*Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
  apply (integrable_exp_translate_of_lipschitz hf c h x).bdd_mul
    (hg.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  filter_upwards [] with y
  change ‖g (x+y)‖ ≤ (G:ℝ)
  simpa only [Real.norm_eq_abs] using hG (x+y)

lemma hasDerivAt_semigroup_weight_exp {f g : ℝ → ℝ} {K G G₁ : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f)
    (hg : ContDiff ℝ 1 g) (hG : ∀ z, |g z| ≤ G) (hG₁ : ∀ z, |deriv g z| ≤ G₁)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (semigroup h (fun z => g z*Real.exp (c*f z)))
      (∫ y, (deriv g (x+y)+c*g (x+y)*deriv f (x+y))*Real.exp (c*f (x+y))
        ∂gaussianReal 0 h) x := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv_one
  have hdg : Continuous (deriv g) := hg.continuous_deriv_one
  let C : ℝ := (G₁:ℝ)+c*(G:ℝ)*(K:ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let bound (y : ℝ) := C*Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|)
  have hb : Integrable bound (gaussianReal 0 h) :=
    (integrable_exp_abs (c*(K:ℝ)) 0 h).const_mul _
  have hi := integrable_weight_exp_translate hLip hg.continuous.measurable hG c h x
  have hm : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable
      (fun y => g (z+y)*Real.exp (c*f (z+y))) (gaussianReal 0 h) := by
    filter_upwards [] with z
    exact ((hg.continuous.measurable.comp (measurable_const.add measurable_id)).mul
      ((measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp)).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun y =>
      (deriv g (x+y)+c*g (x+y)*deriv f (x+y))*Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
    exact ((hdg.measurable.comp (measurable_const.add measurable_id)).add
      ((measurable_const.mul (hg.continuous.measurable.comp (measurable_const.add measurable_id))).mul
        (hdf.measurable.comp (measurable_const.add measurable_id))) |>.mul
      ((measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      ‖(deriv g (z+y)+c*g (z+y)*deriv f (z+y))*Real.exp (c*f (z+y))‖ ≤ bound y := by
    filter_upwards [] with y z hz
    have hz' : |z-x| ≤ 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using le_of_lt hz
    have hD : |deriv f (z+y)| ≤ K := by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := z+y) hLip
    have hw : |deriv g (z+y)+c*g (z+y)*deriv f (z+y)| ≤ C := by
      calc
        _ ≤ |deriv g (z+y)|+|c*g (z+y)*deriv f (z+y)| := abs_add_le _ _
        _ = |deriv g (z+y)|+c*|g (z+y)| * |deriv f (z+y)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc]
        _ ≤ C := by dsimp only [C]; gcongr; exact hG₁ _; exact hG _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ C*Real.exp (c*f (z+y)) := mul_le_mul_of_nonneg_right hw (Real.exp_nonneg _)
      _ ≤ bound y := by
        have he := mul_le_mul_of_nonneg_left (exp_translate_local_bound hLip hc x z y hz') hC
        simpa only [bound, mul_assoc] using he
  have hdiff : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => g (w+y)*Real.exp (c*f (w+y)))
        ((deriv g (z+y)+c*g (z+y)*deriv f (z+y))*Real.exp (c*f (z+y))) z := by
    filter_upwards [] with y z hz
    have h1 : HasDerivAt (fun w => f (w+y)) (deriv f (z+y)) z := by
      convert (hf.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
        ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
    have h2 : HasDerivAt (fun w => g (w+y)) (deriv g (z+y)) z := by
      convert (hg.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
        ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
    convert h2.mul (h1.const_mul c).exp using 1 <;> try rfl
    first | rfl | ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)) hm hi hdm hbound hb hdiff).2

lemma hasDerivAt_semigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f) (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (semigroup h f) (semigroup h (deriv f) x) x := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv_one
  have hm : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun y => f (z+y)) (gaussianReal 0 h) :=
    Filter.Eventually.of_forall (fun z => (hf.continuous.measurable.comp
      (measurable_const.add measurable_id)).aestronglyMeasurable)
  have hdm : AEStronglyMeasurable (fun y => deriv f (x+y)) (gaussianReal 0 h) :=
    (hdf.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      ‖deriv f (z+y)‖ ≤ (K:ℝ) := by
    filter_upwards [] with y z hz
    exact norm_deriv_le_of_lipschitz hLip
  have hdiff : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => f (w+y)) (deriv f (z+y)) z := by
    filter_upwards [] with y z hz
    convert (hf.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
      ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)) hm
    (integrable_translate_of_lipschitz hLip h x) hdm hbound (integrable_const _) hdiff).2

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.BoundedSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure BoundedSmooth (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  bounds : ∀ n : ℕ, ∃ C : ℝ≥0, ∀ x, |iteratedDeriv n g x| ≤ C

lemma BoundedSmooth.bound {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    ∃ C : ℝ≥0, ∀ x, |g x| ≤ C := by simpa using hg.bounds 0

lemma BoundedSmooth.deriv {g : ℝ → ℝ} (hg : BoundedSmooth g) : BoundedSmooth (deriv g) := by
  constructor
  · exact contDiff_infty_iff_deriv.mp hg.smooth |>.2
  · intro n
    simpa only [iteratedDeriv_succ'] using hg.bounds (n+1)

lemma BoundedSmooth.const (c : ℝ) : BoundedSmooth (fun _ : ℝ => c) := by
  constructor
  · exact contDiff_const
  · intro n
    refine ⟨Real.nnabs c, fun x => ?_⟩
    cases n <;> simp [iteratedDeriv_const, Real.coe_nnabs]

lemma BoundedSmooth.add {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x+g x) := by
  constructor
  · exact hf.smooth.add hg.smooth
  · intro n
    obtain ⟨A,hA⟩ := hf.bounds n
    obtain ⟨B,hB⟩ := hg.bounds n
    refine ⟨A+B, fun x => ?_⟩
    rw [iteratedDeriv_fun_add (n := n) (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
    exact (abs_add_le _ _).trans (add_le_add (hA x) (hB x))

lemma BoundedSmooth.mul {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x*g x) := by
  classical
  constructor
  · exact hf.smooth.mul hg.smooth
  · intro n
    choose A hA using hf.bounds
    choose B hB using hg.bounds
    refine ⟨∑ i ∈ Finset.range (n+1), (n.choose i:ℝ≥0)*A i*B (n-i), fun x => ?_⟩
    rw [iteratedDeriv_fun_mul (n := n) (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (n.choose i:ℝ) from Nat.cast_nonneg _)]
    gcongr
    · exact hA i x
    · exact hB (n-i) x

lemma BoundedSmooth.const_mul {g : ℝ → ℝ} (hg : BoundedSmooth g) (c : ℝ) :
    BoundedSmooth (fun x => c*g x) := (BoundedSmooth.const c).mul hg

structure RegularDatum (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  deriv_bounded : BoundedSmooth (deriv f)

lemma weighted_derivative_boundedSmooth {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hg : BoundedSmooth g) (c : ℝ) :
    BoundedSmooth (fun x => deriv g x+c*g x*deriv f x) :=
  hg.deriv.add ((hg.const_mul c).mul hf.deriv_bounded)

lemma weighted_derivative_formula {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    deriv (semigroup h (fun z => g z*Real.exp (c*f z))) =
      semigroup h (fun z => (deriv g z+c*g z*deriv f z)*Real.exp (c*f z)) := by
  obtain ⟨G,hG⟩ := hg.bound
  obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
  funext x
  exact (hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
    (hg.smooth.of_le (by simp)) hG hG₁ hc h x).deriv

lemma contDiff_nat_semigroup_weight_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (h : ℝ≥0) (n : ℕ) : ∀ g : ℝ → ℝ, BoundedSmooth g →
    ContDiff ℝ n (semigroup h (fun z => g z*Real.exp (c*f z))) := by
  induction n with
  | zero =>
      intro g hg
      rw [Nat.cast_zero, contDiff_zero]
      apply Differentiable.continuous (𝕜 := ℝ)
      intro x
      obtain ⟨G,hG⟩ := hg.bound
      obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
      exact (hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
        (hg.smooth.of_le (by simp)) hG hG₁ hc h x).differentiableAt
  | succ n IH =>
      intro g hg
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨?_, by simp, ?_⟩
      · intro x
        obtain ⟨G,hG⟩ := hg.bound
        obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
        exact (hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
          (hg.smooth.of_le (by simp)) hG hG₁ hc h x).differentiableAt
      · rw [weighted_derivative_formula hf hLip hg hc h]
        exact IH _ (weighted_derivative_boundedSmooth hf hg c)

lemma contDiff_semigroup_weight_exp {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    ContDiff ℝ ∞ (semigroup h (fun z => g z*Real.exp (c*f z))) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n hn
  exact contDiff_nat_semigroup_weight_exp hf hLip hc h n g hg

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.TiltedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def tiltedMean (c : ℝ) (h : ℝ≥0) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  semigroup h (fun z => g z*Real.exp (c*f z)) x /
    semigroup h (fun z => Real.exp (c*f z)) x

lemma tiltedMean_bound {f g : ℝ → ℝ} {K G : ℝ≥0}
    (hLip : LipschitzWith K f) (hgm : Measurable g) (hG : ∀ x, |g x| ≤ G)
    (c : ℝ) (h : ℝ≥0) (x : ℝ) : |tiltedMean c h f g x| ≤ G := by
  have hE := semigroup_exp_pos hLip c h x
  unfold tiltedMean
  rw [abs_div, abs_of_pos hE, div_le_iff₀ hE]
  unfold semigroup
  rw [← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (integrable_weight_exp_translate hLip hgm hG c h x).abs
    ((integrable_exp_translate_of_lipschitz hLip c h x).const_mul _)
  intro y
  change |g (x+y)*Real.exp (c*f (x+y))| ≤ (G:ℝ)*Real.exp (c*f (x+y))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hG _) (Real.exp_nonneg _)

lemma contDiff_semigroup_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    ContDiff ℝ ∞ (semigroup h (fun z => Real.exp (c*f z))) := by
  simpa only [one_mul] using contDiff_semigroup_weight_exp hf hLip (BoundedSmooth.const 1) hc h

lemma contDiff_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) : ContDiff ℝ ∞ (tiltedMean c h f g) := by
  exact (contDiff_semigroup_weight_exp hf hLip hg hc h).div
    (contDiff_semigroup_exp hf hLip hc h) (fun x => ne_of_gt (semigroup_exp_pos hLip c h x))

lemma hasDerivAt_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (tiltedMean c h f g)
      (tiltedMean c h f (fun z => deriv g z+c*g z*deriv f z) x -
        c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) x := by
  obtain ⟨G,hG⟩ := hg.bound
  obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
  have hN := hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
    (hg.smooth.of_le (by simp)) hG hG₁ hc h x
  have hD := hasDerivAt_semigroup_exp (hf.smooth.of_le (by simp)) hLip hc h x
  have he : (∫ y, c*deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) =
      c*semigroup h (fun z => deriv f z*Real.exp (c*f z)) x := by
    unfold semigroup
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [he] at hD
  have hE := ne_of_gt (semigroup_exp_pos hLip c h x)
  change HasDerivAt _ (semigroup h (fun z => (deriv g z+c*g z*deriv f z)*Real.exp (c*f z)) x) x at hN
  have hND := hN.div hD hE
  change HasDerivAt _ (_/semigroup h (fun z => Real.exp (c*f z)) x -
    c*(_/semigroup h (fun z => Real.exp (c*f z)) x)*
      (_/semigroup h (fun z => Real.exp (c*f z)) x)) x
  convert hND using 1 <;> first | rfl | field_simp

lemma deriv_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    deriv (tiltedMean c h f g) = fun x =>
      tiltedMean c h f (fun z => deriv g z+c*g z*deriv f z) x -
        c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x := by
  funext x
  exact (hasDerivAt_tiltedMean hf hLip hg hc h x).deriv

lemma iteratedDeriv_mul_bound {f g : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (A B : ℕ → ℝ≥0)
    (hA : ∀ i ≤ n, ∀ x, |iteratedDeriv i f x| ≤ A i)
    (hB : ∀ i ≤ n, ∀ x, |iteratedDeriv i g x| ≤ B i) (x : ℝ) :
    |iteratedDeriv n (fun z => f z*g z) x| ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*A i*B (n-i) := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (n.choose i:ℝ) from Nat.cast_nonneg _)]
  gcongr
  · exact hA i hi' x
  · exact hB (n-i) (Nat.sub_le _ _) x

lemma boundedSmooth_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) : BoundedSmooth (tiltedMean c h f g) := by
  classical
  constructor
  · exact contDiff_tiltedMean hf hLip hg hc h
  · have hbounds : ∀ n : ℕ, ∀ g : ℝ → ℝ, BoundedSmooth g →
        ∃ C : ℝ≥0, ∀ x, |iteratedDeriv n (tiltedMean c h f g) x| ≤ C := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n IH =>
        intro g hg
        cases n with
        | zero =>
          obtain ⟨G,hG⟩ := hg.bound
          refine ⟨G, fun x => ?_⟩
          simpa only [iteratedDeriv_zero] using
            (tiltedMean_bound hLip hg.smooth.continuous.measurable hG c h x)
        | succ m =>
          let q (z : ℝ) := deriv g z+c*g z*deriv f z
          have hq : BoundedSmooth q := weighted_derivative_boundedSmooth hf hg c
          obtain ⟨Cq,hCq⟩ := IH m (by omega) q hq
          have hAg : ∀ i : ℕ, ∃ C : ℝ≥0,
              i ≤ m → ∀ x, |iteratedDeriv i (tiltedMean c h f g) x| ≤ C := by
            intro i
            by_cases hi : i ≤ m
            · obtain ⟨C,hC⟩ := IH i (by omega) g hg
              exact ⟨C, fun _ => hC⟩
            · exact ⟨0, fun hi' => (hi hi').elim⟩
          have hBg : ∀ i : ℕ, ∃ C : ℝ≥0,
              i ≤ m → ∀ x, |iteratedDeriv i (tiltedMean c h f (deriv f)) x| ≤ C := by
            intro i
            by_cases hi : i ≤ m
            · obtain ⟨C,hC⟩ := IH i (by omega) (deriv f) hf.deriv_bounded
              exact ⟨C, fun _ => hC⟩
            · exact ⟨0, fun hi' => (hi hi').elim⟩
          choose A hA using hAg
          choose B hB using hBg
          let Cprod : ℝ≥0 := ∑ i ∈ Finset.range (m+1), (m.choose i:ℝ≥0)*A i*B (m-i)
          refine ⟨Cq+⟨|c|, abs_nonneg c⟩*Cprod, fun x => ?_⟩
          rw [iteratedDeriv_succ', deriv_tiltedMean hf hLip hg hc h]
          have hcg := contDiff_tiltedMean hf hLip hg hc h
          have hcdf := contDiff_tiltedMean hf hLip hf.deriv_bounded hc h
          have hcq := contDiff_tiltedMean hf hLip hq hc h
          have he : (fun x => tiltedMean c h f q x-c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) =
              (fun x => tiltedMean c h f q x-c*(tiltedMean c h f g x*tiltedMean c h f (deriv f) x)) := by
            funext x; ring
          change |iteratedDeriv m (fun x => tiltedMean c h f q x-
            c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) x| ≤ _
          rw [he, iteratedDeriv_fun_sub (n := m) (hcq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt)
            (contDiff_const.mul (hcg.mul hcdf) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt),
            iteratedDeriv_const_mul_field]
          have hp := iteratedDeriv_mul_bound m (hcg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)) (hcdf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
            A B hA hB x
          have hp' : |iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| ≤ Cprod := by
            simpa only [Cprod, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast] using hp
          calc
            _ ≤ |iteratedDeriv m (tiltedMean c h f q) x| +
                |c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| := by
                  have hh := norm_sub_le (iteratedDeriv m (tiltedMean c h f q) x)
                    (c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x)
                  simpa only [Real.norm_eq_abs] using hh
            _ ≤ (Cq:ℝ)+|c| *(Cprod:ℝ) := by rw [abs_mul]; gcongr; exact hCq x
            _ = _ := rfl
    exact fun n => hbounds n g hg

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Const
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma RegularDatum.const (a : ℝ) : RegularDatum (fun _ : ℝ => a) := by
  refine ⟨contDiff_const, ?_⟩
  simpa only [deriv_const'] using BoundedSmooth.const 0

lemma boundedSmooth_semigroup {g : ℝ → ℝ} (hg : BoundedSmooth g) (h : ℝ≥0) :
    BoundedSmooth (semigroup h g) := by
  have hm := boundedSmooth_tiltedMean (RegularDatum.const 0)
    (LipschitzWith.const (0:ℝ)) hg (c := 0) le_rfl h
  have he : tiltedMean 0 h (fun _ => 0) g = semigroup h g := by
    funext x; simp [tiltedMean, semigroup]
  rw [he] at hm
  exact hm

lemma regularDatum_semigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (h : ℝ≥0) :
    RegularDatum (semigroup h f) := by
  have he : deriv (semigroup h f) = semigroup h (deriv f) := funext (fun x =>
    (hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h x).deriv)
  have hd := boundedSmooth_semigroup hf.deriv_bounded h
  constructor
  · apply contDiff_infty_iff_deriv.mpr
    constructor
    · exact fun x => (hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h x).differentiableAt
    · rw [he]; exact hd.smooth
  · rw [he]; exact hd

lemma regularDatum_logSemigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (h : ℝ≥0) : RegularDatum (logSemigroup c h f) := by
  by_cases hc0 : c = 0
  · subst c
    have he : logSemigroup 0 h f = semigroup h f := by funext x; simp [logSemigroup]
    rw [he]; exact regularDatum_semigroup hf hLip h
  have hder : deriv (logSemigroup c h f) = tiltedMean c h f (deriv f) := by
    funext x
    exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip (lt_of_le_of_ne hc (Ne.symm hc0)) h x).deriv
  have hd := boundedSmooth_tiltedMean hf hLip hf.deriv_bounded hc h
  constructor
  · apply contDiff_infty_iff_deriv.mpr
    constructor
    · intro x
      exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip (lt_of_le_of_ne hc (Ne.symm hc0)) h x).differentiableAt
    · rw [hder]; exact hd.smooth
  · rw [hder]; exact hd

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma ExponentialBound.of_bounded {g : ℝ → ℝ} {A : ℝ≥0} (hA : ∀ z, |g z| ≤ A) :
    ExponentialBound g := by
  exact ⟨A, 0, fun z => by simpa using hA z⟩

lemma semigroup_eq_scaled {g : ℝ → ℝ} (hgm : Measurable g) (h : ℝ≥0) (x : ℝ) :
    semigroup h g x = scaled (Real.sqrt (h:ℝ)) g x := by
  have hs : (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt (h:ℝ)*y) = gaussianReal 0 h := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt h.coe_nonneg]
  unfold semigroup scaled
  rw [← hs]
  exact integral_map (by fun_prop)
    (show AEStronglyMeasurable (fun y => g (x+y)) _ from
      (hgm.comp (measurable_const.add measurable_id)).aestronglyMeasurable)

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.VarianceHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma varianceHeat_zero (g : ℝ → ℝ) (x : ℝ) : varianceHeat 0 g x = g x := by
  simp [varianceHeat, scaled]

lemma varianceHeat_eq_semigroup {g : ℝ → ℝ} (hgm : Measurable g) (h : ℝ≥0) (x : ℝ) :
    varianceHeat h g x = semigroup h g x := (semigroup_eq_scaled hgm h x).symm

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.ExponentialBoundLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma exponentialBound_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ExponentialBound f := by
  refine ⟨Real.nnabs (f 0)+K, 1, fun z => ?_⟩
  have hl := hf.norm_sub_le z 0
  have ht := norm_add_le (f z-f 0) (f 0)
  simp only [sub_zero, sub_add_cancel, Real.norm_eq_abs] at hl ht
  have he : |z| ≤ Real.exp |z| := by linarith [Real.add_one_le_exp |z|]
  have he1 : 1 ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
  simp only [NNReal.coe_add, Real.coe_nnabs, NNReal.coe_one, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left he K.coe_nonneg,
    mul_le_mul_of_nonneg_left he1 (abs_nonneg (f 0))]

lemma exponentialBound_exp {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (c : ℝ) :
    ExponentialBound (fun z => Real.exp (c*f z)) := by
  refine ⟨⟨Real.exp (c*f 0), (Real.exp_pos _).le⟩, Real.nnabs c*K, fun z => ?_⟩
  rw [abs_of_pos (Real.exp_pos _)]
  change Real.exp (c*f z) ≤ Real.exp (c*f 0)*Real.exp ((|c| *(K:ℝ))*|z|)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := hf.norm_sub_le z 0
  simp only [sub_zero, Real.norm_eq_abs] at hl
  have h₁ : c*(f z-f 0) ≤ |c| *|f z-f 0| := by
    exact (le_abs_self _).trans_eq (abs_mul _ _)
  nlinarith [mul_le_mul_of_nonneg_left hl (abs_nonneg c)]

lemma ExponentialBound.bdd_mul {f g : ℝ → ℝ} (hf : ExponentialBound f)
    {G : ℝ≥0} (hg : ∀ z, |g z| ≤ G) : ExponentialBound (fun z => g z*f z) := by
  obtain ⟨A,K,hf⟩ := hf
  refine ⟨G*A, K, fun z => ?_⟩
  rw [abs_mul]
  have hh := mul_le_mul (hg z) (hf z) (abs_nonneg (f z)) G.coe_nonneg
  simpa only [NNReal.coe_mul, mul_assoc] using hh

lemma hasDerivAt_weightExp {f g : ℝ → ℝ} (hf : RegularDatum f) (hg : BoundedSmooth g)
    (c x : ℝ) : HasDerivAt (fun z => g z*Real.exp (c*f z))
      ((deriv g x+c*g x*deriv f x)*Real.exp (c*f x)) x := by
  have hfd := (hf.smooth.differentiable (by simp) x).hasDerivAt
  have hgd := (hg.smooth.differentiable (by simp) x).hasDerivAt
  convert hgd.mul (hfd.const_mul c).exp using 1 <;> try rfl
  first | rfl | ring

lemma deriv_weightExp {f g : ℝ → ℝ} (hf : RegularDatum f) (hg : BoundedSmooth g) (c : ℝ) :
    deriv (fun z => g z*Real.exp (c*f z)) = fun x =>
      (deriv g x+c*g x*deriv f x)*Real.exp (c*f x) :=
  funext (fun x => (hasDerivAt_weightExp hf hg c x).deriv)

lemma exp_iteratedDeriv_weight {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) (n : ℕ) :
    ∃ g : ℝ → ℝ, BoundedSmooth g ∧
      iteratedDeriv n (fun z => Real.exp (c*f z)) = fun z => g z*Real.exp (c*f z) := by
  induction n with
  | zero => exact ⟨fun _ => 1, BoundedSmooth.const 1, by funext z; simp⟩
  | succ n IH =>
    obtain ⟨g,hg,he⟩ := IH
    exact ⟨fun z => deriv g z+c*g z*deriv f z, weighted_derivative_boundedSmooth hf hg c,
      by rw [iteratedDeriv_succ, he, deriv_weightExp hf hg c]⟩

lemma exponentialBound_exp_iteratedDeriv {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ) (n : ℕ) :
    ExponentialBound (iteratedDeriv n (fun z => Real.exp (c*f z))) := by
  obtain ⟨g,hg,he⟩ := exp_iteratedDeriv_weight hf c n
  obtain ⟨G,hG⟩ := hg.bound
  rw [he]
  exact (exponentialBound_exp hLip c).bdd_mul hG

lemma hasDerivWithinAt_varianceHeat_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s (fun z => Real.exp (c*f z)) x)
      ((1/2:ℝ)*varianceHeat t (deriv (deriv (fun z => Real.exp (c*f z)))) x)
      (Set.Ici 0) t := by
  apply hasDerivWithinAt_varianceHeat
    ((contDiff_const.mul hf.smooth).exp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (exponentialBound_exp hLip c)
    (by simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using exponentialBound_exp_iteratedDeriv hf hLip c 2)
    ht x

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma varianceHeat_equation {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s g x)
      ((1/2:ℝ)*deriv (deriv (varianceHeat t g)) x) (Set.Ici 0) t :=
  gaussian_heat_equation hgc hg hg' hg'' ht x

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma logarithmic_heat_equation {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {c : ℝ} (hc : c ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (hpos : ∀ z, 0 < varianceHeat t g z) (x : ℝ) :
    HasDerivWithinAt (fun s => Real.log (varianceHeat s g x)/c)
      ((1/2:ℝ)*deriv (deriv (fun z => Real.log (varianceHeat t g z)/c)) x +
        c/2*(deriv (fun z => Real.log (varianceHeat t g z)/c) x)^2)
      (Set.Ici 0) t :=
  gaussian_cole_hopf hgc hg hg' hg'' hc ht hpos x

def varianceLogHeat (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  if c = 0 then varianceHeat t f x else Real.log (varianceHeat t (fun z => Real.exp (c*f z)) x)/c

lemma varianceLogHeat_eq_logSemigroup {f : ℝ → ℝ} (hfm : Measurable f) (c : ℝ)
    (h : ℝ≥0) (x : ℝ) : varianceLogHeat c h f x = logSemigroup c h f x := by
  by_cases hc : c = 0
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    exact varianceHeat_eq_semigroup hfm h x
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    have hem : Measurable (fun z => Real.exp (c*f z)) := (measurable_const.mul hfm).exp
    rw [varianceHeat_eq_semigroup hem h x]

lemma varianceHeat_exp_pos {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c t x : ℝ) : 0 < varianceHeat t (fun z => Real.exp (c*f z)) x := by
  unfold varianceHeat scaled
  exact integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
    (integrable_scaled_of_expBound (measurable_const.mul hf.continuous.measurable |>.exp)
      (exponentialBound_exp hf c) (Real.sqrt t) x) |>.mpr (by simp [Function.support])

lemma varianceLogHeat_equation {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceLogHeat c s f x)
      ((1/2:ℝ)*deriv (deriv (varianceLogHeat c t f)) x +
        c/2*(deriv (varianceLogHeat c t f) x)^2) (Set.Ici 0) t := by
  by_cases hc : c = 0
  · subst c
    have he : (fun s => varianceLogHeat 0 s f x) = fun s => varianceHeat s f x := by
      funext s; simp [varianceLogHeat]
    have he' : varianceLogHeat 0 t f = varianceHeat t f := by funext z; simp [varianceLogHeat]
    rw [he, he']
    simp only [zero_div, zero_mul, add_zero]
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bound
    obtain ⟨C',hC'⟩ := hf.deriv_bounded.deriv.bound
    exact varianceHeat_equation (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (exponentialBound_of_lipschitz hLip)
      (ExponentialBound.of_bounded hC) (ExponentialBound.of_bounded hC') ht x
  · have he : (fun s => varianceLogHeat c s f x) = fun s =>
        Real.log (varianceHeat s (fun z => Real.exp (c*f z)) x)/c := by funext s; simp [varianceLogHeat, hc]
    have he' : varianceLogHeat c t f = fun z =>
        Real.log (varianceHeat t (fun y => Real.exp (c*f y)) z)/c := by funext z; simp [varianceLogHeat, hc]
    rw [he, he']
    exact logarithmic_heat_equation ((contDiff_const.mul hf.smooth).exp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (exponentialBound_exp hLip c)
      (by simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1)
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using exponentialBound_exp_iteratedDeriv hf hLip c 2)
      hc ht (varianceHeat_exp_pos hLip c t) x

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.UniformTiltedMeanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma uniform_tiltedMean_bounds {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) :
    ∀ n : ℕ, ∃ C : ℝ≥0, ∀ h : ℝ≥0, ∀ x,
      |iteratedDeriv n (tiltedMean c h f g) x| ≤ C := by
  classical
  have hbounds : ∀ n : ℕ, ∀ g : ℝ → ℝ, BoundedSmooth g →
      ∃ C : ℝ≥0, ∀ h : ℝ≥0, ∀ x, |iteratedDeriv n (tiltedMean c h f g) x| ≤ C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n IH =>
      intro g hg
      cases n with
      | zero =>
        obtain ⟨G,hG⟩ := hg.bound
        refine ⟨G, fun h x => ?_⟩
        simpa only [iteratedDeriv_zero] using
          (tiltedMean_bound hLip hg.smooth.continuous.measurable hG c h x)
      | succ m =>
        let q (z : ℝ) := deriv g z+c*g z*deriv f z
        have hq : BoundedSmooth q := weighted_derivative_boundedSmooth hf hg c
        obtain ⟨Cq,hCq⟩ := IH m (by omega) q hq
        have hAg : ∀ i : ℕ, ∃ C : ℝ≥0,
            i ≤ m → ∀ h : ℝ≥0, ∀ x, |iteratedDeriv i (tiltedMean c h f g) x| ≤ C := by
          intro i
          by_cases hi : i ≤ m
          · obtain ⟨C,hC⟩ := IH i (by omega) g hg
            exact ⟨C, fun _ => hC⟩
          · exact ⟨0, fun hi' => (hi hi').elim⟩
        have hBg : ∀ i : ℕ, ∃ C : ℝ≥0,
            i ≤ m → ∀ h : ℝ≥0, ∀ x, |iteratedDeriv i (tiltedMean c h f (deriv f)) x| ≤ C := by
          intro i
          by_cases hi : i ≤ m
          · obtain ⟨C,hC⟩ := IH i (by omega) (deriv f) hf.deriv_bounded
            exact ⟨C, fun _ => hC⟩
          · exact ⟨0, fun hi' => (hi hi').elim⟩
        choose A hA using hAg
        choose B hB using hBg
        let Cprod : ℝ≥0 := ∑ i ∈ Finset.range (m+1), (m.choose i:ℝ≥0)*A i*B (m-i)
        refine ⟨Cq+⟨|c|, abs_nonneg c⟩*Cprod, fun h x => ?_⟩
        rw [iteratedDeriv_succ', deriv_tiltedMean hf hLip hg hc h]
        have hcg := contDiff_tiltedMean hf hLip hg hc h
        have hcdf := contDiff_tiltedMean hf hLip hf.deriv_bounded hc h
        have hcq := contDiff_tiltedMean hf hLip hq hc h
        have he : (fun x => tiltedMean c h f q x-c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) =
            (fun x => tiltedMean c h f q x-c*(tiltedMean c h f g x*tiltedMean c h f (deriv f) x)) := by
          funext x; ring
        change |iteratedDeriv m (fun x => tiltedMean c h f q x-
          c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) x| ≤ _
        rw [he, iteratedDeriv_fun_sub (n := m) (hcq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt)
          (contDiff_const.mul (hcg.mul hcdf) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt),
          iteratedDeriv_const_mul_field]
        have hp := iteratedDeriv_mul_bound m (hcg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)) (hcdf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
          A B (fun i hi => hA i hi h) (fun i hi => hB i hi h) x
        have hp' : |iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| ≤ Cprod := by
          simpa only [Cprod, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast] using hp
        calc
          _ ≤ |iteratedDeriv m (tiltedMean c h f q) x| +
              |c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| := by
                have hh := norm_sub_le (iteratedDeriv m (tiltedMean c h f q) x)
                  (c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x)
                simpa only [Real.norm_eq_abs] using hh
          _ ≤ (Cq:ℝ)+|c| *(Cprod:ℝ) := by rw [abs_mul]; gcongr; exact hCq h x
          _ = _ := rfl
  exact fun n => hbounds n g hg

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.VarianceTilted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma varianceHeat_eq_semigroup_toNNReal {g : ℝ → ℝ} (hgm : Measurable g) (t x : ℝ) :
    varianceHeat t g x = semigroup (Real.toNNReal t) g x := by
  rw [semigroup_eq_scaled hgm]
  unfold varianceHeat
  have he : Real.sqrt ((Real.toNNReal t:ℝ≥0):ℝ) = Real.sqrt t := by
    simp only [Real.sqrt, Real.toNNReal_coe]
  rw [he]

lemma varianceLogHeat_eq_logSemigroup_toNNReal {f : ℝ → ℝ} (hfm : Measurable f) (c t x : ℝ) :
    varianceLogHeat c t f x = logSemigroup c (Real.toNNReal t) f x := by
  by_cases hc : c = 0
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    exact varianceHeat_eq_semigroup_toNNReal hfm t x
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    have hem : Measurable (fun z => Real.exp (c*f z)) := (measurable_const.mul hfm).exp
    rw [varianceHeat_eq_semigroup_toNNReal hem t x]

lemma uniform_logSemigroup_derivative_bounds {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ h : ℝ≥0, ∀ x, |iteratedDeriv (n+1) (logSemigroup c h f) x| ≤ C := by
  by_cases hc0 : c = 0
  · subst c
    obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds (RegularDatum.const 0)
      (LipschitzWith.const (0:ℝ)) hf.deriv_bounded (c := 0) le_rfl n
    refine ⟨C, fun h x => ?_⟩
    have he : logSemigroup 0 h f = semigroup h f := by funext z; simp [logSemigroup]
    have hd : deriv (semigroup h f) = semigroup h (deriv f) := funext (fun z =>
      (hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h z).deriv)
    have hm : tiltedMean 0 h (fun _ => 0) (deriv f) = semigroup h (deriv f) := by
      funext z; simp [tiltedMean, semigroup]
    rw [he, iteratedDeriv_succ', hd]
    simpa only [hm] using hC h x
  · obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds hf hLip hf.deriv_bounded hc n
    refine ⟨C, fun h x => ?_⟩
    have hd : deriv (logSemigroup c h f) = tiltedMean c h f (deriv f) := funext (fun z =>
      (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip (lt_of_le_of_ne hc (Ne.symm hc0)) h z).deriv)
    rw [iteratedDeriv_succ', hd]
    exact hC h x

lemma regularDatum_varianceLogHeat {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    RegularDatum (varianceLogHeat c t f) := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  exact regularDatum_logSemigroup hf hLip hc _

lemma uniform_varianceLogHeat_derivative_bounds {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ t x : ℝ, |iteratedDeriv (n+1) (varianceLogHeat c t f) x| ≤ C := by
  obtain ⟨C,hC⟩ := uniform_logSemigroup_derivative_bounds hf hLip hc n
  refine ⟨C, fun t x => ?_⟩
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  exact hC _ x

lemma varianceLogHeat_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : LipschitzWith K (varianceLogHeat c t f) := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.continuous.measurable c t)
  rw [he]
  exact logSemigroup_lipschitz hf hc _

def varianceTilted (c t : ℝ) (f g : ℝ → ℝ) (x : ℝ) :=
  varianceHeat t (fun z => g z*Real.exp (c*f z)) x /
    varianceHeat t (fun z => Real.exp (c*f z)) x

lemma varianceTilted_eq_tiltedMean {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (c t x : ℝ) : varianceTilted c t f g x = tiltedMean c (Real.toNNReal t) f g x := by
  unfold varianceTilted tiltedMean
  have hwm : Measurable (fun z => g z*Real.exp (c*f z)) := hgm.mul ((measurable_const.mul hfm).exp)
  have hem : Measurable (fun z => Real.exp (c*f z)) := (measurable_const.mul hfm).exp
  rw [varianceHeat_eq_semigroup_toNNReal hwm t x, varianceHeat_eq_semigroup_toNNReal hem t x]

lemma varianceTilted_bound {f g : ℝ → ℝ} {K G : ℝ≥0} (hf : LipschitzWith K f)
    (hgm : Measurable g) (hG : ∀ z, |g z| ≤ G) (c t x : ℝ) :
    |varianceTilted c t f g x| ≤ G := by
  rw [varianceTilted_eq_tiltedMean hf.continuous.measurable hgm]
  exact tiltedMean_bound hf hgm hG c _ x

lemma weightExp_iteratedDeriv_weight {f g : ℝ → ℝ} (hf : RegularDatum f)
    (hg : BoundedSmooth g) (c : ℝ) (n : ℕ) :
    ∃ q : ℝ → ℝ, BoundedSmooth q ∧
      iteratedDeriv n (fun z => g z*Real.exp (c*f z)) = fun z => q z*Real.exp (c*f z) := by
  induction n with
  | zero => exact ⟨g, hg, by funext z; simp⟩
  | succ n IH =>
    obtain ⟨q,hq,he⟩ := IH
    exact ⟨fun z => deriv q z+c*q z*deriv f z, weighted_derivative_boundedSmooth hf hq c,
      by rw [iteratedDeriv_succ, he, deriv_weightExp hf hq c]⟩

lemma exponentialBound_weightExp_iteratedDeriv {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) (n : ℕ) :
    ExponentialBound (iteratedDeriv n (fun z => g z*Real.exp (c*f z))) := by
  obtain ⟨q,hq,he⟩ := weightExp_iteratedDeriv_weight hf hg c n
  obtain ⟨G,hG⟩ := hq.bound
  rw [he]
  exact (exponentialBound_exp hLip c).bdd_mul hG

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.DerivWithinVarianceHeatWeightExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma hasDerivWithinAt_varianceHeat_weightExp {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s (fun z => g z*Real.exp (c*f z)) x)
      ((1/2:ℝ)*varianceHeat t (deriv (deriv (fun z => g z*Real.exp (c*f z)))) x)
      (Set.Ici 0) t := by
  exact hasDerivWithinAt_varianceHeat
    ((hg.smooth.mul (contDiff_const.mul hf.smooth).exp).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (by simpa only [iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 0)
    (by simpa only [iteratedDeriv_one] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 1)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      exponentialBound_weightExp_iteratedDeriv hf hLip hg c 2) ht x

lemma hasDerivWithinAt_varianceTilted {f g q r : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ)
    (hq : deriv (deriv (fun z => g z*Real.exp (c*f z))) = fun z => q z*Real.exp (c*f z))
    (hr : deriv (deriv (fun z => Real.exp (c*f z))) = fun z => r z*Real.exp (c*f z))
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceTilted c s f g x)
      ((1/2:ℝ)*(varianceTilted c t f q x-varianceTilted c t f g x*varianceTilted c t f r x))
      (Set.Ici 0) t := by
  have hd := (hasDerivWithinAt_varianceHeat_weightExp hf hLip hg c ht x).div
    (hasDerivWithinAt_varianceHeat_exp hf hLip c ht x)
    (ne_of_gt (varianceHeat_exp_pos hLip c t x))
  rw [hq, hr] at hd
  convert hd using 1 <;> try rfl
  all_goals
    try dsimp only [varianceTilted]
    field_simp [ne_of_gt (varianceHeat_exp_pos hLip c t x)]

lemma varianceTilted_time_lipschitz {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) :
    ∃ C : ℝ≥0, ∀ x, LipschitzOnWith C (fun t => varianceTilted c t f g x) (Set.Ici 0) := by
  obtain ⟨q,hqs,hq⟩ := weightExp_iteratedDeriv_weight hf hg c 2
  obtain ⟨r,hrs,hr⟩ := exp_iteratedDeriv_weight hf c 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hq hr
  obtain ⟨Q,hQ⟩ := hqs.bound
  obtain ⟨R,hR⟩ := hrs.bound
  obtain ⟨G,hG⟩ := hg.bound
  refine ⟨(Q+G*R)/2, fun x => ?_⟩
  apply (convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => hasDerivWithinAt_varianceTilted hf hLip hg c hq hr ht x)
  intro t ht
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_mul, NNReal.coe_ofNat]
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hb : |varianceTilted c t f q x-varianceTilted c t f g x*varianceTilted c t f r x| ≤
      (Q:ℝ)+(G:ℝ)*(R:ℝ) := by
    calc
      _ ≤ |varianceTilted c t f q x|+|varianceTilted c t f g x*varianceTilted c t f r x| := abs_sub _ _
      _ ≤ (Q:ℝ)+(G:ℝ)*(R:ℝ) := by
        apply add_le_add (varianceTilted_bound hLip hqs.smooth.continuous.measurable hQ c t x)
        rw [abs_mul]
        exact mul_le_mul
          (varianceTilted_bound hLip hg.smooth.continuous.measurable hG c t x)
          (varianceTilted_bound hLip hrs.smooth.continuous.measurable hR c t x)
          (abs_nonneg _) G.coe_nonneg
  linarith

lemma varianceTilted_space_lipschitz {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ≥0, ∀ t, LipschitzWith C (varianceTilted c t f g) := by
  obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds hf hLip hg hc 1
  refine ⟨C, fun t => ?_⟩
  have he : varianceTilted c t f g = tiltedMean c (Real.toNNReal t) f g :=
    funext (varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable
      hg.smooth.continuous.measurable c t)
  rw [he]
  apply lipschitzWith_of_nnnorm_deriv_le
    ((contDiff_tiltedMean hf hLip hg hc _).differentiable (by simp))
  intro x
  exact NNReal.coe_le_coe.mp (by
    simpa only [coe_nnnorm, Real.norm_eq_abs, iteratedDeriv_one] using (hC (Real.toNNReal t) x))

lemma varianceTilted_joint_bound {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ L : ℝ≥0, ∀ t ∈ Set.Ici (0:ℝ), ∀ s ∈ Set.Ici (0:ℝ), ∀ x y,
      |varianceTilted c t f g x-varianceTilted c s f g y| ≤ (L:ℝ)*(|t-s|+|x-y|) := by
  obtain ⟨A,hA⟩ := varianceTilted_time_lipschitz hf hLip hg c
  obtain ⟨B,hB⟩ := varianceTilted_space_lipschitz hf hLip hg hc
  refine ⟨A+B, fun t ht s hs x y => ?_⟩
  have ha := (hA x).dist_le_mul t ht s hs
  have hb := (hB s).dist_le_mul x y
  simp only [Real.dist_eq] at ha hb
  have htri := abs_sub_le (varianceTilted c t f g x) (varianceTilted c s f g x)
    (varianceTilted c s f g y)
  simp only [NNReal.coe_add]
  nlinarith [mul_nonneg A.coe_nonneg (abs_nonneg (x-y)),
    mul_nonneg B.coe_nonneg (abs_nonneg (t-s))]

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma varianceHeat_const_mul (a t : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    varianceHeat t (fun z => a*g z) x = a*varianceHeat t g x := by
  exact integral_const_mul a _

lemma varianceTilted_zero (t : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    varianceTilted 0 t f g x = varianceHeat t g x := by
  simp [varianceTilted, varianceHeat, scaled]

def generatorWeight (c : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun z => deriv (deriv f) z+c*(deriv f z)^2

lemma boundedSmooth_generatorWeight {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) :
    BoundedSmooth (generatorWeight c f) := by
  have hh := hf.deriv_bounded.deriv.add ((hf.deriv_bounded.mul hf.deriv_bounded).const_mul c)
  change BoundedSmooth (fun z => deriv (deriv f) z+c*(deriv f z)^2)
  simpa only [pow_two] using hh

lemma deriv_exp_comp {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) :
    deriv (fun z => Real.exp (c*f z)) = fun z => c*deriv f z*Real.exp (c*f z) := by
  funext z
  convert (((hf.smooth.differentiable (by simp) z).hasDerivAt.const_mul c).exp).deriv using 1 <;> try rfl
  ring

lemma deriv_deriv_exp_comp {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) :
    deriv (deriv (fun z => Real.exp (c*f z))) =
      fun z => c*(generatorWeight c f z*Real.exp (c*f z)) := by
  rw [deriv_exp_comp hf c, deriv_weightExp hf (hf.deriv_bounded.const_mul c) c]
  funext z
  have hd : deriv (fun z => c*deriv f z) z = c*deriv (deriv f) z :=
    (((hf.deriv_bounded.smooth.differentiable (by simp) z).hasDerivAt).const_mul c).deriv
  simp only [hd, generatorWeight]
  ring

lemma varianceLogHeat_time_derivative {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceLogHeat c s f x)
      ((1/2:ℝ)*varianceTilted c t f (generatorWeight c f) x) (Set.Ici 0) t := by
  by_cases hc : c = 0
  · subst c
    have he : (fun s => varianceLogHeat 0 s f x) = fun s => varianceHeat s f x := by
      funext s; simp [varianceLogHeat]
    rw [he, varianceTilted_zero]
    have hw : generatorWeight 0 f = deriv (deriv f) := by funext z; simp [generatorWeight]
    rw [hw]
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bound
    obtain ⟨C',hC'⟩ := hf.deriv_bounded.deriv.bound
    exact hasDerivWithinAt_varianceHeat
      (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (exponentialBound_of_lipschitz hLip) (ExponentialBound.of_bounded hC)
      (ExponentialBound.of_bounded hC') ht x
  · have hd := ((hasDerivWithinAt_varianceHeat_exp hf hLip c ht x).log
        (ne_of_gt (varianceHeat_exp_pos hLip c t x))).div_const c
    have he : (fun s => varianceLogHeat c s f x) = fun s =>
        Real.log (varianceHeat s (fun z => Real.exp (c*f z)) x)/c := by
      funext s; simp [varianceLogHeat, hc]
    rw [he]
    rw [deriv_deriv_exp_comp hf c, varianceHeat_const_mul] at hd
    convert hd using 1 <;> try rfl
    dsimp only [varianceTilted]
    field_simp [hc, ne_of_gt (varianceHeat_exp_pos hLip c t x)]

lemma varianceLogHeat_generator_identity {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    (1/2:ℝ)*varianceTilted c t f (generatorWeight c f) x =
      (1/2:ℝ)*deriv (deriv (varianceLogHeat c t f)) x+
        c/2*(deriv (varianceLogHeat c t f) x)^2 := by
  have h₁ := (varianceLogHeat_time_derivative hf hLip c ht x).derivWithin
    (uniqueDiffOn_Ici (0:ℝ) t ht)
  have h₂ := (varianceLogHeat_equation hf hLip c ht x).derivWithin
    (uniqueDiffOn_Ici (0:ℝ) t ht)
  exact h₁.symm.trans h₂

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.Backward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def backward (c T : ℝ) (f : ℝ → ℝ) (t x : ℝ) := varianceLogHeat c (T-t) f x

def backwardRate (c T : ℝ) (f : ℝ → ℝ) (t x : ℝ) :=
  -(1/2:ℝ)*varianceTilted c (T-t) f (generatorWeight c f) x

lemma backward_terminal (c T : ℝ) (f : ℝ → ℝ) (x : ℝ) : backward c T f T x = f x := by
  unfold backward
  rw [sub_self]
  by_cases hc : c = 0
  · simp [varianceLogHeat, hc, varianceHeat_zero]
  · simp [varianceLogHeat, hc, varianceHeat_zero, Real.log_exp, mul_div_cancel_left₀ _ hc]

structure VerificationData (F D : ℝ → ℝ → ℝ) (c T : ℝ) : Prop where
  smooth : ∀ t, ContDiff ℝ 3 (F t)
  gradient_bound : ∀ t z, |deriv (F t) z| ≤ 1
  bounds : ∃ C₂ C₃ Ct L : ℝ≥0,
    (∀ t z, |deriv (deriv (F t)) z| ≤ C₂) ∧
    (∀ t z, |iteratedDeriv 3 (F t) z| ≤ C₃) ∧
    (∀ t, Measurable (D t)) ∧
    (∀ t z, |D t z| ≤ Ct) ∧
    (∀ r ∈ Set.Icc (0:ℝ) T, ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z) (Set.Icc (0:ℝ) T) r) ∧
    (∀ r ∈ Set.Icc (0:ℝ) T, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ z y,
      |D r z-D s y| ≤ (L:ℝ)*(|r-s|+|z-y|)) ∧
    (∀ t ∈ Set.Icc (0:ℝ) T, ∀ z,
      D t z+(1/2:ℝ)*deriv (deriv (F t)) z+c/2*(deriv (F t) z)^2 = 0)

lemma backward_verificationData {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    VerificationData (backward c T f) (backwardRate c T f) c T := by
  have hw := boundedSmooth_generatorWeight hf c
  obtain ⟨C₂,hC₂⟩ := uniform_varianceLogHeat_derivative_bounds hf hLip hc 1
  obtain ⟨C₃,hC₃⟩ := uniform_varianceLogHeat_derivative_bounds hf hLip hc 2
  obtain ⟨G,hG⟩ := hw.bound
  obtain ⟨L,hL⟩ := varianceTilted_joint_bound hf hLip hw hc
  obtain ⟨A,hA⟩ := varianceTilted_space_lipschitz hf hLip hw hc
  constructor
  · intro t
    exact (regularDatum_varianceLogHeat hf hLip hc (T-t)).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t z
    exact norm_deriv_le_of_lipschitz (varianceLogHeat_lipschitz hLip hc (T-t))
  · refine ⟨C₂,C₃,G/2,L,?_,?_,?_,?_,?_,?_,?_⟩
    · intro t z
      change |deriv (deriv (varianceLogHeat c (T-t) f)) z| ≤ C₂
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hC₂ (T-t) z
    · intro t z
      exact hC₃ (T-t) z
    · intro t
      exact measurable_const.mul (hA (T-t)).continuous.measurable
    · intro t z
      dsimp only [backwardRate]
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      have hb := varianceTilted_bound hLip hw.smooth.continuous.measurable hG c (T-t) z
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith
    · intro r hr z
      have hd := (varianceLogHeat_time_derivative hf hLip c (sub_nonneg.mpr hr.2) z).comp r
        (((hasDerivAt_const r T).sub (hasDerivAt_id r)).hasDerivWithinAt (s := Set.Icc (0:ℝ) T))
        (fun (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) T) => show 0 ≤ T-s from sub_nonneg.mpr hs.2)
      convert hd using 1 <;> try rfl
      dsimp only [backwardRate]
      ring
    · intro r hr s hs z y
      have hb := hL (T-r) (sub_nonneg.mpr hr.2) (T-s) (sub_nonneg.mpr hs.2) z y
      have he : |(T-r)-(T-s)| = |r-s| := by
        rw [show (T-r)-(T-s) = -(r-s) by ring, abs_neg]
      rw [he] at hb
      dsimp only [backwardRate]
      rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      have hn := abs_nonneg (varianceTilted c (T-r) f (generatorWeight c f) z-
        varianceTilted c (T-s) f (generatorWeight c f) y)
      linarith
    · intro t ht z
      have he := varianceLogHeat_generator_identity hf hLip c (sub_nonneg.mpr ht.2) z
      change -(1/2:ℝ)*varianceTilted c (T-t) f (generatorWeight c f) z+
        (1/2:ℝ)*deriv (deriv (varianceLogHeat c (T-t) f)) z+
        c/2*(deriv (varianceLogHeat c (T-t) f) z)^2 = 0
      linarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.SoftAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma boundedSmooth_of_polynomial_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {C : ℝ≥0} (hC : ∀ x, |f x| ≤ C) (P : Polynomial ℝ)
    (hD : ∀ x, deriv f x = P.eval (f x)) : BoundedSmooth f := by
  have hrepr : ∀ n : ℕ, ∃ Q : Polynomial ℝ, iteratedDeriv n f = fun x => Q.eval (f x) := by
    intro n
    induction n with
    | zero => exact ⟨Polynomial.X, by funext x; simp⟩
    | succ n IH =>
      obtain ⟨Q,hQ⟩ := IH
      refine ⟨Q.derivative*P, ?_⟩
      rw [iteratedDeriv_succ, hQ]
      funext x
      have hd := (Q.hasDerivAt (f x)).comp x ((hf.differentiable (by simp) x).hasDerivAt)
      simpa only [Function.comp_def, hD, Polynomial.eval_mul] using hd.deriv
  refine ⟨hf, fun n => ?_⟩
  obtain ⟨Q,hQ⟩ := hrepr n
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(C:ℝ)) C)).bddAbove_image
    Q.continuous.abs.continuousOn
  refine ⟨Real.toNNReal R, fun x => ?_⟩
  rw [hQ]
  have hb : |Q.eval (f x)| ≤ R := hR ⟨f x, abs_le.mp (hC x), rfl⟩
  exact hb.trans (Real.le_coe_toNNReal R)

lemma contDiff_tanh : ContDiff ℝ ∞ Real.tanh := by
  have he : Real.tanh = fun x => Real.sinh x/Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => ne_of_gt (Real.cosh_pos x))

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1-(Real.tanh x)^2) x := by
  have hne := ne_of_gt (Real.cosh_pos x)
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hne
  have he : Real.tanh = fun y => Real.sinh y/Real.cosh y := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  convert hd using 1 <;> try rfl
  field_simp

lemma boundedSmooth_tanh_mul (M : ℝ) : BoundedSmooth (fun x => Real.tanh (M*x)) := by
  apply boundedSmooth_of_polynomial_deriv
    (contDiff_tanh.comp (contDiff_const.mul contDiff_id))
    (C := 1) (fun x => (Real.abs_tanh_lt_one (M*x)).le)
    (Polynomial.C M*(1-Polynomial.X^2))
  intro x
  have hd := (hasDerivAt_tanh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  simp only [Function.comp_def, mul_one] at hd
  convert hd.deriv using 1 <;> try rfl
  all_goals
    try simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X,
      Function.comp_def, id_eq]
    ring

def softAbs (M : ℝ) (x : ℝ) := Real.log (2*Real.cosh (M*x))/M

lemma hasDerivAt_softAbs {M : ℝ} (hM : M ≠ 0) (x : ℝ) :
    HasDerivAt (softAbs M) (Real.tanh (M*x)) x := by
  have hn : 2*Real.cosh (M*x) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt (Real.cosh_pos _))
  have hd := ((((Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)).const_mul 2).log hn).div_const M
  simp only [Function.comp_def, mul_one] at hd
  convert hd using 1 <;> try rfl
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hM, ne_of_gt (Real.cosh_pos (M*x))]

lemma regularDatum_softAbs {M : ℝ} (hM : M ≠ 0) : RegularDatum (softAbs M) := by
  constructor
  · exact ((contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))).log
      (fun x => mul_ne_zero (by norm_num) (ne_of_gt (Real.cosh_pos _)))).div_const M
  · have he : deriv (softAbs M) = fun x => Real.tanh (M*x) := funext (fun x => (hasDerivAt_softAbs hM x).deriv)
    rw [he]
    exact boundedSmooth_tanh_mul M

lemma softAbs_lipschitz {M : ℝ} (hM : M ≠ 0) : LipschitzWith 1 (softAbs M) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_softAbs hM x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one, (hasDerivAt_softAbs hM x).deriv] using
    (Real.abs_tanh_lt_one (M*x)).le

lemma exp_abs_bounds (y : ℝ) :
    Real.exp |y| ≤ Real.exp y+Real.exp (-y) ∧
      Real.exp y+Real.exp (-y) ≤ 2*Real.exp |y| := by
  constructor
  · by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hy)]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  · have h₁ := Real.exp_le_exp.mpr (le_abs_self y)
    have h₂ := Real.exp_le_exp.mpr (neg_le_abs y)
    linarith

lemma softAbs_bounds {M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 ≤ softAbs M x-|x| ∧ softAbs M x-|x| ≤ Real.log 2/M := by
  have hb := exp_abs_bounds (M*x)
  have habs : |M*x| = M*|x| := by rw [abs_mul, abs_of_nonneg hM.le]
  rw [habs] at hb
  have hc : 2*Real.cosh (M*x) = Real.exp (M*x)+Real.exp (-(M*x)) := by rw [Real.cosh_eq]; ring
  have hlo := Real.log_le_log (Real.exp_pos _) hb.1
  have hhi := Real.log_le_log (add_pos (Real.exp_pos _) (Real.exp_pos _)) hb.2
  rw [Real.log_exp] at hlo
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hhi
  dsimp only [softAbs]
  rw [hc]
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hM).mpr
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hM).mpr
    field_simp
    nlinarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Cascade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def cascade (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, x => f x
  | n+1, k, x => logSemigroup (c k) h (cascade c h f n (k+1)) x

lemma cascade_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (n k : ℕ) : LipschitzWith K (cascade c h f n k) := by
  induction n generalizing k with
  | zero => exact hf
  | succ n IH => exact logSemigroup_lipschitz (IH (k+1)) (c k).coe_nonneg h

lemma cascade_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (n k : ℕ) : RegularDatum (cascade c h f n k) := by
  induction n generalizing k with
  | zero => exact hf
  | succ n IH =>
    exact regularDatum_logSemigroup (IH (k+1)) (cascade_lipschitz hLip c h n (k+1)) (c k).coe_nonneg h

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma hasFDerivAt_scaled_joint {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => scaled q.2 g q.1)
      (scaled p.2 (deriv g) p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (∫ y, y*deriv g (p.1+p.2*y) ∂gaussianReal 0 1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  obtain ⟨A,K,hA⟩ := hg'
  let L : ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun y =>
    ContinuousLinearMap.fst ℝ ℝ ℝ+y • ContinuousLinearMap.snd ℝ ℝ ℝ
  let D : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q y => deriv g (q.1+q.2*y) • L y
  let R : ℝ := (A:ℝ)*Real.exp ((K:ℝ)*(|p.1|+1))
  let k : ℝ := (K:ℝ)*(|p.2|+1)
  have hgi : Integrable (fun y => deriv g (p.1+p.2*y)) (gaussianReal 0 1) :=
    integrable_scaled_of_expBound hgc.continuous_deriv_one.measurable ⟨A,K,hA⟩ _ _
  have hygi : Integrable (fun y => y*deriv g (p.1+p.2*y)) (gaussianReal 0 1) :=
    integrable_mul_scaled_of_expBound hgc.continuous_deriv_one.measurable ⟨A,K,hA⟩ _ _
  have hDi : Integrable (D p) (gaussianReal 0 1) := by
    have hv := (hgi.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
      (hygi.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
    apply hv.congr
    filter_upwards [] with y
    simp only [D,L,smul_add,smul_smul,Pi.add_apply]
    congr 2; ring
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q : ℝ × ℝ => fun y : ℝ => g (q.1+q.2*y)) (F' := D)
    (bound := fun y : ℝ => R*(1+|y|)*Real.exp (k*|y|))
    (Metric.ball_mem_nhds p (show (0:ℝ)<1 by norm_num))
    (Filter.Eventually.of_forall (fun q => by fun_prop))
    (integrable_scaled_of_expBound hgc.continuous.measurable hg p.2 p.1)
    hDi.aestronglyMeasurable
    (by
      filter_upwards [] with y q hq
      have hx : |q.1| ≤ |p.1|+1 := by
        have hdq := (max_lt_iff.mp (show max (dist q.1 p.1) (dist q.2 p.2) < 1 from hq)).1
        rw [Real.dist_eq] at hdq
        have ht := abs_add_le (q.1-p.1) p.1
        rw [sub_add_cancel] at ht
        linarith
      have ha : |q.2| ≤ |p.2|+1 := by
        have hdq := (max_lt_iff.mp (show max (dist q.1 p.1) (dist q.2 p.2) < 1 from hq)).2
        rw [Real.dist_eq] at hdq
        have ht := abs_add_le (q.2-p.2) p.2
        rw [sub_add_cancel] at ht
        linarith
      have hL : ‖L y‖ ≤ 1+|y| := by
        apply (norm_add_le _ _).trans
        simp only [norm_smul, Real.norm_eq_abs]
        have hf : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
        have hs : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
        nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg y)]
      dsimp only [D]
      rw [norm_smul, Real.norm_eq_abs]
      have hb : |deriv g (q.1+q.2*y)| ≤ R*Real.exp (k*|y|) := by
        apply (exponentialBound_scaled hA q.1 q.2 y (|p.2|+1) ha).trans
        dsimp only [R,k]
        gcongr
      calc
        _ ≤ (R*Real.exp (k*|y|))*(1+|y|) := mul_le_mul hb hL (norm_nonneg _) (by positivity)
        _ = _ := by ring)
    (by
      have hi := ((integrable_exp_abs k 0 1).add (integrable_abs_mul_exp_abs k)).const_mul R
      convert hi using 1 <;> try rfl
      funext y; dsimp only [Pi.add_apply]; ring)
    (by
      filter_upwards [] with y q hq
      have hl : HasFDerivAt (fun q : ℝ × ℝ => q.1+q.2*y) (L y) q := by
        convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).add
          ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).mul_const y)) using 1 <;> try rfl
      convert (hgc.differentiable (by norm_num) (q.1+q.2*y)).hasDerivAt.comp_hasFDerivAt q hl using 1 <;> try rfl
      )
  have heq : (∫ y, D p y ∂gaussianReal 0 1) =
      scaled p.2 (deriv g) p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (∫ y, y*deriv g (p.1+p.2*y) ∂gaussianReal 0 1) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro z
    rw [ContinuousLinearMap.integral_apply hDi]
    dsimp only [D,L]
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    have he : (fun y => deriv g (p.1+p.2*y)*(z.1+y*z.2)) =
        fun y => deriv g (p.1+p.2*y)*z.1+(y*deriv g (p.1+p.2*y))*z.2 := by funext y; ring
    rw [he, integral_add (hgi.mul_const _) (hygi.mul_const _), integral_mul_const, integral_mul_const]
    rfl
  rw [heq] at hd
  exact hd

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.DerivVarianceHeatCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_varianceHeat_curve {g V X : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {s V' X' : ℝ}
    (hV : HasDerivAt V V' s) (hX : HasDerivAt X X' s) (hpos : 0 < V s) :
    HasDerivAt (fun r => varianceHeat (V r) g (X r))
      (V'/2*varianceHeat (V s) (deriv (deriv g)) (X s)+
        X'*varianceHeat (V s) (deriv g) (X s)) s := by
  have hrs : Real.sqrt (V s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hd := (hasFDerivAt_scaled_joint (hgc.of_le (by norm_num)) hg hg'
    (X s, Real.sqrt (V s))).comp_hasDerivAt s
    (hX.prodMk (hV.sqrt (ne_of_gt hpos)))
  have hs := (hasDerivAt_scaled (hgc.of_le (by norm_num)) hg hg'
    (Real.sqrt (V s)) (X s)).unique
    (hasDerivAt_scaled_second hgc hg hg' hg'' (Real.sqrt (V s)) (X s))
  convert hd using 1 <;> first | rfl | skip
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [hs]
  dsimp only [varianceHeat]
  field_simp [hrs]
  ring

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_varianceLogHeat_curve {f V X : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ) {s V' X' : ℝ}
    (hV : HasDerivAt V V' s) (hX : HasDerivAt X X' s) (hpos : 0 < V s) :
    HasDerivAt (fun r => varianceLogHeat c (V r) f (X r))
      (V'*((1/2:ℝ)*deriv (deriv (varianceLogHeat c (V s) f)) (X s)+
        c/2*(deriv (varianceLogHeat c (V s) f) (X s))^2)+
        X'*deriv (varianceLogHeat c (V s) f) (X s)) s := by
  by_cases hc : c = 0
  · subst c
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bound
    obtain ⟨D,hD⟩ := hf.deriv_bounded.deriv.bound
    have hfg := exponentialBound_of_lipschitz hLip
    have hfg' := ExponentialBound.of_bounded hC
    have hfg'' := ExponentialBound.of_bounded hD
    have hfc : ContDiff ℝ 2 f := hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have heF : varianceLogHeat 0 (V s) f = varianceHeat (V s) f := by funext z; simp [varianceLogHeat]
    rw [heF]
    simp only [varianceLogHeat, ↓reduceIte, zero_div, zero_mul, add_zero]
    rw [deriv_deriv_varianceHeat hfc hfg hfg' hfg'',
      deriv_varianceHeat (hfc.of_le (by norm_num)) hfg hfg']
    convert hasDerivAt_varianceHeat_curve hfc hfg hfg' hfg'' hV hX hpos using 1; ring
  · let g : ℝ → ℝ := fun z => Real.exp (c*f z)
    have hgc : ContDiff ℝ 2 g := ((contDiff_const.mul hf.smooth).exp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hg : ExponentialBound g := exponentialBound_exp hLip c
    have hg' : ExponentialBound (deriv g) := by
      simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1
    have hg'' : ExponentialBound (deriv (deriv g)) := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        exponentialBound_exp_iteratedDeriv hf hLip c 2
    have hq : varianceHeat (V s) g (X s) ≠ 0 := ne_of_gt (varianceHeat_exp_pos hLip c (V s) (X s))
    have hd := ((hasDerivAt_varianceHeat_curve hgc hg hg' hg'' hV hX hpos).log hq).div_const c
    have ht := (((hasDerivWithinAt_varianceHeat hgc hg hg' hg'' hpos.le (X s)).hasDerivAt
      (Ici_mem_nhds hpos)).log hq).div_const c
    have hteq : ((1/2:ℝ)*varianceHeat (V s) (deriv (deriv g)) (X s))/
        varianceHeat (V s) g (X s)/c =
        (1/2:ℝ)*deriv (deriv (varianceLogHeat c (V s) f)) (X s)+
          c/2*(deriv (varianceLogHeat c (V s) f) (X s))^2 := by
      apply ht.unique
      simpa only [varianceLogHeat, hc, ↓reduceIte, g] using
        (varianceLogHeat_equation hf hLip c hpos.le (X s)).hasDerivAt (Ici_mem_nhds hpos)
    have hs := ((hasDerivAt_scaled_space (hgc.of_le (by norm_num)) hg hg'
      (Real.sqrt (V s)) (X s)).log hq).div_const c
    have hseq : varianceHeat (V s) (deriv g) (X s)/varianceHeat (V s) g (X s)/c =
        deriv (varianceLogHeat c (V s) f) (X s) := by
      have heF : varianceLogHeat c (V s) f = fun z => Real.log (varianceHeat (V s) g z)/c := by
        funext z; simp only [varianceLogHeat,hc,↓reduceIte,g]
      rw [heF]
      exact hs.deriv.symm
    have hfun : (fun r => Real.log (varianceHeat (V r) g (X r))/c) =
        fun r => varianceLogHeat c (V r) f (X r) := by
      funext r; simp only [varianceLogHeat, hc, ↓reduceIte, g]
    rw [hfun] at hd
    apply hd.congr_deriv
    rw [← hteq, ← hseq]
    ring

end ZeroTemperatureSK.Heat
namespace ZeroTemperatureSK.Heat

def kernelConstant : ℝ := ∫ y : ℝ, |y| ∂gaussianReal 0 1

lemma kernelConstant_nonneg : 0 ≤ kernelConstant := integral_nonneg (fun _ => abs_nonneg _)

lemma integrable_standardGaussian_abs : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
  simpa only [zero_mul, Real.exp_zero, mul_one] using integrable_abs_mul_exp_abs 0

lemma scaled_gradient_stein {g : ℝ → ℝ} (hg : BoundedSmooth g) (a x : ℝ) :
    a * deriv (scaled a g) x = ∫ y, y*g (x+a*y) ∂gaussianReal 0 1 := by
  obtain ⟨C,hC⟩ := hg.bound
  obtain ⟨D,hD⟩ := hg.deriv.bound
  have hgc : ContDiff ℝ 1 g := hg.smooth.of_le (by simp)
  rw [(hasDerivAt_scaled_space hgc (ExponentialBound.of_bounded hC)
    (ExponentialBound.of_bounded hD) a x).deriv]
  have he := standardGaussian_stein (g := fun y => g (x+a*y))
    (g' := fun y => a*deriv g (x+a*y)) (fun y => by
      convert (hgc.differentiable (by norm_num) (x+a*y)).hasDerivAt.comp y
        (((hasDerivAt_id y).const_mul a).const_add x) using 1 <;> first | rfl | ring)
    (integrable_scaled_of_expBound hg.smooth.continuous.measurable
      (ExponentialBound.of_bounded hC) a x)
    ((integrable_scaled_of_expBound hg.deriv.smooth.continuous.measurable
      (ExponentialBound.of_bounded hD) a x).const_mul a)
    (integrable_mul_scaled_of_expBound hg.smooth.continuous.measurable
      (ExponentialBound.of_bounded hC) a x)
  simpa only [integral_const_mul, scaled] using he.symm

lemma scaled_gradient_bound {g : ℝ → ℝ} (hg : BoundedSmooth g)
    {C : ℝ≥0} (hC : ∀ z, |g z| ≤ C) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (scaled a g) x| ≤ kernelConstant * C / a := by
  have he := scaled_gradient_stein hg a x
  have hi := integrable_mul_scaled_of_expBound hg.smooth.continuous.measurable
    (ExponentialBound.of_bounded hC) a x
  have hh : |a*deriv (scaled a g) x| ≤ kernelConstant*C := by
    rw [he]
    apply abs_integral_le_integral_abs.trans
    calc
      (∫ y, |y*g (x+a*y)| ∂gaussianReal 0 1) ≤
          ∫ y : ℝ, |y| *(C:ℝ) ∂gaussianReal 0 1 := by
        apply integral_mono hi.abs (integrable_standardGaussian_abs.mul_const C)
        intro y
        change |y*g (x+a*y)| ≤ |y| *(C:ℝ)
        rw [abs_mul]
        gcongr
        exact hC _
      _ = kernelConstant*C := by rw [integral_mul_const]; rfl
  rw [abs_mul, abs_of_pos ha] at hh
  apply (le_div_iff₀ ha).mpr
  linarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.BackwardJointBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma backward_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    ∃ L : ℝ≥0, ∀ r ∈ Set.Icc (0:ℝ) b, ∀ s ∈ Set.Icc (0:ℝ) b, ∀ z y,
      |backward c b f r z-backward c b f s y| ≤ (L:ℝ)*(|r-s|+|z-y|) := by
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hd,hJ,hE⟩ := (backward_verificationData hf hLip hc b).bounds
  have ht (z : ℝ) : LipschitzOnWith Ct (fun r => backward c b f r z) (Set.Icc 0 b) := by
    apply (convex_Icc (0:ℝ) b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun r hr => hd r hr z)
    intro r hr
    exact NNReal.coe_le_coe.mp (by simpa only [coe_nnnorm,Real.norm_eq_abs] using hCt r z)
  refine ⟨Ct+1, fun r hr s hs z y => ?_⟩
  have htime := (ht z).dist_le_mul r hr s hs
  have hspace := (varianceLogHeat_lipschitz hLip hc (b-s)).dist_le_mul z y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at htime hspace
  change |backward c b f s z-backward c b f s y| ≤ |z-y| at hspace
  have htri := abs_sub_le (backward c b f r z) (backward c b f s z) (backward c b f s y)
  simp only [NNReal.coe_add, NNReal.coe_one]
  nlinarith [abs_nonneg (r-s),mul_nonneg Ct.coe_nonneg (abs_nonneg (z-y))]

lemma deriv_varianceLogHeat_tilted {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    deriv (varianceLogHeat c t f) = varianceTilted c t f (deriv f) := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  funext x
  rw [varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable
    hf.deriv_bounded.smooth.continuous.measurable]
  by_cases hc0 : c = 0
  · subst c
    have hz : logSemigroup 0 (Real.toNNReal t) f = semigroup (Real.toNNReal t) f := by
      funext z; simp [logSemigroup]
    rw [hz,(hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip (Real.toNNReal t) x).deriv]
    simp [tiltedMean,semigroup]
  · exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip
      (lt_of_le_of_ne hc (Ne.symm hc0)) (Real.toNNReal t) x).deriv

lemma backward_gradient_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    ∃ L : ℝ≥0, ∀ r ∈ Set.Icc (0:ℝ) b, ∀ s ∈ Set.Icc (0:ℝ) b, ∀ z y,
      |deriv (backward c b f r) z-deriv (backward c b f s) y| ≤ (L:ℝ)*(|r-s|+|z-y|) := by
  obtain ⟨L,hL⟩ := varianceTilted_joint_bound hf hLip hf.deriv_bounded hc
  refine ⟨L, fun r hr s hs z y => ?_⟩
  rw [show backward c b f r = varianceLogHeat c (b-r) f from rfl,
    show backward c b f s = varianceLogHeat c (b-s) f from rfl,
    deriv_varianceLogHeat_tilted hf hLip hc, deriv_varianceLogHeat_tilted hf hLip hc]
  have hb := hL (b-r) (sub_nonneg.mpr hr.2) (b-s) (sub_nonneg.mpr hs.2) z y
  have he : |(b-r)-(b-s)| = |r-s| := by rw [show (b-r)-(b-s) = -(r-s) by ring,abs_neg]
  rwa [he] at hb

lemma continuousOn_of_joint_bound {F : ℝ → ℝ → ℝ} {L : ℝ≥0} {a b : ℝ}
    (hL : ∀ r ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b, ∀ z y,
      |F r z-F s y| ≤ (L:ℝ)*(|r-s|+|z-y|)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ) := by
  have hl : LipschitzOnWith (2*L) (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    have hh := hL p.1 hp.1 q.1 hq.1 p.2 q.2
    rw [Real.dist_eq]
    have ht : |p.1-q.1| ≤ dist p q := by
      change dist p.1 q.1 ≤ max (dist p.1 q.1) (dist p.2 q.2)
      exact le_max_left _ _
    have hx : |p.2-q.2| ≤ dist p q := by
      change dist p.2 q.2 ≤ max (dist p.1 q.1) (dist p.2 q.2)
      exact le_max_right _ _
    simp only [NNReal.coe_mul,NNReal.coe_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add ht hx) L.coe_nonneg]
  exact hl.continuousOn

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_backward_curve {f X : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c b : ℝ) {s X' : ℝ}
    (hX : HasDerivAt X X' s) (hs : s < b) :
    HasDerivAt (fun r => backward c b f r (X r))
      (-(1/2:ℝ)*deriv (deriv (backward c b f s)) (X s)-
        c/2*(deriv (backward c b f s) (X s))^2+
        X'*deriv (backward c b f s) (X s)) s := by
  have hd := hasDerivAt_varianceLogHeat_curve hf hLip c
    ((hasDerivAt_const s b).sub (hasDerivAt_id s)) hX (sub_pos.mpr hs)
  simp only [Pi.sub_apply,id_eq] at hd
  rw [show backward c b f s = varianceLogHeat c (b-s) f from rfl]
  convert hd using 1 <;> first | rfl | ring

lemma hasDerivAt_moving_backward_heat {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) {a b s : ℝ}
    (has : a < s) (hsb : s < b) (x : ℝ) :
    HasDerivAt (fun r => varianceHeat (r-a) (backward c b f r) x)
      (-(c/2)*varianceHeat (s-a) (fun z => (deriv (backward c b f s) z)^2) x) s := by
  let U : ℝ → ℝ → ℝ := fun r => deriv (backward c b f r)
  let W : ℝ → ℝ → ℝ := fun r => deriv (deriv (backward c b f r))
  let D : ℝ → ℝ → ℝ := fun r y =>
    -(1/2:ℝ)*W r (x+Real.sqrt (r-a)*y)-c/2*(U r (x+Real.sqrt (r-a)*y))^2+
      (y/(2*Real.sqrt (r-a)))*U r (x+Real.sqrt (r-a)*y)
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hdt,hJ,hE⟩ := (backward_verificationData hf hLip hc b).bounds
  have hub (r z : ℝ) : |U r z| ≤ 1 := (backward_verificationData hf hLip hc b).gradient_bound r z
  have hwb (r z : ℝ) : |W r z| ≤ C₂ := h₂ r z
  have hreg (r : ℝ) : RegularDatum (backward c b f r) := regularDatum_varianceLogHeat hf hLip hc (b-r)
  have hUmeas (r : ℝ) : Measurable (U r) := (hreg r).deriv_bounded.smooth.continuous.measurable
  have hWmeas (r : ℝ) : Measurable (W r) := (hreg r).deriv_bounded.deriv.smooth.continuous.measurable
  have hsmall : 0 < (s-a)/2 := by linarith
  have hroot : 0 < Real.sqrt ((s-a)/2) := Real.sqrt_pos.mpr hsmall
  have hiF : Integrable (fun y => backward c b f s (x+Real.sqrt (s-a)*y)) (gaussianReal 0 1) :=
    integrable_scaled_of_expBound (hreg s).smooth.continuous.measurable
      (exponentialBound_of_lipschitz (varianceLogHeat_lipschitz hLip hc (b-s))) _ _
  have hDm : AEStronglyMeasurable (D s) (gaussianReal 0 1) := by
    dsimp only [D]
    exact (((measurable_const.mul ((hWmeas s).comp (by fun_prop))).sub
      (measurable_const.mul (((hUmeas s).comp (by fun_prop)).pow_const 2))).add
      ((measurable_id.div_const _).mul ((hUmeas s).comp (by fun_prop)))).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r y => backward c b f r (x+Real.sqrt (r-a)*y)) (F' := D)
    (bound := fun y : ℝ => ((C₂:ℝ)+c)/2+|y|/(2*Real.sqrt ((s-a)/2)))
    (s := Set.Ioo ((a+s)/2) b) (Ioo_mem_nhds (by linarith) hsb)
    (Filter.Eventually.of_forall (fun r => ((hreg r).smooth.continuous.measurable.comp
      (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable))
    hiF hDm
    (by
      filter_upwards [] with y r hr
      have hra : 0 < r-a := by linarith [hr.1]
      have hsr : Real.sqrt ((s-a)/2) ≤ Real.sqrt (r-a) := Real.sqrt_le_sqrt (by linarith [hr.1])
      have hratio : |y|/(2*Real.sqrt (r-a)) ≤ |y|/(2*Real.sqrt ((s-a)/2)) := by
        exact div_le_div_of_nonneg_left (abs_nonneg y) (by positivity) (by linarith)
      dsimp only [D]
      rw [Real.norm_eq_abs]
      apply (abs_add_le _ _).trans
      apply (add_le_add (abs_sub _ _) le_rfl).trans
      have hU := hub r (x+Real.sqrt (r-a)*y)
      have hW := hwb r (x+Real.sqrt (r-a)*y)
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2), abs_mul,
        abs_of_nonneg (div_nonneg hc (by norm_num)), abs_pow,
        abs_mul, abs_div, abs_of_pos (show 0 < 2*Real.sqrt (r-a) by positivity)]
      have hU2 : |U r (x+Real.sqrt (r-a)*y)|^2 ≤ 1 := by nlinarith [abs_nonneg (U r (x+Real.sqrt (r-a)*y))]
      have hUterm := mul_le_mul_of_nonneg_left hU (show 0 ≤ |y|/(2*Real.sqrt (r-a)) by positivity)
      have hU2term := mul_le_mul_of_nonneg_left hU2 (div_nonneg hc (by norm_num : (0:ℝ)≤2))
      nlinarith)
    ((integrable_const _).add (integrable_standardGaussian_abs.div_const _))
    (by
      filter_upwards [] with y r hr
      have hra : 0 < r-a := by linarith [hr.1]
      have hX : HasDerivAt (fun t : ℝ => x+Real.sqrt (t-a)*y)
          (y/(2*Real.sqrt (r-a))) r := by
        convert ((((hasDerivAt_id r).sub_const a).sqrt (ne_of_gt hra)).mul_const y).const_add x using 1 <;> first | rfl | (simp only [id_eq]; ring)
      exact hasDerivAt_backward_curve hf hLip c b hX hr.2)
  have hUc : BoundedSmooth (U s) := (hreg s).deriv_bounded
  have hUe : ExponentialBound (U s) := ExponentialBound.of_bounded (A := 1) (hub s)
  have hWe : ExponentialBound (W s) := ExponentialBound.of_bounded (hwb s)
  have hUi := integrable_mul_scaled_of_expBound (hUmeas s) hUe (Real.sqrt (s-a)) x
  have hWi := integrable_scaled_of_expBound (hWmeas s) hWe (Real.sqrt (s-a)) x
  have hU2m : Measurable (fun z => (U s z)^2) := (hUmeas s).pow_const 2
  have hU2e : ExponentialBound (fun z => (U s z)^2) := ExponentialBound.of_bounded (A := 1) (fun z => by
    rw [abs_pow]; norm_num only [NNReal.coe_one]; nlinarith [hub s z,abs_nonneg (U s z)])
  have hU2i := integrable_scaled_of_expBound hU2m hU2e (Real.sqrt (s-a)) x
  have hstein := scaled_gradient_stein hUc (Real.sqrt (s-a)) x
  rw [(hasDerivAt_scaled_space (hUc.smooth.of_le (by simp)) hUe hWe (Real.sqrt (s-a)) x).deriv] at hstein
  have heD : D s = fun y => -(1/2:ℝ)*W s (x+Real.sqrt (s-a)*y)-
      c/2*(U s (x+Real.sqrt (s-a)*y))^2+
      (1/(2*Real.sqrt (s-a)))*(y*U s (x+Real.sqrt (s-a)*y)) := by
    funext y; dsimp only [D]; ring
  have he : (∫ y,D s y ∂gaussianReal 0 1) =
      -(c/2)*varianceHeat (s-a) (fun z => (U s z)^2) x := by
    rw [heD]
    dsimp only
    have hsplit := integral_add ((hWi.const_mul (-(1/2:ℝ))).sub (hU2i.const_mul (c/2))) (hUi.const_mul (1/(2*Real.sqrt (s-a))))
    have hsub := integral_sub (hWi.const_mul (-(1/2:ℝ))) (hU2i.const_mul (c/2))
    simp only [Pi.sub_apply] at hsplit hsub
    rw [hsplit,hsub,integral_const_mul,integral_const_mul,integral_const_mul,← hstein]
    change -(1/2:ℝ)*scaled (Real.sqrt (s-a)) (W s) x-c/2*scaled (Real.sqrt (s-a)) (fun z => (U s z)^2) x+
      (1/(2*Real.sqrt (s-a)))*(Real.sqrt (s-a)*scaled (Real.sqrt (s-a)) (W s) x) = _
    dsimp only [varianceHeat]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr has))]
    ring
  exact hd.2.congr_deriv he

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.BackwardGradientSqJointBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma backward_gradient_sq_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    ∃ L : ℝ≥0, ∀ r ∈ Set.Icc (0:ℝ) b, ∀ s ∈ Set.Icc (0:ℝ) b, ∀ z y,
      |(deriv (backward c b f r) z)^2-(deriv (backward c b f s) y)^2| ≤
        (L:ℝ)*(|r-s|+|z-y|) := by
  obtain ⟨L,hL⟩ := backward_gradient_joint_bound hf hLip hc b
  refine ⟨2*L,fun r hr s hs z y => ?_⟩
  have hu := (backward_verificationData hf hLip hc b).gradient_bound r z
  have hv := (backward_verificationData hf hLip hc b).gradient_bound s y
  have hdiff := hL r hr s hs z y
  rw [sq_sub_sq,abs_mul]
  have hsum : |deriv (backward c b f r) z+deriv (backward c b f s) y| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have hprod := mul_le_mul hdiff hsum (abs_nonneg _) (by positivity : 0 ≤ (L:ℝ)*(|r-s|+|z-y|))
  simp only [NNReal.coe_mul,NNReal.coe_ofNat]
  nlinarith [hprod]

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Control
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

def zeroControl (W : BrownianSystem Ω) (t : ℝ≥0) : Control W t where
  val := fun _ _ => 0
  progressive := isProgressive_const _ _
  bound := by simp

end ZeroTemperatureSK

namespace ZeroTemperatureSK

@[simp] theorem extend_coe (γ : Time → ℝ) (t : Time) : extend γ t = γ t := by
  simp [extend, t.property]

lemma OrderParameter.extend_nonneg (γ : OrderParameter) (t : ℝ) : 0 ≤ extend γ.val t := by
  unfold extend
  split
  · exact γ.nonneg _
  · rfl

lemma OrderParameter.measurable_extend (γ : OrderParameter) : Measurable (extend γ.val) := by
  exact γ.monotone.measurable.dite measurable_const measurableSet_Ico

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Control.measurable {W : BrownianSystem Ω} {t : ℝ≥0} (α : Control W t) :
    Measurable (fun p : ℝ≥0 × Ω => α.val p.1 p.2) := by
  have hclip (n : ℕ) : Measurable (fun p : ℝ≥0 × Ω => α.val (min p.1 n) p.2) := by
    have hs : Measurable[inferInstance, incrementFiltration W t (n : ℝ≥0)]
        (fun p : ℝ≥0 × Ω => p.2) :=
      measurable_snd.mono le_rfl ((incrementFiltration W t).le n)
    exact (α.progressive n).comp
      (((measurable_fst.min measurable_const).subtype_mk
        (h := fun p : ℝ≥0 × Ω => min_le_right p.1 (n : ℝ≥0))).prodMk hs)
  apply measurable_of_tendsto_metrizable hclip
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually
    (eventually_ge_atTop p.1)] with n hn
  simp only [min_eq_left hn]

lemma Control.measurable_elapsed {W : BrownianSystem Ω} {t : ℝ≥0}
    (α : Control W t) (b : ℝ) :
    Measurable (fun p : ℝ × Ω => α.val (Real.toNNReal (p.1 - b)) p.2) := by
  exact α.measurable.comp
    (((measurable_fst.sub measurable_const).real_toNNReal).prodMk measurable_snd)

lemma Control.integrable_weighted_sq {W : BrownianSystem Ω} {t : ℝ≥0}
    (α : Control W t) (γ : OrderParameter) (b : ℝ) (ω : Ω) :
    Integrable (fun s : ℝ => extend γ.val s * (α.val (Real.toNNReal (s - b)) ω)^2) := by
  apply γ.integrable.mul_bdd
    (((α.measurable_elapsed b).comp measurable_prodMk_right).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [Real.norm_eq_abs, abs_pow, one_pow, Function.comp_apply] using
      pow_le_pow_left₀ (abs_nonneg (α.val (Real.toNNReal (s - b)) ω)) (α.bound _ _) 2)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.AbsExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

@[simp] lemma OrderParameter.abs_extend (γ : OrderParameter) (s : ℝ) :
    |extend γ.val s| = extend γ.val s := abs_of_nonneg (γ.extend_nonneg s)

lemma Control.measurable_drift_integral {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Measurable (fun ω => ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω) := by
  simp_rw [intervalIntegral.integral_of_le ht]
  exact ((γ.measurable_extend.comp measurable_fst).mul
    (α.measurable_elapsed t)).stronglyMeasurable.integral_prod_left.measurable

lemma Control.measurable_cost_integral {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Measurable (fun ω => ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2) := by
  simp_rw [intervalIntegral.integral_of_le ht]
  exact ((γ.measurable_extend.comp measurable_fst).mul
    ((α.measurable_elapsed t).pow_const 2)).stronglyMeasurable.integral_prod_left.measurable

lemma Control.drift_integral_bound {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    |∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω| ≤
      ∫ s in t..1, extend γ.val s := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ γ.integrable.intervalIntegrable
  exact Filter.Eventually.of_forall (fun s _ => by
    simp only [Real.norm_eq_abs, abs_mul, γ.abs_extend]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (α.bound _ _) (γ.extend_nonneg s))

lemma Control.cost_integral_bound {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    |∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2| ≤
      ∫ s in t..1, extend γ.val s := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ γ.integrable.intervalIntegrable
  exact Filter.Eventually.of_forall (fun s _ => by
    simp only [Real.norm_eq_abs, abs_mul, γ.abs_extend, abs_pow]
    simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (α.bound _ _) 2) (γ.extend_nonneg s))

lemma controlPayoff_measurable (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Measurable (controlPayoff W γ t x α) := by
  exact (((measurable_const.add (W.measurable 1)).sub
    (W.measurable (Real.toNNReal t))).add
    (α.measurable_drift_integral γ t ht)).abs.sub
    ((α.measurable_cost_integral γ t ht).const_mul _)

lemma controlPayoff_abs_bound (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    |controlPayoff W γ t x α ω| ≤ |x + W.B 1 ω - W.B (Real.toNNReal t) ω| +
      (3 / 2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  have hd := α.drift_integral_bound γ t ht ω
  have hc := α.cost_integral_bound γ t ht ω
  have htri := abs_add_le (x + W.B 1 ω - W.B (Real.toNNReal t) ω)
    (∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω)
  have hall := abs_sub
    |x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω|
    ((1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2)
  simp only [abs_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hall
  dsimp [controlPayoff]
  linarith

lemma controlPayoff_integrable (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Integrable (controlPayoff W γ t x α) W.law := by
  let := W.isProbability
  have h := (((integrable_const x).add (W.brownian.integrable_eval 1)).sub
    (W.brownian.integrable_eval (Real.toNNReal t))).abs.add
    (integrable_const ((3 / 2 : ℝ) * ∫ s in t..1, extend γ.val s))
  exact h.mono' (controlPayoff_measurable W γ t x ht α).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => controlPayoff_abs_bound W γ t x ht α ω))

lemma controlPayoff_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    controlPayoff W γ t x α ω ≤ |x + W.B 1 ω - W.B (Real.toNNReal t) ω| +
      (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  have habs : Integrable (fun s : ℝ => extend γ.val s * |α.val (Real.toNNReal (s - t)) ω|) := by
    exact γ.integrable.mul_bdd
      (((α.measurable_elapsed t).comp measurable_prodMk_right).abs.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun s => by
        simpa only [Real.norm_eq_abs, Function.comp_apply, abs_abs] using α.bound _ _))
  have hnorm : |∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω| ≤
      ∫ s in t..1, extend γ.val s * |α.val (Real.toNNReal (s - t)) ω| := by
    simpa only [Real.norm_eq_abs, abs_mul, γ.abs_extend] using
      (intervalIntegral.norm_integral_le_integral_norm (f := fun s =>
        extend γ.val s * α.val (Real.toNNReal (s - t)) ω) ht)
  have hcomp := intervalIntegral.integral_mono_on ht
    (habs.sub ((α.integrable_weighted_sq γ t ω).const_mul (1 / 2 : ℝ))).intervalIntegrable
    (γ.integrable.const_mul (1 / 2 : ℝ)).intervalIntegrable
    (fun s (_ : s ∈ Set.Icc t 1) => show
      extend γ.val s * |α.val (Real.toNNReal (s - t)) ω| -
          (1 / 2 : ℝ) * (extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2) ≤
        (1 / 2 : ℝ) * extend γ.val s from by
      have he : |α.val (Real.toNNReal (s - t)) ω| -
          (1 / 2 : ℝ) * (α.val (Real.toNNReal (s - t)) ω)^2 ≤ 1 / 2 := by
        nlinarith [sq_nonneg (|α.val (Real.toNNReal (s - t)) ω| - 1),
          sq_abs (α.val (Real.toNNReal (s - t)) ω)]
      nlinarith [mul_le_mul_of_nonneg_left he (γ.extend_nonneg s)])
  simp only [Pi.sub_apply] at hcomp
  rw [intervalIntegral.integral_sub habs.intervalIntegrable
    ((α.integrable_weighted_sq γ t ω).const_mul (1 / 2 : ℝ)).intervalIntegrable,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hcomp
  have htri := abs_add_le (x + W.B 1 ω - W.B (Real.toNNReal t) ω)
    (∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω)
  dsimp [controlPayoff]
  linarith

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.ExpectedControlPayoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

lemma expected_controlPayoff_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤
      (∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) +
      (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  let := W.isProbability
  have hnoise : Integrable (fun ω => |x + W.B 1 ω - W.B (Real.toNNReal t) ω|) W.law :=
    (((integrable_const x).add (W.brownian.integrable_eval 1)).sub
      (W.brownian.integrable_eval (Real.toNNReal t))).abs
  calc
    _ ≤ ∫ ω, (|x + W.B 1 ω - W.B (Real.toNNReal t) ω| +
        (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s) ∂W.law :=
      integral_mono (controlPayoff_integrable W γ t x ht α)
        (hnoise.add (integrable_const _)) (controlPayoff_le W γ t x ht α)
    _ = _ := by rw [integral_add hnoise (integrable_const _)]; simp

lemma control_values_bddAbove (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) :
    BddAbove (Set.range (fun α : Control W (Real.toNNReal t) =>
      ∫ ω, controlPayoff W γ t x α ω ∂W.law)) := by
  refine ⟨(∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) +
      (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s, ?_⟩
  rintro _ ⟨α, rfl⟩
  exact expected_controlPayoff_le W γ t x ht α

lemma expected_controlPayoff_le_value (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤ value W γ t x := by
  exact le_csSup (control_values_bddAbove W γ t x ht) ⟨α, rfl⟩

lemma controlPayoff_space_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x y : ℝ) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    controlPayoff W γ t x α ω ≤ controlPayoff W γ t y α ω + |x - y| := by
  have h := abs_add_le
    (y + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω) (x-y)
  have heq : y + W.B 1 ω - W.B (Real.toNNReal t) ω +
      (∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω) + (x-y) =
      x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω := by ring
  rw [heq] at h
  dsimp [controlPayoff]
  linarith

lemma value_space_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x y : ℝ) (ht : t ≤ 1) : value W γ t x ≤ value W γ t y + |x - y| := by
  let := W.isProbability
  unfold value
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨zeroControl W (Real.toNNReal t), rfl⟩⟩
  rintro _ ⟨α, rfl⟩
  calc
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤
        ∫ ω, (controlPayoff W γ t y α ω + |x-y|) ∂W.law :=
      integral_mono (controlPayoff_integrable W γ t x ht α)
        ((controlPayoff_integrable W γ t y ht α).add (integrable_const _))
        (controlPayoff_space_le W γ t x y α)
    _ = (∫ ω, controlPayoff W γ t y α ω ∂W.law) + |x-y| := by
      rw [integral_add (controlPayoff_integrable W γ t y ht α) (integrable_const _)]
      simp
    _ ≤ value W γ t y + |x-y| :=
      add_le_add (expected_controlPayoff_le_value W γ t y ht α) le_rfl

theorem value_lipschitz (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) : LipschitzWith 1 (value W γ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [abs_le]
  constructor
  · have h := value_space_le W γ t y x ht
    rw [abs_sub_comm y x] at h
    linarith
  · have h := value_space_le W γ t x y ht
    linarith

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.ProgressiveIntegralMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma progressive_integral_measurable (ℱ : Filtration ℝ≥0 mΩ)
    {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive ℱ α) (s : ℝ≥0) {w : ℝ → ℝ}
    (hw : Measurable w) :
    Measurable[ℱ s] (fun ω => ∫ r in (0:ℝ)..(s:ℝ), w r*α (Real.toNNReal r) ω) := by
  let clip (p : ℝ × Ω) := α (min (Real.toNNReal p.1) s) p.2
  have htime : Measurable[(borel ℝ).prod (ℱ s)]
      (fun p : ℝ × Ω => min (Real.toNNReal p.1) s) :=
    (measurable_fst.real_toNNReal).min measurable_const
  have hclip : Measurable[(borel ℝ).prod (ℱ s)] clip := by
    exact (hα s).comp ((htime.subtype_mk (h := fun p : ℝ × Ω => (min_le_right (Real.toNNReal p.1) s))).prodMk measurable_snd)
  have hwm : Measurable[(borel ℝ).prod (ℱ s)] (fun p : ℝ × Ω => w p.1*clip p) :=
    (hw.comp measurable_fst).mul hclip
  have hint : Measurable[ℱ s]
      (fun ω => ∫ r in (0:ℝ)..(s:ℝ), w r*clip (r,ω)) := by
    let : MeasurableSpace Ω := ℱ s
    simp_rw [intervalIntegral.integral_of_le s.coe_nonneg]
    exact hwm.stronglyMeasurable.integral_prod_left.measurable
  convert hint using 1 <;> try rfl
  funext ω
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le s.coe_nonneg] at hr
  have hle : Real.toNNReal r ≤ s := by
    exact Real.toNNReal_le_iff_le_coe.mpr hr.2
  simp only [clip, min_eq_left hle]

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.IntegratedCompletionSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

lemma integrated_completion_square (a b c u : ℝ) (hab : a ≤ b) (hc : 0 ≤ c)
    {α : ℝ → ℝ} (hα : IntervalIntegrable α volume a b)
    (hα₂ : IntervalIntegrable (fun t => (α t)^2) volume a b) :
    u * (∫ t in a..b, c*α t) - (1/2:ℝ)*(∫ t in a..b, c*(α t)^2) ≤
      (b-a)*c/2*u^2 := by
  have hmono : (∫ t in a..b, u*(c*α t)-(1/2:ℝ)*(c*(α t)^2)) ≤
      ∫ _t in a..b, c/2*u^2 := by
    apply intervalIntegral.integral_mono_on hab
      ((hα.const_mul c).const_mul u |>.sub ((hα₂.const_mul c).const_mul (1/2:ℝ)))
      intervalIntegrable_const
    intro t ht
    nlinarith [mul_nonneg hc (sq_nonneg (α t-u))]
  rw [intervalIntegral.integral_sub ((hα.const_mul c).const_mul u)
    ((hα₂.const_mul c).const_mul (1/2:ℝ)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simpa only [intervalIntegral.integral_const_mul, smul_eq_mul, mul_div_assoc, mul_assoc] using hmono

lemma vanishing_mesh_error (T A C : ℝ) :
    Tendsto (fun n : ℕ =>
      (n:ℝ) * (A*(T/(n:ℝ))*Real.sqrt (T/(n:ℝ)) + C*(T/(n:ℝ))^2)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => T/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hlim : Tendsto (fun n : ℕ => A*T*Real.sqrt (T/(n:ℝ)) + C*T*(T/(n:ℝ)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0 |>.comp hh)).add
      (tendsto_const_nhds.mul hh))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1) hn))
  field_simp

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.StepDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def stepDrift (α : ℝ → Ω → ℝ) (s h c : ℝ) (ω : Ω) : ℝ :=
  ∫ r in s..s+h, c*α r ω

def stepCost (α : ℝ → Ω → ℝ) (s h c : ℝ) (ω : Ω) : ℝ :=
  (1/2:ℝ)*∫ r in s..s+h, c*(α r ω)^2

lemma bounded_control_intervalIntegrable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h : ℝ) (hh : 0 ≤ h) (ω : Ω) :
    IntervalIntegrable (fun r => α r ω) volume s (s+h) ∧
    IntervalIntegrable (fun r => (α r ω)^2) volume s (s+h) := by
  have hm₁ : Measurable (fun r => α r ω) := hm.comp measurable_prodMk_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : s ≤ s+h),
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : s ≤ s+h)]
  constructor
  · exact Integrable.of_bound hm₁.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using hb r ω))
  · apply Integrable.of_bound (hm₁.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with r
    rw [Real.norm_eq_abs, abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg (α r ω)) (hb r ω) 2

lemma stepDrift_measurable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (s h c : ℝ) (hh : 0 ≤ h) :
    Measurable (stepDrift α s h c) := by
  unfold stepDrift
  simp_rw [intervalIntegral.integral_of_le (by linarith : s ≤ s+h)]
  exact (hm.const_mul c).stronglyMeasurable.integral_prod_left.measurable

lemma stepCost_measurable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (s h c : ℝ) (hh : 0 ≤ h) :
    Measurable (stepCost α s h c) := by
  unfold stepCost
  simp_rw [intervalIntegral.integral_of_le (by linarith : s ≤ s+h)]
  exact (((hm.pow_const 2).const_mul c).stronglyMeasurable.integral_prod_left.measurable).const_mul _

omit [MeasurableSpace Ω] in
lemma stepDrift_bound {α : ℝ → Ω → ℝ}
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) (ω : Ω) :
    |stepDrift α s h c ω| ≤ c*h := by
  unfold stepDrift
  rw [← Real.norm_eq_abs]
  have hbound : ‖∫ r in s..s+h, c*α r ω‖ ≤ ∫ _r in s..s+h, c := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      _ intervalIntegrable_const
    filter_upwards [] with r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    nlinarith [hb r ω]
  simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_comm] using hbound

omit [MeasurableSpace Ω] in
lemma stepCost_bound {α : ℝ → Ω → ℝ}
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) (ω : Ω) :
    |stepCost α s h c ω| ≤ c*h/2 := by
  unfold stepCost
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have hbound : |∫ r in s..s+h, c*(α r ω)^2| ≤ c*h := by
    apply stepDrift_bound (α := fun r ω => (α r ω)^2) _ s h c hh hc ω
    intro r ω
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg (α r ω)) (hb r ω) 2
  linarith

lemma stepDrift_integrable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) :
    Integrable (stepDrift α s h c) P := by
  exact Integrable.of_bound (stepDrift_measurable hm s h c hh).aestronglyMeasurable (c*h)
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using (stepDrift_bound hb s h c hh hc ω)))

lemma stepCost_integrable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) :
    Integrable (stepCost α s h c) P := by
  exact Integrable.of_bound (stepCost_measurable hm s h c hh).aestronglyMeasurable (c*h/2)
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using (stepCost_bound hb s h c hh hc ω)))

lemma step_completion_square {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (u : ℝ) (ω : Ω) :
    u*stepDrift α s h c ω-stepCost α s h c ω ≤ h*c/2*u^2 := by
  obtain ⟨hα,hα₂⟩ := bounded_control_intervalIntegrable hm hb s h hh ω
  simpa only [stepDrift, stepCost, add_sub_cancel_left] using
    integrated_completion_square s (s+h) c u (by linarith) hc hα hα₂

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.AdaptedIndepIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

lemma adapted_indep_increment (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y) :
    IndepFun Y (fun ω => B (s+h) ω - B s ω) P := by
  have hi := (hB.indepFun_shift s).comp (measurable_pi_apply h) measurable_id
  change IndepFun (fun ω => B (s+h) ω - B s ω)
    (fun ω (t : Set.Iic s) => B t ω) P at hi
  apply Indep.symm
  apply indep_of_indep_of_le hi le_rfl
  rw [← Filtration.natural_eq_comap B (fun t => (hm t).stronglyMeasurable) s]
  exact measurable_iff_comap_le.mp hY

lemma integral_adapted_mul_increment (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y) :
    (∫ ω, Y ω * (B (s+h) ω - B s ω) ∂P) = 0 := by
  have hYm : Measurable Y := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  rw [(adapted_indep_increment hB hm s h hY).integral_fun_mul_eq_mul_integral
    hYm.aestronglyMeasurable ((hm (s+h)).sub (hm s)).aestronglyMeasurable]
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
    hB.integral_eval]
  simp

lemma gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable] at h
  simpa using h

lemma integral_adapted_mul_increment_sq (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y) :
    (∫ ω, Y ω * (B (s+h) ω - B s ω)^2 ∂P) = (h : ℝ) * ∫ ω, Y ω ∂P := by
  have hYm : Measurable Y := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hi := (adapted_indep_increment hB hm s h hY).comp measurable_id
    (measurable_id.pow_const 2)
  change IndepFun Y (fun ω => (B (s+h) ω - B s ω)^2) P at hi
  rw [hi.integral_fun_mul_eq_mul_integral hYm.aestronglyMeasurable
    (((hm (s+h)).sub (hm s)).pow_const 2).aestronglyMeasurable]
  have he := (hB.hasLaw_sub (s+h) s).integral_comp
    (f := fun x : ℝ => x^2) ((measurable_id.pow_const 2).aestronglyMeasurable)
  change (∫ ω, (B (s+h) ω - B s ω)^2 ∂P) = _ at he
  rw [he, gaussian_second_moment]
  rw [coe_nndist, Real.dist_eq]
  change (∫ ω, Y ω ∂P) * |((s+h : ℝ≥0) : ℝ) - (s : ℝ)| = _
  rw [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg]
  ring

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

lemma taylor2_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ}
    (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x d : ℝ) :
    |f (x+d) - f x - deriv f x*d - (1/2:ℝ)*deriv (deriv f) x*d^2| ≤
      C / 6 * |d|^3 := by
  by_cases hd : d = 0
  · simp [hd]
  have hxd : x ≠ x+d := by intro h; apply hd; linarith
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxd hf.contDiffOn
  have hu := uniqueDiffOn_uIcc hxd
  have hx : x ∈ Set.uIcc x (x+d) := left_mem_uIcc
  have h1 : iteratedDerivWithin 1 f (Set.uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hx,
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (Set.uIcc x (x+d)) x = deriv (deriv f) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hx,
      iteratedDeriv_succ, iteratedDeriv_one]
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, h1, h2] at he
  norm_num at he
  have he' : f (x+d) - f x - deriv f x*d - (1/2:ℝ)*deriv (deriv f) x*d^2 =
      iteratedDeriv 3 f y * d^3 / 6 := by
    calc
      _ = f (x+d) - (f x + d * deriv f x + (1/2:ℝ)*d^2*deriv (deriv f) x) := by ring
      _ = _ := by convert he using 1
  rw [he', abs_div, abs_mul, abs_pow]
  norm_num
  have := mul_le_mul_of_nonneg_right (hC y) (pow_nonneg (abs_nonneg d) 3)
  nlinarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.IntegrableCompBoundedDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integrable_comp_of_bounded_deriv [IsFiniteMeasure P] {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (C : ℝ≥0) (hC : ∀ x, |deriv f x| ≤ C) {Y : Ω → ℝ} (hY : Integrable Y P) :
    Integrable (fun ω => f (Y ω)) P := by
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_deriv_le hf
    (fun x => show ‖deriv f x‖₊ ≤ C from by exact_mod_cast hC x)
  apply ((integrable_const ‖f 0‖).add (hY.norm.const_mul (C:ℝ))).mono'
    (hf.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable)
  filter_upwards [] with ω
  have h := hl.norm_sub_le (Y ω) 0
  simp only [sub_zero] at h
  have htri := norm_add_le (f (Y ω)-f 0) (f 0)
  rw [sub_add_cancel] at htri
  dsimp
  simp only [Real.norm_eq_abs] at h htri
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.NormalThirdMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace ZeroTemperatureSK.WeakIto

def normalThirdMoment : ℝ := ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1

lemma normalThirdMoment_nonneg : 0 ≤ normalThirdMoment :=
  integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 3)

lemma gaussian_abs_pow (p : ℕ) (v : ℝ≥0) :
    (∫ x : ℝ, |x|^p ∂gaussianReal 0 v) =
      (Real.sqrt (v : ℝ))^p * ∫ x : ℝ, |x|^p ∂gaussianReal 0 1 := by
  have hs : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v:ℝ)*x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hs, integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma increment_abs_cube (hB : IsPreBrownianReal B P) (s h : ℝ≥0) :
    (∫ ω, |B (s+h) ω - B s ω|^3 ∂P) = (h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment := by
  have he := (hB.hasLaw_sub (s+h) s).integral_comp
    (f := fun x : ℝ => |x|^3) ((continuous_abs.pow 3).measurable.aestronglyMeasurable)
  change (∫ ω, |B (s+h) ω - B s ω|^3 ∂P) = _ at he
  rw [he, gaussian_abs_pow]
  have hd : nndist ((s+h : ℝ≥0):ℝ) (s:ℝ) = h := by
    ext
    rw [coe_nndist, Real.dist_eq]
    rw [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg]
  change Real.sqrt ((nndist ((s+h : ℝ≥0):ℝ) (s:ℝ) : ℝ≥0):ℝ)^3 *
    normalThirdMoment = _
  rw [hd]
  rw [pow_succ, Real.sq_sqrt h.coe_nonneg]

end ZeroTemperatureSK.WeakIto

end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.ExpectedBrownianStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_brownian_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C₁ C₂ C₃ : ℝ≥0) (hC₁ : ∀ x, |deriv f x| ≤ C₁)
    (hC₂ : ∀ x, |deriv (deriv f) x| ≤ C₂)
    (hC₃ : ∀ x, |iteratedDeriv 3 f x| ≤ C₃) :
    |(∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, f (Y ω) ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P)| ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hd : Integrable (fun ω => B (s+h) ω - B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have m2 := hB.isGaussianProcess.hasGaussianLaw_sub (s := s+h) (t := s) |>.memLp_two
  have hd2 : Integrable (fun ω => (B (s+h) ω - B s ω)^2) P := by
    simpa only [Pi.sub_apply] using m2.integrable_sq
  have hd3 : Integrable (fun ω => |B (s+h) ω - B s ω|^3) P := by
    have hh := hB.isGaussianProcess.hasGaussianLaw_sub (s := s+h) (t := s) |>.memLp
      (p := (3 : ℝ≥0∞)) (by norm_num)
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hh.integrable_norm_pow (by norm_num : 3 ≠ 0)
  have hf₁ : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hf₂ : ContDiff ℝ 1 (deriv (deriv f)) := hf₁.deriv'
  have hm₁ : AEStronglyMeasurable (fun ω => deriv f (Y ω)) P :=
    (hf₁.continuous.measurable.comp hYm).aestronglyMeasurable
  have hm₂ : AEStronglyMeasurable (fun ω => deriv (deriv f) (Y ω)) P :=
    (hf₂.continuous.measurable.comp hYm).aestronglyMeasurable
  have hi₀ := integrable_comp_of_bounded_deriv (hf.differentiable (by norm_num)) C₁ hC₁ hYi
  have hi₁ : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω))) P := by
    simpa only [Pi.add_apply] using integrable_comp_of_bounded_deriv
      (hf.differentiable (by norm_num)) C₁ hC₁ (hYi.add hd)
  have hiL := hd.bdd_mul hm₁ (Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using hC₁ (Y ω)))
  have hiQ := hd2.bdd_mul hm₂ (Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using hC₂ (Y ω)))
  have hLin := integral_adapted_mul_increment hB hm s h (hf₁.continuous.measurable.comp hY)
  have hQuad := integral_adapted_mul_increment_sq hB hm s h (hf₂.continuous.measurable.comp hY)
  simp only [Function.comp_apply] at hLin hQuad
  have hiD : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω)) - f (Y ω)) P := hi₁.sub hi₀
  have hiDL : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω)) - f (Y ω) -
      deriv f (Y ω) * (B (s+h) ω - B s ω)) P := hiD.sub hiL
  let R (ω : Ω) := f (Y ω + (B (s+h) ω - B s ω)) - f (Y ω) -
    deriv f (Y ω) * (B (s+h) ω - B s ω) -
    (1/2:ℝ) * (deriv (deriv f) (Y ω) * (B (s+h) ω - B s ω)^2)
  have hiR : Integrable R P := ((hi₁.sub hi₀).sub hiL).sub (hiQ.const_mul (1/2:ℝ))
  have hR : (∫ ω, R ω ∂P) = (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, f (Y ω) ∂P) - (h:ℝ)/2 * ∫ ω, deriv (deriv f) (Y ω) ∂P := by
    dsimp only [R]
    rw [integral_sub hiDL (hiQ.const_mul (1/2:ℝ)),
      integral_sub hiD hiL, integral_sub hi₁ hi₀, integral_const_mul,
      hLin, hQuad]
    ring
  rw [← hR]
  calc
    _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (C₃:ℝ)/6 * |B (s+h) ω - B s ω|^3 ∂P := by
      apply integral_mono hiR.abs (hd3.const_mul _)
      intro ω
      dsimp only [R]
      simpa only [mul_assoc] using taylor2_bound hf hC₃ (Y ω) (B (s+h) ω - B s ω)
    _ = _ := by rw [integral_const_mul, increment_abs_cube hB s h]

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

lemma drift_perturbation_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |deriv (deriv f) x| ≤ C) (x d a : ℝ) :
    |f (x+d+a) - f (x+d) - deriv f x*a| ≤ (C:ℝ)*(|d|+|a|)*|a| := by
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hl : LipschitzWith C (deriv f) := lipschitzWith_of_nnnorm_deriv_le
    (hfd.differentiable (by norm_num))
    (fun z => show ‖deriv (deriv f) z‖₊ ≤ C from by exact_mod_cast hC z)
  let g : ℝ → ℝ := fun z => f z - deriv f x*z
  have hgd (z : ℝ) : HasDerivAt g (deriv f z-deriv f x) z := by
    have h1 : HasDerivAt f (deriv f z) z := (hf.differentiable (by norm_num) z).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => deriv f x*t) (deriv f x) z := by
      simpa using (hasDerivAt_id z).const_mul (deriv f x)
    exact h1.sub h2
  have hb (z : ℝ) (hz : z ∈ Set.uIcc (x+d) (x+d+a)) :
      ‖deriv f z - deriv f x‖ ≤ (C:ℝ)*(|d|+|a|) := by
    have hh := abs_sub_left_of_mem_uIcc hz
    rw [add_sub_cancel_left] at hh
    have hh' : |z-x| ≤ |d|+|a| := by
      have := abs_add_le (z-(x+d)) d
      have he : z-(x+d)+d = z-x := by ring
      rw [he] at this
      linarith
    have hg := hl.norm_sub_le z x
    simp only [Real.norm_eq_abs] at hg ⊢
    exact hg.trans (mul_le_mul_of_nonneg_left hh' C.coe_nonneg)
  have hmv := (convex_uIcc (x+d) (x+d+a)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hgd z).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
  simp only [g, Real.norm_eq_abs, add_sub_cancel_left] at hmv
  convert hmv using 1 <;> try rfl
  congr 1
  ring

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.NormalFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

def normalFirstMoment : ℝ := ∫ x : ℝ, |x| ∂gaussianReal 0 1

lemma normalFirstMoment_nonneg : 0 ≤ normalFirstMoment := integral_nonneg abs_nonneg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma increment_abs_first (hB : IsPreBrownianReal B P) (s h : ℝ≥0) :
    (∫ ω, |B (s+h) ω - B s ω| ∂P) = Real.sqrt (h:ℝ)*normalFirstMoment := by
  have he := (hB.hasLaw_sub (s+h) s).integral_comp
    (f := abs) continuous_abs.measurable.aestronglyMeasurable
  change (∫ ω, |B (s+h) ω - B s ω| ∂P) = _ at he
  rw [he]
  have hh := gaussian_abs_pow 1 (nndist ((s+h:ℝ≥0):ℝ) (s:ℝ))
  simp only [pow_one] at hh
  change (∫ x : ℝ, |x| ∂gaussianReal 0 (nndist ((s+h:ℝ≥0):ℝ) (s:ℝ))) = _
  rw [hh]
  change Real.sqrt ((nndist ((s+h:ℝ≥0):ℝ) (s:ℝ):ℝ≥0):ℝ) * normalFirstMoment = _
  rw [coe_nndist, Real.dist_eq]
  rw [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg]

lemma expected_control_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y A : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) (hA : Measurable A) (M : ℝ≥0)
    (hAb : ∀ ω, |A ω| ≤ (M:ℝ)*(h:ℝ)) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C₁ C₂ C₃ : ℝ≥0) (hC₁ : ∀ x, |deriv f x| ≤ C₁)
    (hC₂ : ∀ x, |deriv (deriv f) x| ≤ C₂)
    (hC₃ : ∀ x, |iteratedDeriv 3 f x| ≤ C₃) :
    |(∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω) ∂P) - (∫ ω, deriv f (Y ω) * A ω ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P)| ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) +
      (C₂:ℝ)*(M:ℝ)*(h:ℝ) * (Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hd : Integrable (fun ω => B (s+h) ω - B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have hAi : Integrable A P := Integrable.of_bound hA.aestronglyMeasurable ((M:ℝ)*(h:ℝ))
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hAb ω))
  have hf₁ : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hiF : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω))) P := by
    simpa only [Pi.add_apply] using integrable_comp_of_bounded_deriv
      (hf.differentiable (by norm_num)) C₁ hC₁ (hYi.add hd)
  have hiFA : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω) + A ω)) P := by
    simpa only [Pi.add_apply] using integrable_comp_of_bounded_deriv
      (hf.differentiable (by norm_num)) C₁ hC₁ ((hYi.add hd).add hAi)
  have hiL : Integrable (fun ω => deriv f (Y ω)*A ω) P := hAi.bdd_mul
    (hf₁.continuous.measurable.comp hYm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC₁ (Y ω)))
  let R (ω : Ω) := f (Y ω + (B (s+h) ω - B s ω) + A ω) -
    f (Y ω + (B (s+h) ω - B s ω)) - deriv f (Y ω)*A ω
  have hiD : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω) + A ω) -
    f (Y ω + (B (s+h) ω - B s ω))) P := hiFA.sub hiF
  have hiR : Integrable R P := hiD.sub hiL
  have hR : (∫ ω, R ω ∂P) =
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, deriv f (Y ω)*A ω ∂P) := by
    dsimp only [R]
    rw [integral_sub hiD hiL, integral_sub hiFA hiF]
  have hRb : |∫ ω, R ω ∂P| ≤ (C₂:ℝ)*(M:ℝ)*(h:ℝ) *
      (Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C₂:ℝ)*(M:ℝ)*(h:ℝ) * (|B (s+h) ω - B s ω| + (M:ℝ)*(h:ℝ)) ∂P := by
        apply integral_mono hiR.abs ((hd.abs.add (integrable_const _)).const_mul _)
        intro ω
        have hb := drift_perturbation_bound (hf.of_le (by norm_num)) C₂ hC₂
          (Y ω) (B (s+h) ω - B s ω) (A ω)
        change |R ω| ≤ _
        apply hb.trans
        have h₁ := mul_le_mul_of_nonneg_left (add_le_add_left (hAb ω)
          |B (s+h) ω - B s ω|) C₂.coe_nonneg
        have h₂ := mul_le_mul h₁ (hAb ω) (abs_nonneg (A ω))
          (mul_nonneg C₂.coe_nonneg (by positivity))
        convert h₂ using 1 <;> (try dsimp only [Pi.add_apply]) <;> ring
      _ = _ := by
        rw [integral_const_mul, integral_add hd.abs (integrable_const _),
          increment_abs_first hB s h]
        simp
  rw [hR] at hRb
  have hG := expected_brownian_step hB hm s h hY hYi hf C₁ C₂ C₃ hC₁ hC₂ hC₃
  have htri := abs_add_le
    ((∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) - (∫ ω, f (Y ω) ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P))
    ((∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, deriv f (Y ω)*A ω ∂P))
  calc
    _ = |((∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) - (∫ ω, f (Y ω) ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P)) +
    ((∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, deriv f (Y ω)*A ω ∂P))| := by congr 1; ring
    _ ≤ _ := htri.trans (add_le_add hG hRb)

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.TimeStepBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

lemma time_step_bound {F D : ℝ → ℝ → ℝ} (s h x z : ℝ) (hh : 0 ≤ h)
    (L : ℝ≥0)
    (hD : ∀ r ∈ Set.Icc s (s+h),
      HasDerivWithinAt (fun t => F t z) (D r z) (Set.Icc s (s+h)) r)
    (hL : ∀ r ∈ Set.Icc s (s+h), |D r z-D s x| ≤ (L:ℝ)*(|r-s|+|z-x|)) :
    |F (s+h) z-F s z-h*D s x| ≤ (L:ℝ)*h*(h+|z-x|) := by
  let g : ℝ → ℝ := fun t => F t z-t*D s x
  have hd (r : ℝ) (hr : r ∈ Set.Icc s (s+h)) :
      HasDerivWithinAt g (D r z-D s x) (Set.Icc s (s+h)) r := by
    have h2 : HasDerivWithinAt (fun t : ℝ => t*D s x) (D s x) (Set.Icc s (s+h)) r := by
      simpa using ((hasDerivAt_id r).mul_const (D s x)).hasDerivWithinAt
    exact (hD r hr).sub h2
  have hb (r : ℝ) (hr : r ∈ Set.Icc s (s+h)) :
      ‖D r z-D s x‖ ≤ (L:ℝ)*(h+|z-x|) := by
    rw [Real.norm_eq_abs]
    apply (hL r hr).trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
    linarith [hr.2]
  have hm := (convex_Icc s (s+h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => hd r hr) hb
    (show s ∈ Set.Icc s (s+h) by constructor <;> linarith)
    (show s+h ∈ Set.Icc s (s+h) by constructor <;> linarith)
  simp only [g, Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh] at hm
  convert hm using 1 <;> try rfl
  · congr 1; ring
  · ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_time_space_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y A : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) (hA : Measurable A) (M : ℝ≥0)
    (hAb : ∀ ω, |A ω| ≤ (M:ℝ)*(h:ℝ)) {F D : ℝ → ℝ → ℝ}
    (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₁ C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t x, |deriv (F t) x| ≤ C₁)
    (hC₂ : ∀ t x, |deriv (deriv (F t)) x| ≤ C₂)
    (hC₃ : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C₃)
    (hDm : Measurable (D s)) (hCt : ∀ x, |D s x| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z)
        (Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ))) r)
    (hL : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z x,
      |D r z-D s x| ≤ (L:ℝ)*(|r-(s:ℝ)|+|z-x|)) :
    |(∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω + (B (s+h) ω-B s ω) + A ω) ∂P) -
      (∫ ω, F s (Y ω) ∂P) - (∫ ω, deriv (F s) (Y ω)*A ω ∂P) -
      (h:ℝ) * ((∫ ω, D s (Y ω) ∂P) +
        (1/2:ℝ) * (∫ ω, deriv (deriv (F s)) (Y ω) ∂P))| ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) +
      (C₂:ℝ)*(M:ℝ)*(h:ℝ) * (Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) +
      (L:ℝ)*(h:ℝ) * ((h:ℝ) + Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hd : Integrable (fun ω => B (s+h) ω - B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have hAi : Integrable A P := Integrable.of_bound hA.aestronglyMeasurable ((M:ℝ)*(h:ℝ))
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hAb ω))
  let Z (ω : Ω) := Y ω + (B (s+h) ω-B s ω) + A ω
  have hZi : Integrable Z P := (hYi.add hd).add hAi
  have hiF (t : ℝ) : Integrable (fun ω => F t (Z ω)) P :=
    integrable_comp_of_bounded_deriv ((hf t).differentiable (by norm_num)) C₁ (hC₁ t) hZi
  have hiD : Integrable (fun ω => D s (Y ω)) P := Integrable.of_bound
    (hDm.comp hYm).aestronglyMeasurable Ct
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hCt (Y ω)))
  let R (ω : Ω) := F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω)-(h:ℝ)*D s (Y ω)
  have hiR : Integrable R P := ((hiF _).sub (hiF _)).sub (hiD.const_mul _)
  have hiDb : Integrable (fun ω => (h:ℝ)+|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) P :=
    ((integrable_const _).add hd.abs).add (integrable_const _)
  have hRb : |∫ ω, R ω ∂P| ≤
      (L:ℝ)*(h:ℝ) * ((h:ℝ) + Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (L:ℝ)*(h:ℝ) * ((h:ℝ)+|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) ∂P := by
        apply integral_mono hiR.abs (hiDb.const_mul _)
        intro ω
        have he := time_step_bound (s:ℝ) (h:ℝ) (Y ω) (Z ω) h.coe_nonneg L
          (fun r hr => hD r hr (Z ω)) (fun r hr => hL r hr (Z ω) (Y ω))
        apply he.trans
        have hz : |Z ω-Y ω| ≤ |B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ) := by
          have hz : Z ω-Y ω = (B (s+h) ω-B s ω)+A ω := by dsimp only [Z]; ring
          rw [hz]
          have habs := abs_add_le (B (s+h) ω-B s ω) (A ω)
          linarith [hAb ω]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg L.coe_nonneg h.coe_nonneg)
        linarith
      _ = _ := by
        have hiDa : Integrable (fun ω => (h:ℝ)+|B (s+h) ω-B s ω|) P :=
          (integrable_const _).add hd.abs
        rw [integral_const_mul, integral_add hiDa (integrable_const _),
          integral_add (integrable_const _) hd.abs, increment_abs_first hB s h]
        simp
  have hR : (∫ ω, R ω ∂P) = (∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P) -
      (∫ ω, F s (Z ω) ∂P) - (h:ℝ)*(∫ ω, D s (Y ω) ∂P) := by
    have hiFd : Integrable (fun ω => F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω)) P :=
      (hiF _).sub (hiF _)
    dsimp only [R]
    rw [integral_sub hiFd (hiD.const_mul _), integral_sub (hiF _) (hiF _),
      integral_const_mul]
  have hG := expected_control_step hB hm s h hY hYi hA M hAb (hf s)
    C₁ C₂ C₃ (hC₁ s) (hC₂ s) (hC₃ s)
  rw [hR] at hRb
  have htri := abs_add_le
    ((∫ ω, F s (Z ω) ∂P) - (∫ ω, F s (Y ω) ∂P) -
      (∫ ω, deriv (F s) (Y ω)*A ω ∂P) -
      (h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P))
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P) - (∫ ω, F s (Z ω) ∂P) -
      (h:ℝ)*(∫ ω, D s (Y ω) ∂P))
  calc
    _ = |((∫ ω, F s (Z ω) ∂P) - (∫ ω, F s (Y ω) ∂P) -
      (∫ ω, deriv (F s) (Y ω)*A ω ∂P) -
      (h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)) +
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P) - (∫ ω, F s (Z ω) ∂P) -
      (h:ℝ)*(∫ ω, D s (Y ω) ∂P))| := by congr 1; dsimp only [Z]; ring
    _ ≤ _ := htri.trans (add_le_add hG hRb)

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.ExpectedVerificationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_verification_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h c : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) {α : ℝ → Ω → ℝ}
    (hαm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hαb : ∀ r ω, |α r ω| ≤ 1)
    {F D : ℝ → ℝ → ℝ} (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₁ C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t x, |deriv (F t) x| ≤ C₁)
    (hC₂ : ∀ t x, |deriv (deriv (F t)) x| ≤ C₂)
    (hC₃ : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C₃)
    (hDm : Measurable (D s)) (hCt : ∀ x, |D s x| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z)
        (Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ))) r)
    (hL : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z x,
      |D r z-D s x| ≤ (L:ℝ)*(|r-(s:ℝ)|+|z-x|))
    (hPDE : ∀ x, D s x + (1/2:ℝ)*deriv (deriv (F s)) x +
      (c:ℝ)/2*(deriv (F s) x)^2 = 0) :
    (∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω+(B (s+h) ω-B s ω)+stepDrift α s h c ω) ∂P) -
      (∫ ω, F s (Y ω) ∂P) - (∫ ω, stepCost α s h c ω ∂P) ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) +
      (C₂:ℝ)*(c:ℝ)*(h:ℝ) * (Real.sqrt (h:ℝ)*normalFirstMoment + (c:ℝ)*(h:ℝ)) +
      (L:ℝ)*(h:ℝ) * ((h:ℝ) + Real.sqrt (h:ℝ)*normalFirstMoment + (c:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hAm := stepDrift_measurable hαm s h c h.coe_nonneg
  have hAi := stepDrift_integrable (P := P) hαm hαb s h c h.coe_nonneg c.coe_nonneg
  have hKi := stepCost_integrable (P := P) hαm hαb s h c h.coe_nonneg c.coe_nonneg
  have hG := expected_time_space_step hB hm s h hY hYi hAm c
    (stepDrift_bound hαb s h c h.coe_nonneg c.coe_nonneg) hf
    C₁ C₂ C₃ Ct L hC₁ hC₂ hC₃ hDm hCt hD hL
  have hfd : ContDiff ℝ 2 (deriv (F s)) := (hf s).deriv'
  have hfm : Measurable (fun ω => deriv (F s) (Y ω)) := hfd.continuous.measurable.comp hYm
  have hfi : Integrable (fun ω => deriv (F s) (Y ω)*stepDrift α s h c ω) P :=
    hAi.bdd_mul hfm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hC₁ s (Y ω)))
  have hdi : Integrable (fun ω => D s (Y ω)) P := Integrable.of_bound
    (hDm.comp hYm).aestronglyMeasurable Ct (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hCt (Y ω)))
  have hfdd : ContDiff ℝ 1 (deriv (deriv (F s))) := hfd.deriv'
  have hddi : Integrable (fun ω => deriv (deriv (F s)) (Y ω)) P := Integrable.of_bound
    (hfdd.continuous.measurable.comp hYm).aestronglyMeasurable C₂
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC₂ s (Y ω)))
  let H (ω : Ω) := deriv (F s) (Y ω)*stepDrift α s h c ω-stepCost α s h c ω +
    (h:ℝ)*(D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω))
  have hH : (∫ ω, H ω ∂P) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [] with ω
    have hsq := step_completion_square hαm hαb s h c h.coe_nonneg c.coe_nonneg
      (deriv (F s) (Y ω)) ω
    have he := congrArg (fun z : ℝ => (h:ℝ)*z) (hPDE (Y ω))
    change H ω ≤ 0
    dsimp only [H]
    nlinarith
  have hsub : Integrable (fun ω => deriv (F s) (Y ω)*stepDrift α s h c ω-
      stepCost α s h c ω) P := hfi.sub hKi
  have hadd : Integrable (fun ω => D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω)) P :=
    hdi.add (hddi.const_mul _)
  dsimp only [H] at hH
  rw [integral_add hsub (hadd.const_mul _), integral_sub hfi hKi,
    integral_const_mul, integral_add hdi (hddi.const_mul _), integral_const_mul] at hH
  have ha := le_abs_self
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω+(B (s+h) ω-B s ω)+stepDrift α s h c ω) ∂P) -
      (∫ ω, F s (Y ω) ∂P) -
      (∫ ω, deriv (F s) (Y ω)*stepDrift α s h c ω ∂P) -
      (h:ℝ)*((∫ ω, D s (Y ω) ∂P)+(1/2:ℝ)*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)))
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.ControlledState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma stepDrift_add {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (c : ℝ) (s h : ℝ≥0) (ω : Ω) :
    stepDrift α 0 (s+h) c ω = stepDrift α 0 s c ω + stepDrift α s h c ω := by
  have h0 := (bounded_control_intervalIntegrable hm hb 0 s s.coe_nonneg ω).1.const_mul c
  have hs := (bounded_control_intervalIntegrable hm hb s h h.coe_nonneg ω).1.const_mul c
  simp only [zero_add] at h0
  simpa only [stepDrift, zero_add, NNReal.coe_add] using
    (intervalIntegral.integral_add_adjacent_intervals h0 hs).symm

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

def verificationError (c C₂ C₃ L h : ℝ) : ℝ :=
  C₃/6*(h*Real.sqrt h*normalThirdMoment) +
  C₂*c*h*(Real.sqrt h*normalFirstMoment+c*h) +
  L*h*(h+Real.sqrt h*normalFirstMoment+c*h)

lemma verificationError_limit (T c C₂ C₃ L : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*verificationError c C₂ C₃ L (T/(n:ℝ)))
      atTop (𝓝 0) := by
  convert vanishing_mesh_error T
    (C₃/6*normalThirdMoment+C₂*c*normalFirstMoment+L*normalFirstMoment)
    (C₂*c^2+L*(1+c)) using 1 <;> try rfl
  funext n
  unfold verificationError
  ring

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.ElementaryControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma progressive_joint_measurable (ℱ : Filtration ℝ≥0 mΩ)
    {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive ℱ α) :
    Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2) := by
  have hclip (n : ℕ) : Measurable (fun p : ℝ≥0 × Ω => α (min p.1 n) p.2) := by
    have hs : Measurable[inferInstance, ℱ (n:ℝ≥0)] (fun p : ℝ≥0 × Ω => p.2) :=
      measurable_snd.mono le_rfl (ℱ.le n)
    exact (hα n).comp (((measurable_fst.min measurable_const).subtype_mk
      (h := fun p : ℝ≥0 × Ω => min_le_right p.1 (n:ℝ≥0))).prodMk hs)
  apply measurable_of_tendsto_metrizable hclip
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ≥0)) atTop atTop).eventually
    (eventually_ge_atTop p.1)] with n hn
  simp only [min_eq_left hn]

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.ExpectedFeedbackStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_feedback_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h c : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) {F D : ℝ → ℝ → ℝ} (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t z, |deriv (F t) z| ≤ 1)
    (hC₂ : ∀ t z, |deriv (deriv (F t)) z| ≤ C₂)
    (hC₃ : ∀ t z, |iteratedDeriv 3 (F t) z| ≤ C₃)
    (hDm : Measurable (D s)) (hCt : ∀ z, |D s z| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z)
        (Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ))) r)
    (hL : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z y,
      |D r z-D s y| ≤ (L:ℝ)*(|r-(s:ℝ)|+|z-y|))
    (hPDE : ∀ z, D s z+(1/2:ℝ)*deriv (deriv (F s)) z+
      (c:ℝ)/2*(deriv (F s) z)^2 = 0) :
    |(∫ ω, F ((s:ℝ)+(h:ℝ))
        (Y ω+(B (s+h) ω-B s ω)+(c:ℝ)*(h:ℝ)*deriv (F s) (Y ω)) ∂P) -
      (∫ ω, F s (Y ω) ∂P) -
      (c:ℝ)*(h:ℝ)/2*(∫ ω, (deriv (F s) (Y ω))^2 ∂P)| ≤
        verificationError c C₂ C₃ L h := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hfd : ContDiff ℝ 2 (deriv (F s)) := (hf s).deriv'
  have hfm : Measurable (fun ω => deriv (F s) (Y ω)) := hfd.continuous.measurable.comp hYm
  let A (ω : Ω) := (c:ℝ)*(h:ℝ)*deriv (F s) (Y ω)
  have hAm : Measurable A := hfm.const_mul _
  have hAb : ∀ ω, |A ω| ≤ (c:ℝ)*(h:ℝ) := by
    intro ω
    dsimp only [A]
    rw [abs_mul, abs_mul, abs_of_nonneg c.coe_nonneg, abs_of_nonneg h.coe_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left (hC₁ s (Y ω)) (mul_nonneg c.coe_nonneg h.coe_nonneg)]
  have hG := expected_time_space_step hB hm s h hY hYi hAm c hAb hf
    1 C₂ C₃ Ct L hC₁ hC₂ hC₃ hDm hCt hD hL
  have hui : Integrable (fun ω => (deriv (F s) (Y ω))^2) P := by
    apply Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (hC₁ s (Y ω)) 2
  have hDi : Integrable (fun ω => D s (Y ω)) P := Integrable.of_bound
    (hDm.comp hYm).aestronglyMeasurable Ct (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hCt (Y ω)))
  have hfdd : ContDiff ℝ 1 (deriv (deriv (F s))) := hfd.deriv'
  have hddi : Integrable (fun ω => deriv (deriv (F s)) (Y ω)) P := Integrable.of_bound
    (hfdd.continuous.measurable.comp hYm).aestronglyMeasurable C₂
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC₂ s (Y ω)))
  have hPe : (∫ ω, D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω)+
      (c:ℝ)/2*(deriv (F s) (Y ω))^2 ∂P) = 0 := by
    have he : (fun ω => D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω)+
        (c:ℝ)/2*(deriv (F s) (Y ω))^2) = fun _ => (0:ℝ) := funext (fun ω => hPDE (Y ω))
    rw [he, integral_zero]
  have hsplit := integral_add (hDi.add (hddi.const_mul (1/2:ℝ))) (hui.const_mul ((c:ℝ)/2))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit] at hPe
  have hsplit' := integral_add hDi (hddi.const_mul (1/2:ℝ))
  rw [hsplit', integral_const_mul, integral_const_mul] at hPe
  have hAe : (∫ ω, deriv (F s) (Y ω)*A ω ∂P) =
      (c:ℝ)*(h:ℝ)*(∫ ω, (deriv (F s) (Y ω))^2 ∂P) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp only [A]
    ring
  rw [hAe] at hG
  have hid : (c:ℝ)*(h:ℝ)*(∫ ω, (deriv (F s) (Y ω))^2 ∂P) +
      (h:ℝ)*((∫ ω, D s (Y ω) ∂P)+(1/2:ℝ)*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)) =
      (c:ℝ)*(h:ℝ)/2*(∫ ω, (deriv (F s) (Y ω))^2 ∂P) := by
    have he := congrArg (fun z : ℝ => (h:ℝ)*z) hPe
    nlinarith
  rw [sub_sub] at hG
  rw [hid] at hG
  exact hG

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.ControlledGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma progressive_stepDrift_measurable (ℱ : Filtration ℝ≥0 mΩ)
    {α : ℝ≥0 → Ω → ℝ} (hap : IsProgressive ℱ α) (hab : ∀ t ω, |α t ω| ≤ 1)
    (s h : ℝ≥0) (c : ℝ) :
    Measurable[ℱ (s+h)] (stepDrift (fun r => α (Real.toNNReal r)) s h c) := by
  have ham := progressive_joint_measurable ℱ hap
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have h₁ := progressive_integral_measurable ℱ hap (s+h) (w := fun _ => c) measurable_const
  have h₂ := (progressive_integral_measurable ℱ hap s (w := fun _ => c) measurable_const).mono
    (ℱ.mono (show s ≤ s+h from le_add_of_nonneg_right (show (0:ℝ≥0) ≤ h from zero_le))) le_rfl
  have he : stepDrift (fun r => α (Real.toNNReal r)) s h c = fun ω =>
      (∫ r in (0:ℝ)..((s+h:ℝ≥0):ℝ), c*α (Real.toNNReal r) ω)-
      (∫ r in (0:ℝ)..(s:ℝ), c*α (Real.toNNReal r) ω) := by
    funext ω
    have hh := stepDrift_add (α := fun r => α (Real.toNNReal r)) ham' (fun r ω => hab _ ω) c s h ω
    simpa only [stepDrift, zero_add, NNReal.coe_add] using (eq_sub_of_add_eq' hh.symm)
  rw [he]
  exact h₁.sub h₂

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.SumRangeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma sum_range_blocks (f : ℕ → ℝ) (n m : ℕ) :
    ∑ j ∈ Finset.range (n*m), f j =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, f (k*m+j) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [Nat.succ_mul, Finset.sum_range_add, IH, Finset.sum_range_succ]

lemma stepDrift_subdivision {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (s h c : ℝ) (hh : 0 ≤ h) (m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range m, stepDrift α (s+(j:ℝ)*(h/(m:ℝ))) (h/(m:ℝ)) c ω) =
      stepDrift α s h c ω := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hd : 0 ≤ h/(m:ℝ) := div_nonneg hh (Nat.cast_nonneg m)
  have hint : ∀ j < m, IntervalIntegrable (fun r => c*α r ω) volume
      (s+(j:ℝ)*(h/(m:ℝ))) (s+((j+1:ℕ):ℝ)*(h/(m:ℝ))) := by
    intro j hj
    convert (bounded_control_intervalIntegrable hm hb (s+(j:ℝ)*(h/(m:ℝ))) (h/(m:ℝ)) hd ω).1.const_mul c using 1 <;> try rfl
    push_cast
    ring
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  convert hsum using 1 <;> try rfl
  · apply Finset.sum_congr rfl
    intro j hj
    unfold stepDrift
    congr 1
    push_cast
    ring
  · unfold stepDrift
    congr 1
    · simp
    · field_simp

lemma stepCost_subdivision {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (s h c : ℝ) (hh : 0 ≤ h) (m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range m, stepCost α (s+(j:ℝ)*(h/(m:ℝ))) (h/(m:ℝ)) c ω) =
      stepCost α s h c ω := by
  have hsq : Measurable (fun p : ℝ × Ω => (α p.1 p.2)^2) := hm.pow_const 2
  have hb2 : ∀ r ω, |(α r ω)^2| ≤ 1 := fun r ω => by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (hb r ω) 2
  have he := stepDrift_subdivision (α := fun r ω => (α r ω)^2) hsq hb2 s h c hh m hmpos ω
  unfold stepCost
  rw [← Finset.mul_sum]
  exact congrArg (fun z : ℝ => (1/2:ℝ)*z) he

lemma refined_time (h : ℝ≥0) {m : ℕ} (hm : 0 < m) (k j : ℕ) :
    ((k*m+j:ℕ):ℝ≥0)*(h/(m:ℝ≥0)) = (k:ℝ≥0)*h+(j:ℝ≥0)*(h/(m:ℝ≥0)) := by
  have hm0 : (m:ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

lemma refined_coefficient {m j : ℕ} (hm : 0 < m) (hj : j < m) (k : ℕ) :
    (k*m+j)/m = k := by
  rw [Nat.mul_comm k m, Nat.mul_add_div hm, Nat.div_eq_of_lt hj, Nat.add_zero]

lemma grid_drift_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (h : ℝ≥0) (c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range (n*m), stepDrift α ((j:ℝ≥0)*(h/(m:ℝ≥0))) (h/(m:ℝ≥0)) (c (j/m)) ω) =
      ∑ k ∈ Finset.range n, stepDrift α ((k:ℝ≥0)*h) h (c k) ω := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have ht (j : ℕ) : ((k*m+j:ℕ):ℝ)*(↑h/(↑m:ℝ)) =
      (k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ)) := by
    have he := congrArg NNReal.toReal (refined_time h hmpos k j)
    simpa only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast] using he
  simp only [NNReal.coe_natCast]
  have he : (∑ j ∈ Finset.range m,
      stepDrift α (((k*m+j:ℕ):ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c ((k*m+j)/m)) ω) =
      ∑ j ∈ Finset.range m,
      stepDrift α ((k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c k) ω := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [refined_coefficient hmpos (Finset.mem_range.mp hj) k, ht j]
  rw [he]
  exact stepDrift_subdivision hm hb ((k:ℝ)*(h:ℝ)) h (c k) h.coe_nonneg m hmpos ω

lemma grid_cost_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (h : ℝ≥0) (c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range (n*m), stepCost α ((j:ℝ≥0)*(h/(m:ℝ≥0))) (h/(m:ℝ≥0)) (c (j/m)) ω) =
      ∑ k ∈ Finset.range n, stepCost α ((k:ℝ≥0)*h) h (c k) ω := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have ht (j : ℕ) : ((k*m+j:ℕ):ℝ)*(↑h/(↑m:ℝ)) =
      (k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ)) := by
    have he := congrArg NNReal.toReal (refined_time h hmpos k j)
    simpa only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast] using he
  simp only [NNReal.coe_natCast]
  have he : (∑ j ∈ Finset.range m,
      stepCost α (((k*m+j:ℕ):ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c ((k*m+j)/m)) ω) =
      ∑ j ∈ Finset.range m,
      stepCost α ((k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c k) ω := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [refined_coefficient hmpos (Finset.mem_range.mp hj) k, ht j]
  rw [he]
  exact stepCost_subdivision hm hb ((k:ℝ)*(h:ℝ)) h (c k) h.coe_nonneg m hmpos ω

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

lemma refinement_successor {m : ℕ} (hm : 0 < m) (j : ℕ) :
    (j+1)/m = j/m ∨ ((j+1)/m = j/m+1 ∧ j+1 = (j/m+1)*m) := by
  have hj := Nat.div_add_mod j m
  have hr := Nat.mod_lt j hm
  by_cases he : j%m+1 < m
  · left
    have hde : j+1 = m*(j/m)+(j%m+1) := by omega
    rw [hde, Nat.mul_add_div hm, Nat.div_eq_of_lt he, Nat.add_zero]
  · right
    have he' : j%m+1 = m := by omega
    have hde : j+1 = (j/m+1)*m := by
      calc j+1 = m*(j/m)+(j%m+1) := by omega
           _ = m*(j/m)+m := by rw [he']
           _ = (j/m+1)*m := by ring
    refine ⟨?_, hde⟩
    rw [hde, Nat.mul_comm, Nat.mul_div_cancel_left _ hm]

lemma verificationError_mono (c d C₂ D₂ C₃ D₃ L M h : ℝ≥0)
    (hc : c ≤ d) (h₂ : C₂ ≤ D₂) (h₃ : C₃ ≤ D₃) (hL : L ≤ M) :
    verificationError c C₂ C₃ L h ≤ verificationError d D₂ D₃ M h := by
  have hF := normalFirstMoment_nonneg
  have hT := normalThirdMoment_nonneg
  unfold verificationError
  gcongr

end ZeroTemperatureSK.WeakIto

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.VariableGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Nonuniform
open WeakIto Heat
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def time (h : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := ∑ k ∈ Finset.range n, h k

@[simp] lemma time_zero (h : ℕ → ℝ≥0) : time h 0 = 0 := by simp [time]
@[simp] lemma time_succ (h : ℕ → ℝ≥0) (n : ℕ) : time h (n+1) = time h n+h n := by
  simp only [time,Finset.sum_range_succ]
lemma time_mono (h : ℕ → ℝ≥0) : Monotone (time h) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [time_succ]
  exact le_add_of_nonneg_right (bot_le : (0:ℝ≥0) ≤ h n)

lemma coe_time_succ (h : ℕ → ℝ≥0) (n : ℕ) : (time h (n+1):ℝ) = (time h n:ℝ)+(h n:ℝ) := by
  rw [time_succ,NNReal.coe_add]

def controlled (B α : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (x : ℝ) : ℕ → Ω → ℝ
  | 0, _ => x
  | k+1, ξ => controlled B α h c x k ξ + (B (time h (k+1)) ξ-B (time h k) ξ)+
      stepDrift (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ

lemma controlled_adapted {B α : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1) (h c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (time h n)]
      (controlled B α h c x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hle := time_mono h (Nat.le_succ n)
    have hYm := ih.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBs := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h n)).measurable.mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h (n+1))).measurable
    have hAm := progressive_stepDrift_measurable _ hap hab (time h n) (h n) (c n)
    rw [← time_succ] at hAm
    exact (hYm.add (hBt.sub hBs)).add hAm

lemma controlled_integrable {B α : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2))
    (hab : ∀ t ξ, |α t ξ| ≤ 1) (h c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) :
    Integrable (controlled B α h c x n) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  induction n with
  | zero => exact integrable_const x
  | succ n ih =>
    exact (ih.add ((hB.integrable_eval _).sub (hB.integrable_eval _))).add
      (stepDrift_integrable ham' (fun r ξ => hab _ ξ) (time h n) (h n) (c n)
        (h n).coe_nonneg (c n).coe_nonneg)

omit mΩ in
lemma controlled_formula (B α : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) (ξ : Ω) :
    controlled B α h c x n ξ = x+B (time h n) ξ-B 0 ξ+
      ∑ k ∈ Finset.range n, stepDrift (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ := by
  induction n with
  | zero => simp [controlled]
  | succ n ih => rw [controlled,ih,Finset.sum_range_succ]; ring

def elementary (h : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) : ℕ → ℝ≥0 → Ω → ℝ
  | 0, _, _ => 0
  | n+1, t, ξ => if time h n ≤ t ∧ t < time h (n+1) then a n ξ else elementary h a n t ξ

omit mΩ in
lemma elementary_bound (h : ℕ → ℝ≥0) {a : ℕ → Ω → ℝ} (ha : ∀ k ξ, |a k ξ| ≤ 1)
    (n : ℕ) (t : ℝ≥0) (ξ : Ω) : |elementary h a n t ξ| ≤ 1 := by
  induction n with
  | zero => simp [elementary]
  | succ n ih => simp only [elementary]; split_ifs <;> first | exact ha n ξ | exact ih

lemma elementary_progressive (ℱ : Filtration ℝ≥0 mΩ) (h : ℕ → ℝ≥0)
    {a : ℕ → Ω → ℝ} (ha : ∀ n, Measurable[ℱ (time h n)] (a n)) (n : ℕ) :
    IsProgressive ℱ (elementary h a n) := by
  induction n with
  | zero => exact isProgressive_const ℱ 0
  | succ n ih =>
    intro s
    by_cases hns : time h n ≤ s
    · have ham : Measurable[ℱ s] (a n) := (ha n).mono (ℱ.mono hns) le_rfl
      let : MeasurableSpace Ω := ℱ s
      have htime : Measurable (fun p : Set.Iic s × Ω => (p.1:ℝ≥0)) :=
        measurable_subtype_coe.comp measurable_fst
      have hset : MeasurableSet {p : Set.Iic s × Ω |
          time h n ≤ (p.1:ℝ≥0) ∧ (p.1:ℝ≥0) < time h (n+1)} :=
        (measurableSet_le (measurable_const : Measurable (fun _ : Set.Iic s × Ω => time h n)) htime).inter
          (measurableSet_lt (α := ℝ≥0) (f := fun p : Set.Iic s × Ω => (p.1:ℝ≥0))
            (g := fun _ : Set.Iic s × Ω => time h (n+1)) htime measurable_const)
      exact (ham.comp measurable_snd).ite hset (ih s)
    · convert ih s using 1 <;> try rfl
      funext p
      have hn : ¬time h n ≤ (p.1:ℝ≥0) := fun ht => hns (ht.trans p.1.property)
      simp only [elementary,hn,false_and,↓reduceIte]

omit mΩ in
lemma elementary_on_step (h : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (n k : ℕ) (hk : k < n)
    (t : ℝ≥0) (ht : time h k ≤ t ∧ t < time h (k+1)) (ξ : Ω) :
    elementary h a n t ξ = a k ξ := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst k; simp only [elementary,ite_eq_left ht]
    · have hk' : k < n := by omega
      have hlt : t < time h n := ht.2.trans_le (time_mono h (by omega : k+1 ≤ n))
      simp only [elementary,not_le.mpr hlt,false_and,↓reduceIte]
      exact ih hk'

omit mΩ in
lemma elementary_integral_on_step (h : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ)
    (n k : ℕ) (hk : k < n) (φ : ℝ → ℝ) (ξ : Ω) :
    (∫ r in (time h k:ℝ)..(time h k:ℝ)+(h k:ℝ),
      φ (elementary h a n (Real.toNNReal r) ξ)) = (h k:ℝ)*φ (a k ξ) := by
  have he : (∫ r in (time h k:ℝ)..(time h k:ℝ)+(h k:ℝ),
      φ (elementary h a n (Real.toNNReal r) ξ)) =
      ∫ _r in (time h k:ℝ)..(time h k:ℝ)+(h k:ℝ), φ (a k ξ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [(h k).coe_nonneg])
    intro r hr
    have hr0 : 0 ≤ r := (time h k).coe_nonneg.trans hr.1.le
    have ht : time h k ≤ Real.toNNReal r ∧ Real.toNNReal r < time h (k+1) := by
      constructor
      · apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ hr0]
        exact hr.1.le
      · apply NNReal.coe_lt_coe.mp
        rw [Real.coe_toNNReal _ hr0,coe_time_succ]
        exact hr.2
    change φ (elementary h a n (Real.toNNReal r) ξ) = φ (a k ξ)
    rw [elementary_on_step h a n k hk _ ht ξ]
  rw [he,intervalIntegral.integral_const]
  simp only [add_sub_cancel_left,smul_eq_mul]

structure GridData (N : ℕ) (h c : ℕ → ℝ≥0) (F D : ℕ → ℝ → ℝ → ℝ) where
  C₂ : ℝ≥0
  C₃ : ℝ≥0
  Ct : ℝ≥0
  L : ℝ≥0
  Γ : ℝ≥0
  smooth : ∀ k t, ContDiff ℝ 3 (F k t)
  gradient_bound : ∀ k t z, |deriv (F k t) z| ≤ 1
  seam : ∀ k < N, F k (time h (k+1)) = F (k+1) (time h (k+1))
  coefficient_bound : ∀ k < N, c k ≤ Γ
  second_bound : ∀ k < N, ∀ t z, |deriv (deriv (F k t)) z| ≤ C₂
  third_bound : ∀ k < N, ∀ t z, |iteratedDeriv 3 (F k t) z| ≤ C₃
  rate_measurable : ∀ k t, Measurable (D k t)
  rate_bound : ∀ k < N, ∀ t z, |D k t z| ≤ Ct
  time_derivative : ∀ k < N, ∀ r ∈ Icc (time h k:ℝ) (time h (k+1):ℝ), ∀ z,
      HasDerivWithinAt (fun t => F k t z) (D k r z)
        (Icc (time h k:ℝ) (time h (k+1):ℝ)) r
  rate_joint : ∀ k < N, ∀ r ∈ Icc (time h k:ℝ) (time h (k+1):ℝ),
      ∀ s ∈ Icc (time h k:ℝ) (time h (k+1):ℝ), ∀ z y,
      |D k r z-D k s y| ≤ (L:ℝ)*(|r-s|+|z-y|)
  pde : ∀ k < N, ∀ t ∈ Icc (time h k:ℝ) (time h (k+1):ℝ), ∀ z,
      D k t z+(1/2:ℝ)*deriv (deriv (F k t)) z+(c k:ℝ)/2*(deriv (F k t) z)^2 = 0

def profit (B α : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  (∫ ξ, f (controlled B α h c x N ξ) ∂P)-
    ∑ k ∈ Finset.range N, ∫ ξ, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P

lemma telescope_bound (Q K ε : ℕ → ℝ) (n : ℕ)
    (hs : ∀ k < n, Q (k+1)-Q k-K k ≤ ε k) :
    Q n-Q 0-(∑ k ∈ Finset.range n, K k) ≤ ∑ k ∈ Finset.range n, ε k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun k hk => hs k (by omega))
    have hlast := hs n (by omega)
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    linarith

lemma GridData.mesh_upper {B α : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) :
    profit (P := P) B α h c (F N (time h N)) x N-F 0 0 x ≤
      ∑ k ∈ Finset.range N, verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ham := progressive_joint_measurable _ hap
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  let Q (k : ℕ) := ∫ ξ, F k (time h k) (controlled B α h c x k ξ) ∂P
  let K (k : ℕ) := ∫ ξ, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P
  have hstep (k : ℕ) (hk : k < N) : Q (k+1)-Q k-K k ≤ verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
    have hleft : (time h k:ℝ) ∈ Icc (time h k:ℝ) (time h (k+1):ℝ) :=
      ⟨le_rfl,NNReal.coe_le_coe.mpr (time_mono h (Nat.le_succ k))⟩
    have hu := expected_verification_step hB hm (time h k) (h k) (c k)
      (controlled_adapted hm hap hab h c x k) (controlled_integrable hB ham hab h c x k)
      (α := fun r => α (Real.toNNReal r)) ham' (fun r ξ => hab _ ξ)
      (sd.smooth k) 1 sd.C₂ sd.C₃ sd.Ct sd.L
      (sd.gradient_bound k) (sd.second_bound k hk) (sd.third_bound k hk)
      (sd.rate_measurable k _) (sd.rate_bound k hk _)
      (by simpa only [coe_time_succ] using sd.time_derivative k hk)
      (by simpa only [coe_time_succ] using
        fun r hr z y => sd.rate_joint k hk r hr (time h k) hleft z y)
      (sd.pde k hk (time h k) hleft)
    have he : (fun ξ => F k ((time h k:ℝ)+(h k:ℝ))
        (controlled B α h c x k ξ+(B (time h k+h k) ξ-B (time h k) ξ)+
          stepDrift (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ)) =
        fun ξ => F (k+1) (time h (k+1)) (controlled B α h c x (k+1) ξ) := by
      funext ξ
      rw [← time_succ,← coe_time_succ,sd.seam k hk]
      rfl
    rw [he] at hu
    exact hu.trans (verificationError_mono (c k) sd.Γ sd.C₂ sd.C₂ sd.C₃ sd.C₃ sd.L sd.L (h k)
      (sd.coefficient_bound k hk) le_rfl le_rfl le_rfl)
  have hh := telescope_bound Q K (fun k => verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) N hstep
  have hz : Q 0 = F 0 0 x := by simp [Q,controlled]
  rw [hz] at hh
  dsimp only [profit]
  linarith

def euler (B : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (u : ℕ → ℝ → ℝ) (x : ℝ) : ℕ → Ω → ℝ
  | 0, _ => x
  | k+1, ξ => euler B h c u x k ξ+(B (time h (k+1)) ξ-B (time h k) ξ)+
      (c k:ℝ)*(h k:ℝ)*u k (euler B h c u x k ξ)

lemma euler_adapted {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (h c : ℕ → ℝ≥0) {u : ℕ → ℝ → ℝ} (hum : ∀ k, Measurable (u k)) (x : ℝ) (n : ℕ) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (time h n)]
      (euler B h c u x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hle := time_mono h (Nat.le_succ n)
    have hYm := ih.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBs := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h n)).measurable.mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h (n+1))).measurable
    exact (hYm.add (hBt.sub hBs)).add (((hum n).comp hYm).const_mul ((c n:ℝ)*(h n:ℝ)))

omit mΩ in
lemma euler_controlled {B : ℝ≥0 → Ω → ℝ} (h c : ℕ → ℝ≥0) (u : ℕ → ℝ → ℝ)
    (x : ℝ) (n k : ℕ) (hk : k ≤ n) (ξ : Ω) :
    controlled B (elementary h (fun j ξ => u j (euler B h c u x j ξ)) n) h c x k ξ =
      euler B h c u x k ξ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < n := by omega
    have he := elementary_integral_on_step h (fun j ξ => u j (euler B h c u x j ξ)) n k hk'
      (fun z => (c k:ℝ)*z) ξ
    change stepDrift (fun r => elementary h (fun j ξ => u j (euler B h c u x j ξ)) n (Real.toNNReal r))
      (time h k) (h k) (c k) ξ = (h k:ℝ)*((c k:ℝ)*u k (euler B h c u x k ξ)) at he
    rw [controlled,he,ih (by omega),euler]
    ring

lemma GridData.mesh_lower {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) :
    ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
      (∀ t ξ, |α t ξ| ≤ 1) ∧
      F 0 0 x-(∑ k ∈ Finset.range N, verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) ≤
        profit (P := P) B α h c (F N (time h N)) x N := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let u (k : ℕ) := deriv (F k (time h k))
  let a (k : ℕ) (ξ : Ω) := u k (euler B h c u x k ξ)
  let α := elementary h a N
  have hum : ∀ k, Measurable (u k) := fun k =>
    (show ContDiff ℝ 2 (u k) from (sd.smooth k _).deriv').continuous.measurable
  have hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α :=
    elementary_progressive _ h (fun k => (hum k).comp (euler_adapted hm h c hum x k)) N
  have hab : ∀ t ξ, |α t ξ| ≤ 1 := elementary_bound h (fun k ξ => sd.gradient_bound _ _ _) N
  refine ⟨α,hap,hab,?_⟩
  have ham := progressive_joint_measurable _ hap
  have hgrid (k : ℕ) (hk : k ≤ N) (ξ : Ω) :
      controlled B α h c x k ξ = euler B h c u x k ξ := euler_controlled h c u x N k hk ξ
  let Q (k : ℕ) := ∫ ξ, F k (time h k) (controlled B α h c x k ξ) ∂P
  let K (k : ℕ) := ∫ ξ, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P
  have hstep (k : ℕ) (hk : k < N) : -Q (k+1)-(-Q k)-(-K k) ≤
      verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
    have hleft : (time h k:ℝ) ∈ Icc (time h k:ℝ) (time h (k+1):ℝ) :=
      ⟨le_rfl,NNReal.coe_le_coe.mpr (time_mono h (Nat.le_succ k))⟩
    have hg := expected_feedback_step hB hm (time h k) (h k) (c k)
      (controlled_adapted hm hap hab h c x k) (controlled_integrable hB ham hab h c x k)
      (sd.smooth k) sd.C₂ sd.C₃ sd.Ct sd.L (sd.gradient_bound k) (sd.second_bound k hk)
      (sd.third_bound k hk) (sd.rate_measurable k _) (sd.rate_bound k hk _)
      (by simpa only [coe_time_succ] using sd.time_derivative k hk)
      (by simpa only [coe_time_succ] using
        fun r hr z y => sd.rate_joint k hk r hr (time h k) hleft z y)
      (sd.pde k hk (time h k) hleft)
    have he : (fun ξ => F k ((time h k:ℝ)+(h k:ℝ))
        (controlled B α h c x k ξ+(B (time h k+h k) ξ-B (time h k) ξ)+
          (c k:ℝ)*(h k:ℝ)*deriv (F k (time h k)) (controlled B α h c x k ξ))) =
        fun ξ => F (k+1) (time h (k+1)) (controlled B α h c x (k+1) ξ) := by
      funext ξ
      rw [← time_succ,← coe_time_succ,sd.seam k hk]
      rw [hgrid k hk.le,hgrid (k+1) (by omega)]
      rfl
    rw [he] at hg
    have hK : K k = (c k:ℝ)*(h k:ℝ)/2*
        (∫ ξ, (deriv (F k (time h k)) (controlled B α h c x k ξ))^2 ∂P) := by
      dsimp only [K]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      have hh := elementary_integral_on_step h a N k hk (fun z => (c k:ℝ)*z^2) ξ
      change stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ = _
      rw [stepCost,hh]
      dsimp only [a,u]
      rw [hgrid k hk.le]
      ring
    have hg' : |Q (k+1)-Q k-K k| ≤ verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
      rw [hK]
      exact hg.trans (verificationError_mono (c k) sd.Γ sd.C₂ sd.C₂ sd.C₃ sd.C₃ sd.L sd.L (h k)
        (sd.coefficient_bound k hk) le_rfl le_rfl le_rfl)
    linarith [(abs_le.mp hg').1]
  have hh := telescope_bound (fun k => -Q k) (fun k => -K k)
    (fun k => verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) N hstep
  have hz : Q 0 = F 0 0 x := by simp [Q,controlled]
  rw [hz,Finset.sum_neg_distrib] at hh
  change F 0 0 x-(∑ k ∈ Finset.range N, verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) ≤
    Q N-∑ k ∈ Finset.range N, K k
  linarith

def refineLengths (h : ℕ → ℝ≥0) (m : ℕ) : ℕ → ℝ≥0 := fun j => h (j/m)/(m:ℝ≥0)

lemma refine_time_block (h : ℕ → ℝ≥0) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    time (refineLengths h m) (k*m) = time h k := by
  apply NNReal.coe_injective
  simp only [time,NNReal.coe_sum,refineLengths,NNReal.coe_div,NNReal.coe_natCast]
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ j ∈ Finset.range m, (h ((i*m+j)/m):ℝ)/(m:ℝ)) =
      ∑ _j ∈ Finset.range m, (h i:ℝ)/(m:ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [refined_coefficient hm (Finset.mem_range.mp hj)]
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma refine_time_inside (h : ℕ → ℝ≥0) {m : ℕ} (hm : 0 < m) (k j : ℕ) (hj : j ≤ m) :
    time (refineLengths h m) (k*m+j) = time h k+(j:ℝ≥0)*(h k/(m:ℝ≥0)) := by
  induction j with
  | zero => simp only [refine_time_block h hm,Nat.cast_zero,zero_mul,add_zero]
  | succ j ih =>
    have hjm : j < m := by omega
    rw [show k*m+(j+1) = (k*m+j)+1 by omega,time_succ,ih (by omega)]
    simp only [refineLengths,refined_coefficient hm hjm,Nat.cast_add,Nat.cast_one]
    ring

lemma refine_cell_subset (h : ℕ → ℝ≥0) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Icc (time (refineLengths h m) j:ℝ) (time (refineLengths h m) (j+1):ℝ) ⊆
      Icc (time h (j/m):ℝ) (time h (j/m+1):ℝ) := by
  have hl : j/m*m ≤ j := Nat.div_mul_le_self _ _
  have hu : j+1 ≤ (j/m+1)*m := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self _)
  intro r hr
  constructor
  · have ht := time_mono (refineLengths h m) hl
    rw [refine_time_block h hm] at ht
    exact (NNReal.coe_le_coe.mpr ht).trans hr.1
  · have ht := time_mono (refineLengths h m) hu
    rw [refine_time_block h hm] at ht
    exact hr.2.trans (NNReal.coe_le_coe.mpr ht)

lemma grid_drift_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ξ, |α r ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ξ : Ω) :
    (∑ j ∈ Finset.range (n*m), stepDrift α (time (refineLengths h m) j)
      (refineLengths h m j) (c (j/m)) ξ) =
      ∑ k ∈ Finset.range n, stepDrift α (time h k) (h k) (c k) ξ := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (∑ j ∈ Finset.range m, stepDrift α (time (refineLengths h m) (k*m+j))
      (refineLengths h m (k*m+j)) (c ((k*m+j)/m)) ξ) =
      ∑ j ∈ Finset.range m, stepDrift α ((time h k:ℝ)+(j:ℝ)*((h k:ℝ)/(m:ℝ)))
        ((h k:ℝ)/(m:ℝ)) (c k) ξ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    rw [refine_time_inside h hmpos k j hjm.le]
    simp only [refineLengths,refined_coefficient hmpos hjm,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_div,NNReal.coe_natCast]
  rw [he]
  exact stepDrift_subdivision hm hb (time h k) (h k) (c k) (h k).coe_nonneg m hmpos ξ

lemma grid_cost_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ξ, |α r ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ξ : Ω) :
    (∑ j ∈ Finset.range (n*m), stepCost α (time (refineLengths h m) j)
      (refineLengths h m j) (c (j/m)) ξ) =
      ∑ k ∈ Finset.range n, stepCost α (time h k) (h k) (c k) ξ := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (∑ j ∈ Finset.range m, stepCost α (time (refineLengths h m) (k*m+j))
      (refineLengths h m (k*m+j)) (c ((k*m+j)/m)) ξ) =
      ∑ j ∈ Finset.range m, stepCost α ((time h k:ℝ)+(j:ℝ)*((h k:ℝ)/(m:ℝ)))
        ((h k:ℝ)/(m:ℝ)) (c k) ξ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    rw [refine_time_inside h hmpos k j hjm.le]
    simp only [refineLengths,refined_coefficient hmpos hjm,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_div,NNReal.coe_natCast]
  rw [he]
  exact stepCost_subdivision hm hb (time h k) (h k) (c k) (h k).coe_nonneg m hmpos ξ
lemma controlled_refinement (B : ℝ≥0 → Ω → ℝ) {α : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hb : ∀ r ξ, |α r ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (x : ℝ) (n m : ℕ) (hmpos : 0 < m) (ξ : Ω) :
    controlled B α (refineLengths h m) (fun j => c (j/m)) x (n*m) ξ =
      controlled B α h c x n ξ := by
  have hm' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    hm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  simp only [controlled_formula,refine_time_block h hmpos]
  rw [grid_drift_refinement hm' (fun r ξ => hb _ ξ) h c n m hmpos ξ]

lemma profit_refinement {B α : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P]
    (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hab : ∀ t ξ, |α t ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (x : ℝ) (N m : ℕ) (hmpos : 0 < m) :
    profit (P := P) B α (refineLengths h m) (fun j => c (j/m)) f x (N*m) =
      profit (P := P) B α h c f x N := by
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  unfold profit
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with ξ
    rw [controlled_refinement B ham hab h c x N m hmpos ξ]
  · have hi (d a : ℝ≥0) (s : ℝ) : Integrable (stepCost (fun r => α (Real.toNNReal r)) s d a) P :=
      stepCost_integrable (α := fun r => α (Real.toNNReal r)) ham' (fun r ξ => hab _ ξ) s d a d.coe_nonneg a.coe_nonneg
    rw [← integral_finsetSum (Finset.range (N*m)) (fun j _ => hi _ _ _),
      ← integral_finsetSum (Finset.range N) (fun k _ => hi _ _ _)]
    apply integral_congr_ae
    filter_upwards [] with ξ
    exact grid_cost_refinement ham' (fun r ξ => hab _ ξ) h c N m hmpos ξ

noncomputable def GridData.refine {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (m : ℕ) (hm : 0 < m) :
    GridData (N*m) (refineLengths h m) (fun j => c (j/m)) (fun j => F (j/m)) (fun j => D (j/m)) := by
  have hq (j : ℕ) (hj : j < N*m) : j/m < N := (Nat.div_lt_iff_lt_mul hm).mpr hj
  refine ⟨sd.C₂,sd.C₃,sd.Ct,sd.L,sd.Γ,
    fun j => sd.smooth (j/m), fun j => sd.gradient_bound (j/m), ?_,
    fun j hj => sd.coefficient_bound _ (hq j hj),
    fun j hj => sd.second_bound _ (hq j hj),
    fun j hj => sd.third_bound _ (hq j hj), fun j => sd.rate_measurable (j/m),
    fun j hj => sd.rate_bound _ (hq j hj), ?_,?_,?_⟩
  · intro j hj
    rcases refinement_successor hm j with he | ⟨he,hde⟩
    · rw [he]
    · rw [he,hde,refine_time_block h hm]
      exact sd.seam (j/m) (hq j hj)
  · intro j hj r hr z
    exact (sd.time_derivative _ (hq j hj) r (refine_cell_subset h hm j hr) z).mono
      (refine_cell_subset h hm j)
  · intro j hj r hr s hs z y
    exact sd.rate_joint _ (hq j hj) r (refine_cell_subset h hm j hr) s
      (refine_cell_subset h hm j hs) z y
  · intro j hj t ht z
    exact sd.pde _ (hq j hj) t (refine_cell_subset h hm j ht) z

lemma sum_error_refinement (h : ℕ → ℝ≥0) (N m : ℕ) (hm : 0 < m) (Γ C₂ C₃ L : ℝ≥0) :
    (∑ j ∈ Finset.range (N*m), verificationError Γ C₂ C₃ L (refineLengths h m j)) =
      ∑ k ∈ Finset.range N, (m:ℝ)*verificationError Γ C₂ C₃ L ((h k:ℝ)/(m:ℝ)) := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (∑ j ∈ Finset.range m, verificationError Γ C₂ C₃ L (refineLengths h m (k*m+j))) =
      ∑ _j ∈ Finset.range m, verificationError Γ C₂ C₃ L ((h k:ℝ)/(m:ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [refineLengths,refined_coefficient hm (Finset.mem_range.mp hj),NNReal.coe_div,NNReal.coe_natCast]
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma refined_error_limit (h : ℕ → ℝ≥0) (N : ℕ) (Γ C₂ C₃ L : ℝ≥0) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range N,
      (m:ℝ)*verificationError Γ C₂ C₃ L ((h k:ℝ)/(m:ℝ))) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range N) (fun k _ => verificationError_limit (h k) Γ C₂ C₃ L)

def objectives {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t)) (h c : ℕ → ℝ≥0)
    (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ α : ℝ≥0 → Ω → ℝ,
    IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
    (∀ t ξ, |α t ξ| ≤ 1) ∧ v = profit (P := P) B α h c f x N}

lemma objectives_nonempty {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : (objectives (P := P) hm h c f x N).Nonempty := by
  exact ⟨_,fun _ _ => 0,isProgressive_const _ _,by simp,rfl⟩

lemma GridData.control_upper {B α : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) :
    profit (P := P) B α h c (F N (time h N)) x N ≤ F 0 0 x := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hlim := refined_error_limit h N sd.Γ sd.C₂ sd.C₃ sd.L
  have hh : profit (P := P) B α h c (F N (time h N)) x N-F 0 0 x ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm1
    have hmpos : 0 < m := by omega
    have hu := (sd.refine m hmpos).mesh_upper hB hm hap hab x
    have hdiv : N*m/m = N := by rw [Nat.mul_comm,Nat.mul_div_cancel_left _ hmpos]
    change profit (P := P) B α (refineLengths h m) (fun j => c (j/m))
      (F (N*m/m) (time (refineLengths h m) (N*m))) x (N*m)-F (0/m) 0 x ≤
      ∑ j ∈ Finset.range (N*m), verificationError sd.Γ sd.C₂ sd.C₃ sd.L (refineLengths h m j) at hu
    rw [hdiv,refine_time_block h hmpos,Nat.zero_div,
      profit_refinement (progressive_joint_measurable _ hap) hab h c _ x N m hmpos,
      sum_error_refinement h N m hmpos] at hu
    exact hu
  linarith

lemma GridData.control_lower {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v ∈ objectives (P := P) hm h c (F N (time h N)) x N, F 0 0 x-ε ≤ v := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hlim := refined_error_limit h N sd.Γ sd.C₂ sd.C₃ sd.L
  obtain ⟨m,hm1,he⟩ := ((eventually_ge_atTop (1:ℕ)).and (hlim.eventually (gt_mem_nhds hε))).exists
  have hmpos : 0 < m := by omega
  obtain ⟨α,hap,hab,hl⟩ := (sd.refine m hmpos).mesh_lower hB hm x
  have hdiv : N*m/m = N := by rw [Nat.mul_comm,Nat.mul_div_cancel_left _ hmpos]
  change F (0/m) 0 x-(∑ j ∈ Finset.range (N*m),
    verificationError sd.Γ sd.C₂ sd.C₃ sd.L (refineLengths h m j)) ≤
    profit (P := P) B α (refineLengths h m) (fun j => c (j/m))
      (F (N*m/m) (time (refineLengths h m) (N*m))) x (N*m) at hl
  rw [hdiv,refine_time_block h hmpos,Nat.zero_div,
    profit_refinement (progressive_joint_measurable _ hap) hab h c _ x N m hmpos,
    sum_error_refinement h N m hmpos] at hl
  refine ⟨_,⟨α,hap,hab,rfl⟩,?_⟩
  linarith

def cascadeV (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, x => f x
  | n+1, k, x => logSemigroup (c k) (h k) (cascadeV h c f n (k+1)) x

lemma cascadeV_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) : LipschitzWith K (cascadeV h c f N k) := by
  induction N generalizing k with
  | zero => exact hf
  | succ N ih => exact logSemigroup_lipschitz (ih (k+1)) (c k).coe_nonneg (h k)

lemma cascadeV_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) : RegularDatum (cascadeV h c f N k) := by
  induction N generalizing k with
  | zero => exact hf
  | succ N ih =>
    exact regularDatum_logSemigroup (ih (k+1))
      (cascadeV_lipschitz hLip h c N (k+1)) (c k).coe_nonneg (h k)

def cascadeVAt (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ :=
  cascadeV h c f (N-k) k

def cellVHeat (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ → ℝ :=
  backward (c k) (time h (min (k+1) N)) (cascadeVAt h c f N (k+1))

def cellVRate (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ → ℝ :=
  backwardRate (c k) (time h (min (k+1) N)) (cascadeVAt h c f N (k+1))

lemma cellVHeat_verificationData {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) :
    VerificationData (cellVHeat h c f N k) (cellVRate h c f N k) (c k) (time h (min (k+1) N)) :=
  backward_verificationData (cascadeV_regular hf hLip h c _ _)
    (cascadeV_lipschitz hLip h c _ _) (c k).coe_nonneg _

lemma cellVHeat_left {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) (hk : k ≤ N) :
    cellVHeat h c f N k (time h k) = cascadeVAt h c f N k := by
  by_cases he : k = N
  · subst k
    funext x
    simpa [cellVHeat,cascadeVAt,cascadeV,Nat.min_eq_right (Nat.le_succ N)] using
      backward_terminal (c N) (time h N) f x
  · have hk' : k < N := lt_of_le_of_ne hk he
    have hN : N-k = (N-(k+1))+1 := by omega
    funext x
    unfold cellVHeat cascadeVAt backward
    rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
    have ht : (time h (k+1):ℝ)-(time h k:ℝ) = (h k:ℝ) := by rw [coe_time_succ]; ring
    rw [ht,hN,cascadeV]
    exact varianceLogHeat_eq_logSemigroup
      (cascadeV_regular hf hLip h c _ _).smooth.continuous.measurable (c k) (h k) x

lemma cellVHeat_right (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) (hk : k < N) :
    cellVHeat h c f N k (time h (k+1)) = cascadeVAt h c f N (k+1) := by
  funext x
  dsimp only [cellVHeat]
  rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
  exact backward_terminal _ _ _ _

lemma cellVHeat_seam {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) (hk : k < N) :
    cellVHeat h c f N k (time h (k+1)) = cellVHeat h c f N (k+1) (time h (k+1)) := by
  rw [cellVHeat_right h c f N k hk,cellVHeat_left hf hLip h c N (k+1) (by omega)]

noncomputable def cellVHeat_gridData {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N : ℕ) : GridData N h c (cellVHeat h c f N) (cellVRate h c f N) := by
  classical
  have hd (k : ℕ) := cellVHeat_verificationData hf hLip h c N k
  have hb (k : ℕ) := (hd k).bounds
  choose C₂ C₃ Ct L H using hb
  refine ⟨(Finset.range N).sup C₂,(Finset.range N).sup C₃,
    (Finset.range N).sup Ct,(Finset.range N).sup L,(Finset.range N).sup c,
    fun k => (hd k).smooth,fun k => (hd k).gradient_bound,
    cellVHeat_seam hf hLip h c N,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    exact Finset.le_sup (f := c) (Finset.mem_range.mpr hk)
  · intro k hk t z
    exact ((H k).1 t z).trans (by exact_mod_cast Finset.le_sup (f := C₂) (Finset.mem_range.mpr hk))
  · intro k hk t z
    exact ((H k).2.1 t z).trans (by exact_mod_cast Finset.le_sup (f := C₃) (Finset.mem_range.mpr hk))
  · exact fun k => (H k).2.2.1
  · intro k hk t z
    exact ((H k).2.2.2.1 t z).trans (by exact_mod_cast Finset.le_sup (f := Ct) (Finset.mem_range.mpr hk))
  · intro k hk r hr z
    have hs : Icc (time h k:ℝ) (time h (k+1):ℝ) ⊆ Icc (0:ℝ) (time h (min (k+1) N):ℝ) := by
      rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
      exact fun s hs => ⟨(time h k).coe_nonneg.trans hs.1,hs.2⟩
    exact ((H k).2.2.2.2.1 r (hs hr) z).mono hs
  · intro k hk r hr s hs z y
    have hsub : Icc (time h k:ℝ) (time h (k+1):ℝ) ⊆ Icc (0:ℝ) (time h (min (k+1) N):ℝ) := by
      rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
      exact fun t ht => ⟨(time h k).coe_nonneg.trans ht.1,ht.2⟩
    exact ((H k).2.2.2.2.2.1 r (hsub hr) s (hsub hs) z y).trans (by
      gcongr
      exact_mod_cast Finset.le_sup (f := L) (Finset.mem_range.mpr hk))
  · intro k hk t ht z
    apply (H k).2.2.2.2.2.2 t
    rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
    exact ⟨(time h k).coe_nonneg.trans ht.1,ht.2⟩

theorem cascadeV_eq_control_sup {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N : ℕ) (x : ℝ) :
    cascadeV h c f N 0 x = sSup (objectives (P := P) hm h c f x N) := by
  let sd := cellVHeat_gridData hf hLip h c N
  have hend : cellVHeat h c f N N (time h N) = f := by
    rw [cellVHeat_left hf hLip h c N N le_rfl]
    simp [cascadeVAt,cascadeV]
  have hstart : cellVHeat h c f N 0 0 x = cascadeV h c f N 0 x := by
    have he := congrFun (cellVHeat_left hf hLip h c N 0 (Nat.zero_le N)) x
    simpa only [time_zero,NNReal.coe_zero,cascadeVAt,Nat.sub_zero] using he
  have hu : ∀ v ∈ objectives (P := P) hm h c f x N, v ≤ cascadeV h c f N 0 x := by
    intro v hv
    obtain ⟨α,hap,hab,hv⟩ := hv
    rw [hv]
    have hh := sd.control_upper hB hm hap hab x
    change profit (P := P) B α h c (cellVHeat h c f N N (time h N)) x N ≤
      cellVHeat h c f N 0 0 x at hh
    rwa [hend,hstart] at hh
  have hb : BddAbove (objectives (P := P) hm h c f x N) := ⟨_,hu⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hh := sd.control_lower hB hm x hε
    change ∃ v ∈ objectives (P := P) hm h c (cellVHeat h c f N N (time h N)) x N,
      cellVHeat h c f N 0 0 x-ε ≤ v at hh
    rw [hend,hstart] at hh
    obtain ⟨v,hv,hl⟩ := hh
    have hs := le_csSup hb hv
    linarith
  · exact csSup_le (objectives_nonempty hm h c f x N) hu

end ZeroTemperatureSK.Nonuniform

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.MeasurableSpatialDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma measurable_spatial_deriv {F : ℝ → ℝ → ℝ}
    (hm : Measurable (fun p : ℝ × ℝ => F p.1 p.2))
    (hd : ∀ r, Differentiable ℝ (F r)) :
    Measurable (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  let h : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht : Tendsto h atTop (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat,?_⟩
    exact Eventually.of_forall (fun n => by simp only [Set.mem_compl_iff,Set.mem_singleton_iff]; dsimp [h]; positivity)
  apply measurable_of_tendsto_metrizable
    (f := fun n (p : ℝ × ℝ) => (h n)⁻¹*(F p.1 (p.2+h n)-F p.1 p.2))
  · intro n
    exact measurable_const.mul ((hm.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hm)
  · apply tendsto_pi_nhds.mpr
    intro p
    simpa only [Function.comp_def,smul_eq_mul] using (hd p.1 p.2).hasDerivAt.tendsto_slope_zero.comp ht

lemma measurable_varianceHeat_family {F : ℝ → ℝ → ℝ} {V : ℝ → ℝ}
    (hm : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) (hV : Measurable V) :
    Measurable (fun p : ℝ × ℝ => varianceHeat (V p.1) (F p.1) p.2) := by
  have hj : Measurable (fun q : (ℝ × ℝ) × ℝ => F q.1.1 (q.1.2+Real.sqrt (V q.1.1)*q.2)) :=
    hm.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).add (((hV.comp (measurable_fst.comp measurable_fst)).sqrt).mul measurable_snd)))
  exact hj.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_backward {f : ℝ → ℝ} (hf : Measurable f) (c b : ℝ) :
    Measurable (fun p : ℝ × ℝ => backward c b f p.1 p.2) := by
  unfold backward varianceLogHeat
  split_ifs with hc
  · exact measurable_varianceHeat_family (F := fun _ z => f z) (hf.comp measurable_snd) (measurable_const.sub measurable_id)
  · exact (measurable_varianceHeat_family (F := fun _ z => Real.exp (c*f z))
      ((measurable_const.mul (hf.comp measurable_snd)).exp) (measurable_const.sub measurable_id)).log.div_const c

lemma varianceHeat_abs_le {g : ℝ → ℝ} {A : ℝ} (hA : ∀ z, |g z| ≤ A) (t x : ℝ) :
    |varianceHeat t g x| ≤ A := by
  have hnn : 0 ≤ A := (abs_nonneg (g 0)).trans (hA 0)
  change ‖∫ y, g (x+Real.sqrt t*y) ∂gaussianReal 0 1‖ ≤ A
  have hh := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (f := fun y => g (x+Real.sqrt t*y)) (C := A)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hA (x+Real.sqrt t*y)))
  simpa using hh

lemma hasDerivAt_integral_varianceHeat {F : ℝ → ℝ → ℝ} {A B : ℝ≥0}
    (hm : Measurable (fun p : ℝ × ℝ => F p.1 p.2))
    (hf : ∀ r, BoundedSmooth (F r)) (hA : ∀ r z, |F r z| ≤ A)
    (hB : ∀ r z, |deriv (F r) z| ≤ B) (a b x : ℝ) :
    HasDerivAt (fun z => ∫ r in a..b, varianceHeat (r-a) (F r) z)
      (∫ r in a..b, varianceHeat (r-a) (deriv (F r)) x) x := by
  have hm' := measurable_spatial_deriv hm (fun r => (hf r).smooth.differentiable (by simp))
  have hH := measurable_varianceHeat_family hm (measurable_id.sub_const a)
  have hH' := measurable_varianceHeat_family (F := fun r => deriv (F r)) hm' (measurable_id.sub_const a)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z r => varianceHeat (r-a) (F r) z)
    (F' := fun z r => varianceHeat (r-a) (deriv (F r)) z)
    (bound := fun _ => (B:ℝ)) (s := Set.univ) (Filter.univ_mem)
    (Eventually.of_forall (fun z => (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    ?_ ((hH'.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
    (intervalIntegrable_const) ?_).2
  · apply (intervalIntegrable_const (c := (A:ℝ))).mono_fun
      (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    filter_upwards [] with r
    simpa only [Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg A.coe_nonneg] using varianceHeat_abs_le (hA r) (r-a) x
  · filter_upwards [] with r hr z hz
    simpa only [Real.norm_eq_abs] using varianceHeat_abs_le (hB r) (r-a) z
  · filter_upwards [] with r hr z hz
    exact hasDerivAt_scaled_space ((hf r).smooth.of_le (by simp))
      (ExponentialBound.of_bounded (hA r)) (ExponentialBound.of_bounded (hB r)) (Real.sqrt (r-a)) z

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.FiniteValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma continuousOn_moving_heat_from {F : ℝ → ℝ → ℝ} {L : ℝ≥0} {p l u : ℝ}
    (hpl : p ≤ l) (hlu : l ≤ u) (hm : ∀ r, Measurable (F r))
    (hL : ∀ r ∈ Icc l u, ∀ s ∈ Icc l u, ∀ z y,
      |F r z-F s y| ≤ (L:ℝ)*(|r-s|+|z-y|)) (x : ℝ) :
    ContinuousOn (fun r => varianceHeat (r-p) (F r) x) (Icc l u) := by
  apply continuousOn_of_dominated
    (bound := fun y : ℝ => |F l x|+(L:ℝ)*((u-l)+Real.sqrt (u-p)*|y|))
  · intro r hr
    exact ((hm r).comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
  · intro r hr
    filter_upwards [] with y
    have hh := hL r hr l ⟨le_rfl,hlu⟩ (x+Real.sqrt (r-p)*y) x
    have htri := abs_add_le (F r (x+Real.sqrt (r-p)*y)-F l x) (F l x)
    rw [sub_add_cancel] at htri
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (sub_nonneg.mpr hr.1)] at hh
    have hs : Real.sqrt (r-p) ≤ Real.sqrt (u-p) :=
      (Real.sqrt_le_sqrt_iff (sub_nonneg.mpr (hpl.trans hlu))).mpr (sub_le_sub_right hr.2 p)
    rw [Real.norm_eq_abs]
    change |F r (x+Real.sqrt (r-p)*y)| ≤ _
    have hmul := mul_le_mul_of_nonneg_right hs (abs_nonneg y)
    have hhi := mul_le_mul_of_nonneg_left (add_le_add (show r-l ≤ u-l by linarith [hr.2]) hmul) L.coe_nonneg
    linarith
  · exact (integrable_const _).add
      (((integrable_const _).add (integrable_standardGaussian_abs.const_mul _)).const_mul _)
  · filter_upwards [] with y
    exact (continuousOn_of_joint_bound hL).comp
      ((continuous_id.prodMk (continuous_const.add ((Real.continuous_sqrt.comp
        (continuous_id.sub continuous_const)).mul continuous_const))).continuousOn)
      (fun r hr => ⟨hr,Set.mem_univ _⟩)

lemma backward_heat_dual {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) {p l u b : ℝ}
    (hl : 0 ≤ l) (hpl : p ≤ l) (hlu : l ≤ u) (hub : u ≤ b) (x : ℝ) :
    varianceHeat (u-p) (backward c b f u) x =
      varianceHeat (l-p) (backward c b f l) x-
        (c/2)*(∫ r in l..u, varianceHeat (r-p) (fun z => (deriv (backward c b f r) z)^2) x) := by
  obtain ⟨L,hL⟩ := backward_joint_bound hf hLip hc b
  obtain ⟨J,hJ⟩ := backward_gradient_sq_joint_bound hf hLip hc b
  have hinc : Icc l u ⊆ Icc 0 b := fun r hr => ⟨hl.trans hr.1,hr.2.trans hub⟩
  have hcont : ContinuousOn (fun r => varianceHeat (r-p) (backward c b f r) x) (Icc l u) :=
    continuousOn_moving_heat_from hpl hlu
      (fun r => (regularDatum_varianceLogHeat hf hLip hc (b-r)).smooth.continuous.measurable)
      (fun r hr s hs => hL r (hinc hr) s (hinc hs)) x
  have hscont := continuousOn_moving_heat_from hpl hlu
      (fun r => (regularDatum_varianceLogHeat hf hLip hc (b-r)).deriv_bounded.smooth.continuous.measurable.pow_const 2)
      (fun r hr s hs => hJ r (hinc hr) s (hinc hs)) x
  have hint : IntervalIntegrable (fun r => -(c/2)*varianceHeat (r-p)
      (fun z => (deriv (backward c b f r) z)^2) x) volume l u :=
    (hscont.const_mul (-(c/2))).intervalIntegrable_of_Icc hlu
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlu hcont
    (fun r hr => hasDerivAt_moving_backward_heat hf hLip hc (hpl.trans_lt hr.1) (hr.2.trans_le hub) x) hint
  rw [intervalIntegral.integral_const_mul] at he
  linarith

def finiteValue (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, _, _, x => f x
  | N+1, i, t, x => if t ≤ h then
      backward (c i) h (cascade c h f N (i+1)) t x
    else finiteValue c h f N (i+1) (t-h) x

def finiteCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | N+1, i, t => if t ≤ h then c i else finiteCoeff c h N (i+1) (t-h)

lemma finiteValue_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    RegularDatum (finiteValue c h f N i t) := by
  induction N generalizing i t with
  | zero => exact hf
  | succ N ih =>
    by_cases ht : t ≤ h
    · have he : finiteValue c h f (N+1) i t = backward (c i) h (cascade c h f N (i+1)) t := by
        funext x; simp only [finiteValue,ite_eq_left ht]
      rw [he]
      exact regularDatum_varianceLogHeat (cascade_regular hf hLip c h N (i+1))
        (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg (h-t)
    · have he : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
        funext x; simp only [finiteValue,ite_eq_right ht]
      rw [he]
      exact ih (i+1) (t-h)

lemma finiteValue_lipschitz {f : ℝ → ℝ} (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    LipschitzWith 1 (finiteValue c h f N i t) := by
  induction N generalizing i t with
  | zero => exact hLip
  | succ N ih =>
    by_cases ht : t ≤ h
    · have he : finiteValue c h f (N+1) i t = varianceLogHeat (c i) (h-t) (cascade c h f N (i+1)) := by
        funext x; simp only [finiteValue,ite_eq_left ht,backward]
      rw [he]
      exact varianceLogHeat_lipschitz (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg _
    · have he : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
        funext x; simp only [finiteValue,ite_eq_right ht]
      rw [he]
      exact ih (i+1) (t-h)

lemma finiteValue_head (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : t ≤ h) : finiteValue c h f (N+1) i t = backward (c i) h (cascade c h f N (i+1)) t := by
  funext x; simp only [finiteValue,ite_eq_left ht]

lemma finiteValue_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) < t) : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
  funext x; simp only [finiteValue,ite_eq_right (not_le.mpr ht)]

lemma finiteValue_zero {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : finiteValue c h f N i 0 = cascade c h f N i := by
  cases N with
  | zero => rfl
  | succ N =>
    rw [finiteValue_head f c h N i h.coe_nonneg]
    funext x
    simp only [backward,sub_zero,cascade]
    exact varianceLogHeat_eq_logSemigroup (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable (c i) h x

lemma measurable_finiteValue {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (fun p : ℝ × ℝ => finiteValue c h f N i p.1 p.2) := by
  induction N generalizing i with
  | zero => exact hf.smooth.continuous.measurable.comp measurable_snd
  | succ N ih =>
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
      (measurable_backward (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable (c i) h)
      ((ih (i+1)).comp ((measurable_fst.sub_const (h:ℝ)).prodMk measurable_snd))

lemma measurable_finiteCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (finiteCoeff c h N i) := by
  induction N generalizing i with
  | zero => exact measurable_const
  | succ N ih =>
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const ((ih (i+1)).comp (measurable_id.sub_const (h:ℝ)))

lemma finiteCoeff_bounds (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t, 0 ≤ finiteCoeff c h N i t ∧ finiteCoeff c h N i t ≤ C := by
  induction N generalizing i with
  | zero => exact ⟨0,fun _ => ⟨le_rfl,le_rfl⟩⟩
  | succ N ih =>
    obtain ⟨C,hC⟩ := ih (i+1)
    refine ⟨c i+C,fun t => ?_⟩
    dsimp only [finiteCoeff]
    split_ifs with ht
    · constructor
      · exact (c i).coe_nonneg
      · simp only [NNReal.coe_add]; linarith [C.coe_nonneg]
    · constructor
      · exact (hC (t-h)).1
      · simp only [NNReal.coe_add]; linarith [(hC (t-h)).2,(c i).coe_nonneg]

lemma finiteValue_uniform_derivative_bounds {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i n : ℕ) :
    ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv (n+1) (finiteValue c h f N i t) x| ≤ C := by
  induction N generalizing i with
  | zero =>
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bounds n
    exact ⟨C,fun _ x => by simpa only [finiteValue,iteratedDeriv_succ'] using hC x⟩
  | succ N ih =>
    obtain ⟨C,hC⟩ := uniform_varianceLogHeat_derivative_bounds
      (cascade_regular hf hLip c h N (i+1)) (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg n
    obtain ⟨D,hD⟩ := ih (i+1)
    refine ⟨C+D,fun t x => ?_⟩
    by_cases ht : t ≤ h
    · rw [finiteValue_head f c h N i ht]
      rw [show backward (c i) h (cascade c h f N (i+1)) t =
        varianceLogHeat (c i) (h-t) (cascade c h f N (i+1)) from rfl]
      exact (hC (h-t) x).trans (by simp only [NNReal.coe_add]; linarith [D.coe_nonneg])
    · rw [finiteValue_tail f c h N i (lt_of_not_ge ht)]
      exact (hD (t-h) x).trans (by simp only [NNReal.coe_add]; linarith [C.coe_nonneg])

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.GridBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def remainingLengths (h : ℝ≥0) (t : ℝ) (j : ℕ) : ℝ≥0 :=
  Real.toNNReal (min (h:ℝ) (((j+1:ℕ):ℝ)*h-t))

lemma remainingLengths_shift (h : ℝ≥0) (t : ℝ) (j : ℕ) :
    remainingLengths h t (j+1) = remainingLengths h (t-h) j := by
  unfold remainingLengths
  congr 2
  push_cast
  ring

lemma remainingLengths_nonpos (h : ℝ≥0) {t : ℝ} (ht : t ≤ 0) (j : ℕ) :
    remainingLengths h t j = h := by
  have hh : (h:ℝ) ≤ ((j+1:ℕ):ℝ)*h-t := by
    push_cast
    nlinarith [h.coe_nonneg, mul_nonneg (Nat.cast_nonneg (α := ℝ) j) h.coe_nonneg]
  unfold remainingLengths
  rw [min_eq_left hh]
  exact Real.toNNReal_coe

lemma remainingLengths_head (h : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    remainingLengths h t 0 = Real.toNNReal ((h:ℝ)-t) := by
  simp only [remainingLengths,Nat.zero_add,Nat.cast_one,one_mul]
  rw [min_eq_right (by linarith)]

lemma remainingLengths_time (h : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Nonuniform.time (remainingLengths h t) n = Real.toNNReal ((n:ℝ)*h-t) := by
  induction n with
  | zero => simp only [Nonuniform.time_zero,Nat.cast_zero,zero_mul,zero_sub]
            rw [Real.toNNReal_of_nonpos (by linarith)]
  | succ n ih =>
    rw [Nonuniform.time_succ,ih]
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,remainingLengths,Real.coe_toNNReal']
    push_cast
    have hn := h.coe_nonneg
    by_cases hc : (n:ℝ)*h ≤ t
    · rw [max_eq_right (by linarith)]
      have hm : ((n:ℝ)+1)*h-t ≤ h := by nlinarith
      rw [min_eq_right hm,zero_add]
    · have hp : 0 ≤ (n:ℝ)*h-t := by linarith
      rw [max_eq_left hp,min_eq_left (by nlinarith),max_eq_left hn,
        max_eq_left (by nlinarith)]
      ring

lemma cascadeV_shift (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (n k j : ℕ) :
    cascadeV (fun l => h (k+l)) (fun l => c (k+l)) f n j = cascadeV h c f n (k+j) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cascadeV,ih]
    rw [Nat.add_assoc]

lemma cascadeV_uniform (h : ℝ≥0) (c : ℕ → ℝ≥0) (f : ℝ → ℝ) (n k : ℕ) :
    cascadeV (fun _ => h) c f n k = cascade c h f n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [cascadeV,cascade,ih]

lemma finiteValue_eq_remaining {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (n i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    finiteValue c h f n i t = cascadeV (remainingLengths h t) (fun j => c (i+j)) f n 0 := by
  induction n generalizing i t with
  | zero => rfl
  | succ n ih =>
    have hs : cascadeV (remainingLengths h t) (fun j => c (i+j)) f n 1 =
        cascadeV (remainingLengths h (t-h)) (fun j => c ((i+1)+j)) f n 0 := by
      have he := cascadeV_shift (remainingLengths h t) (fun j => c (i+j)) f n 1 0
      simp only [Nat.add_zero] at he
      rw [← he]
      congr 2
      · funext j
        rw [Nat.add_comm 1 j,remainingLengths_shift]
      · funext j
        congr 1
        omega
    by_cases hth : t ≤ h
    · rw [finiteValue_head f c h n i hth]
      have hl : remainingLengths h (t-h) = fun _ => h := by
        funext j
        exact remainingLengths_nonpos h (sub_nonpos.mpr hth) j
      funext x
      simp only [cascadeV,Nat.add_zero]
      rw [hs,hl,cascadeV_uniform]
      have hc := cascadeV_shift (fun _ => h) c f n (i+1) 0
      simp only [Nat.add_zero,cascadeV_uniform] at hc
      rw [hc]
      rw [remainingLengths_head h ht]
      exact varianceLogHeat_eq_logSemigroup_toNNReal
        (cascade_regular hf hLip c h n (i+1)).smooth.continuous.measurable (c i) (h-t) x
    · rw [finiteValue_tail f c h n i (lt_of_not_ge hth),ih (i+1) (by linarith)]
      funext x
      simp only [cascadeV,Nat.add_zero]
      rw [hs,remainingLengths_head h ht,Real.toNNReal_of_nonpos (by linarith)]
      simp only [logSemigroup,semigroup,gaussianReal_zero_var,integral_dirac,add_zero]
      split_ifs with hc
      · rfl
      · rw [Real.log_exp,mul_div_cancel_left₀ _ (by exact_mod_cast hc)]

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def gridError (h c : ℕ → ℝ≥0) (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ∫ r in (time h k:ℝ)..(time h (k+1):ℝ), |(c k:ℝ)-g r|

lemma grid_integral_error (h c : ℕ → ℝ≥0) {g a : ℝ → ℝ}
    (hg : Integrable g) (ha : Measurable a) (hab : ∀ r, |a r| ≤ 1) (N : ℕ) :
    |(∑ k ∈ Finset.range N, ∫ r in (time h k:ℝ)..(time h (k+1):ℝ), (c k:ℝ)*a r) -
      ∫ r in (0:ℝ)..(time h N:ℝ), g r*a r| ≤ gridError h c g N := by
  have hga : Integrable (fun r => g r*a r) := hg.mul_bdd ha.aestronglyMeasurable
    (Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hab))
  have haI (k : ℕ) : IntervalIntegrable a volume (time h k:ℝ) (time h (k+1):ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast time_mono h (Nat.le_succ k))]
    exact Integrable.of_bound ha.aestronglyMeasurable 1
      (Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hab))
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => (time h k:ℝ)) (n := N) (fun k _ => hga.intervalIntegrable)
  simp only [time_zero,NNReal.coe_zero] at hs
  rw [← hs,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [← intervalIntegral.integral_sub ((haI k).const_mul _) hga.intervalIntegrable]
  have hc : IntervalIntegrable (fun r => |(c k:ℝ)-g r|) volume (time h k:ℝ) (time h (k+1):ℝ) :=
    (intervalIntegrable_const.sub hg.intervalIntegrable).abs
  change ‖∫ r in (time h k:ℝ)..(time h (k+1):ℝ), (c k:ℝ)*a r-g r*a r‖ ≤ _
  apply intervalIntegral.norm_integral_le_of_norm_le
    (by exact_mod_cast time_mono h (Nat.le_succ k)) _ hc
  filter_upwards [] with r hr
  rw [← sub_mul,Real.norm_eq_abs,abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hab r) (abs_nonneg ((c k:ℝ)-g r))

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Control.elapsed_integral (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (α : Control W (Real.toNNReal t)) (ξ : Ω) (p : ℕ) :
    (∫ r in (0:ℝ)..(1-t), extend γ.val (t+r)*(α.val (Real.toNNReal r) ξ)^p) =
      ∫ s in t..1, extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^p := by
  have he := intervalIntegral.integral_comp_add_left
    (fun s => extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^p) t (a := 0) (b := 1-t)
  simpa only [add_sub_cancel_left,add_zero,add_sub_cancel] using he

lemma profit_eq_integral {B α : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsPreBrownianReal B P)
    (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hab : ∀ t ξ, |α t ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (x : ℝ) (N : ℕ) :
    profit (P := P) B α h c f x N = ∫ ξ, f (controlled B α h c x N ξ)-
      ∑ k ∈ Finset.range N, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hi := controlled_integrable hB ham hab h c x N
  have hfI : Integrable (fun ξ => f (controlled B α h c x N ξ)) P := by
    apply ((integrable_const |f 0|).add hi.norm).mono'
      (hf.continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable)
    filter_upwards [] with ξ
    have hh := hf.dist_le_mul (controlled B α h c x N ξ) 0
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_zero] at hh
    change |f (controlled B α h c x N ξ)| ≤ |f 0|+|controlled B α h c x N ξ|
    have htri := abs_sub_le (f (controlled B α h c x N ξ)) (f 0) 0
    simp only [sub_zero] at htri
    linarith
  have hiC (k : ℕ) : Integrable (stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k)) P :=
    stepCost_integrable (ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd))
      (fun r ξ => hab _ ξ) _ _ _ (h k).coe_nonneg (c k).coe_nonneg
  rw [integral_sub hfI (integrable_finsetSum (Finset.range N) (fun k _ => hiC k)),integral_finsetSum _ (fun k _ => hiC k)]
  rfl

lemma control_profit_error (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (α : Control W (Real.toNNReal t))
    (h c : ℕ → ℝ≥0) (N : ℕ) (hH : (time h N:ℝ) = 1-t)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) {ε : ℝ} (he : ∀ z, |f z - abs z| ≤ ε) :
    |profit (P := W.law) (fun s ξ => W.B (Real.toNNReal t+s) ξ-W.B (Real.toNNReal t) ξ)
      α.val h c f x N - ∫ ξ, controlPayoff W γ t x α ξ ∂W.law| ≤
      ε+(3/2:ℝ)*gridError h c (fun r => extend γ.val (t+r)) N := by
  let := W.isProbability
  let B := fun s ξ => W.B (Real.toNNReal t+s) ξ-W.B (Real.toNNReal t) ξ
  have hB : IsPreBrownianReal B W.law := W.brownian.toIsPreBrownianReal.shift _
  have hpred : Real.toNNReal t+time h N = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,Real.coe_toNNReal _ ht0,hH,NNReal.coe_one]
    ring
  have hg : Integrable (fun r => extend γ.val (t+r)) := γ.integrable.comp_add_left t
  have ham : Measurable (fun p : ℝ × Ω => α.val (Real.toNNReal p.1) p.2) :=
    α.measurable.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  let E := gridError h c (fun r => extend γ.val (t+r)) N
  have hpath (ξ : Ω) :
      |(f (controlled B α.val h c x N ξ)-∑ k ∈ Finset.range N,
        stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)-
        controlPayoff W γ t x α ξ| ≤ ε+(3/2:ℝ)*E := by
    have hamξ : Measurable (fun r => α.val (Real.toNNReal r) ξ) := ham.comp measurable_prodMk_right
    have hd := grid_integral_error h c hg hamξ
      (fun r => α.bound _ ξ) N
    have hc := grid_integral_error h c hg (hamξ.pow_const 2)
      (fun r => by simpa only [abs_pow,one_pow] using
        pow_le_pow_left₀ (abs_nonneg (α.val (Real.toNNReal r) ξ)) (α.bound _ ξ) 2) N
    rw [hH,Control.elapsed_integral W γ t α ξ 2] at hc
    have hdp := Control.elapsed_integral W γ t α ξ 1
    simp only [pow_one] at hdp
    rw [hH,hdp] at hd
    have hstate : |controlled B α.val h c x N ξ-
        (x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
          ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ)| ≤ E := by
      rw [controlled_formula]
      simp only [B,hpred,add_zero,sub_self,sub_zero,stepDrift,← coe_time_succ]
      convert hd using 1 <;> try rfl
      simp only [sub_eq_add_neg,add_assoc]
      congr 1
      ring
    have hferr := (abs_sub_le (f (controlled B α.val h c x N ξ))
      |controlled B α.val h c x N ξ|
      |x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
        ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ|).trans
        (add_le_add (he _) ((abs_abs_sub_abs_le_abs_sub _ _).trans hstate))
    have hcost : |(∑ k ∈ Finset.range N, stepCost (fun r => α.val (Real.toNNReal r))
        (time h k) (h k) (c k) ξ)-(1/2:ℝ)*∫ s in t..1,
          extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^2| ≤ (1/2:ℝ)*E := by
      simp only [stepCost,← coe_time_succ,← Finset.mul_sum,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      exact mul_le_mul_of_nonneg_left hc (by norm_num)
    unfold controlPayoff
    have hp := abs_sub_le (f (controlled B α.val h c x N ξ)-∑ k ∈ Finset.range N,
      stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)
      (|x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
        ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ|-
        ∑ k ∈ Finset.range N, stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)
      (|x+W.B 1 ξ-W.B (Real.toNNReal t) ξ+
        ∫ s in t..1, extend γ.val s*α.val (Real.toNNReal (s-t)) ξ|-
        (1/2:ℝ)*∫ s in t..1, extend γ.val s*(α.val (Real.toNNReal (s-t)) ξ)^2)
    simp only [sub_sub_sub_cancel_right,sub_sub_sub_cancel_left,abs_sub_comm] at hp
    linarith
  rw [profit_eq_integral hB α.measurable α.bound h c hf x N]
  have hi := controlled_integrable hB α.measurable α.bound h c x N
  have hfI : Integrable (fun ξ => f (controlled B α.val h c x N ξ)) W.law := by
    apply ((integrable_const (|f 0|)).add hi.norm).mono'
      (hf.continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable)
    filter_upwards [] with ξ
    have hh := hf.dist_le_mul (controlled B α.val h c x N ξ) 0
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_zero] at hh
    change |f (controlled B α.val h c x N ξ)| ≤ |f 0|+|controlled B α.val h c x N ξ|
    have htri := abs_sub_le (f (controlled B α.val h c x N ξ)) (f 0) 0
    simp only [sub_zero] at htri
    linarith
  have hiC (k : ℕ) : Integrable (stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k)) W.law :=
    stepCost_integrable ham (fun r ξ => α.bound _ ξ) _ _ _ (h k).coe_nonneg (c k).coe_nonneg
  have hdiff := integral_sub (hfI.sub (integrable_finsetSum (Finset.range N) (fun k _ => hiC k)))
    (controlPayoff_integrable W γ t x ht1 α)
  simp only [Pi.sub_apply] at hdiff
  rw [← hdiff]
  have hn := norm_integral_le_of_norm_le_const (μ := W.law)
    (f := fun ξ => (f (controlled B α.val h c x N ξ)-∑ k ∈ Finset.range N,
      stepCost (fun r => α.val (Real.toNNReal r)) (time h k) (h k) (c k) ξ)-
      controlPayoff W γ t x α ξ)
    (Eventually.of_forall (fun ξ => by simpa only [Real.norm_eq_abs] using hpath ξ))
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using hn

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.GridApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

lemma finiteCoeff_cell (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i k : ℕ) (hk : k < N)
    {r : ℝ} (hr0 : 0 < r) (hrh : r ≤ h) :
    finiteCoeff c h N i ((k:ℝ)*h+r) = c (i+k) := by
  induction N generalizing i k with
  | zero => omega
  | succ N ih =>
    cases k with
    | zero => simp only [Nat.cast_zero,zero_mul,zero_add,finiteCoeff,ite_eq_left hrh,Nat.add_zero]
    | succ k =>
      have hgt : (h:ℝ) < ((k+1:ℕ):ℝ)*h+r := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) h.coe_nonneg]
      simp only [finiteCoeff,ite_eq_right (not_le.mpr hgt)]
      have he : ((k+1:ℕ):ℝ)*h+r-h = (k:ℝ)*h+r := by push_cast; ring
      rw [he,ih (i+1) k (by omega), show i+1+k = i+(k+1) by omega]

lemma finiteCoeff_intervalIntegrable (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (a b : ℝ) :
    IntervalIntegrable (finiteCoeff c h N i) volume a b := by
  obtain ⟨C,hC⟩ := finiteCoeff_bounds c h N i
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun'
    (measurable_finiteCoeff c h N i).aestronglyMeasurable
  filter_upwards [] with r
  rw [Real.norm_eq_abs,abs_of_nonneg (hC r).1]
  exact (hC r).2

lemma finiteCoeff_remaining_cell (c : ℕ → ℝ≥0) (h : ℝ≥0) (N k : ℕ) (hk : k < N)
    {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Ioo (time (remainingLengths h t) k:ℝ)
      (time (remainingLengths h t) (k+1):ℝ)) :
    finiteCoeff c h N 0 (t+r) = c k := by
  rw [remainingLengths_time h ht,remainingLengths_time h ht] at hr
  simp only [Real.coe_toNNReal',Set.mem_Ioo] at hr
  obtain ⟨hrlo,hrhi⟩ := hr
  have hkr : (k:ℝ)*h < t+r := by linarith [hrlo,le_max_left ((k:ℝ)*h-t) 0]
  have hrpos : 0 < r := (le_max_right ((k:ℝ)*h-t) 0).trans_lt hrlo
  have htkr : 0 < ((k+1:ℕ):ℝ)*h-t := by
    by_contra hn
    rw [max_eq_right (le_of_not_gt hn)] at hrhi
    linarith
  have hrr : t+r ≤ ((k+1:ℕ):ℝ)*h := by
    rw [max_eq_left htkr.le] at hrhi
    linarith
  have hloc : t+r-(k:ℝ)*h ≤ h := by push_cast at hrr; nlinarith
  have he := finiteCoeff_cell c h N 0 k hk (sub_pos.mpr hkr) hloc
  simp only [Nat.zero_add] at he
  simpa only [add_sub_cancel] using he

lemma finiteCoeff_sample (c : ℕ → ℝ≥0) {h : ℝ≥0} (_hh : 0 < h) (N i : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ (N:ℝ)*h) (hN : 0 < N) :
    ∃ j < N, finiteCoeff c h N i t = c (i+j) ∧
      (j:ℝ)*h ≤ t ∧ t ≤ (j+1:ℕ)*h := by
  induction N generalizing i t with
  | zero => omega
  | succ N ih =>
    by_cases hth : t ≤ h
    · refine ⟨0,by omega,?_,?_,?_⟩
      · simp only [finiteCoeff,ite_eq_left hth,Nat.add_zero]
      · simpa using ht0
      · simpa using hth
    · have hNp : 0 < N := by
        by_contra hn
        have : N = 0 := by omega
        subst N
        norm_num at htN
        exact hth htN
      have htt : t-h ≤ (N:ℝ)*h := by push_cast at htN; nlinarith
      obtain ⟨j,hj,he,hl,hu⟩ := ih (i+1) (by linarith) htt hNp
      refine ⟨j+1,by omega,?_,?_,?_⟩
      · simp only [finiteCoeff,ite_eq_right hth,he]
        rw [show i+1+j = i+(j+1) by omega]
      · push_cast
        linarith
      · push_cast at hu ⊢
        nlinarith

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

lemma gridError_remaining (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) (hN : (N:ℝ)*h = 1)
    (γ : OrderParameter) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gridError (remainingLengths h t) c (fun r => extend γ.val (t+r)) N =
      ∫ s in t..1, |finiteCoeff c h N 0 s-extend γ.val s| := by
  let d := remainingLengths h t
  let g := fun r => |finiteCoeff c h N 0 (t+r)-extend γ.val (t+r)|
  have hH : (time d N:ℝ) = 1-t := by
    rw [remainingLengths_time h ht0,hN,Real.coe_toNNReal _ (by linarith)]
  have hg (a b : ℝ) : IntervalIntegrable g volume a b := by
    have hh := ((finiteCoeff_intervalIntegrable c h N 0 (t+a) (t+b)).sub
      γ.integrable.intervalIntegrable).abs.comp_add_left t
    simpa only [add_sub_cancel_left] using hh
  have he : gridError d c (fun r => extend γ.val (t+r)) N =
      ∑ k ∈ Finset.range N, ∫ r in (time d k:ℝ)..(time d (k+1):ℝ), g r := by
    apply Finset.sum_congr rfl
    intro k hk
    apply intervalIntegral.integral_congr_Ioo_of_le
      (by exact_mod_cast time_mono d (Nat.le_succ k))
    intro r hr
    dsimp only [g]
    rw [finiteCoeff_remaining_cell c h N k (Finset.mem_range.mp hk) ht0 hr]
  rw [he,intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hg _ _),time_zero,NNReal.coe_zero,hH]
  have hs := intervalIntegral.integral_comp_add_left
    (fun s => |finiteCoeff c h N 0 s-extend γ.val s|) t (a := 0) (b := 1-t)
  simpa only [add_zero,add_sub_cancel] using hs

lemma gridError_remaining_le (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) (hN : (N:ℝ)*h = 1)
    (γ : OrderParameter) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gridError (remainingLengths h t) c (fun r => extend γ.val (t+r)) N ≤
      ∫ s in (0:ℝ)..1, |finiteCoeff c h N 0 s-extend γ.val s| := by
  rw [gridError_remaining c h N hN γ ht0 ht1]
  exact intervalIntegral.integral_mono_interval ht0 ht1 le_rfl
    (Eventually.of_forall (fun s => abs_nonneg _))
    (((finiteCoeff_intervalIntegrable c h N 0 0 1).sub γ.integrable.intervalIntegrable).abs)

variable {Ω : Type*} [MeasurableSpace Ω]

lemma cascadeV_value_error (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h c : ℕ → ℝ≥0) (N : ℕ)
    (hH : (time h N:ℝ) = 1-t) {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {ε : ℝ} (he : ∀ z, |f z-abs z| ≤ ε) :
    |cascadeV h c f N 0 x-value W γ t x| ≤
      ε+(3/2:ℝ)*gridError h c (fun r => extend γ.val (t+r)) N := by
  let B := fun s ξ => W.B (Real.toNNReal t+s) ξ-W.B (Real.toNNReal t) ξ
  have hB : IsPreBrownianReal B W.law := W.brownian.toIsPreBrownianReal.shift _
  have hm (s : ℝ≥0) : Measurable (B s) := (W.measurable _).sub (W.measurable _)
  let E := ε+(3/2:ℝ)*gridError h c (fun r => extend γ.val (t+r)) N
  have hobj : ∀ v ∈ objectives (P := W.law) hm h c f x N, v ≤ value W γ t x+E := by
    intro v hv
    obtain ⟨a,hap,hab,rfl⟩ := hv
    let α : Control W (Real.toNNReal t) := ⟨a,hap,hab⟩
    have hh := control_profit_error W γ t x ht0 ht1 α h c N hH hLip he
    have hp := expected_controlPayoff_le_value W γ t x ht1 α
    have := (abs_le.mp hh).2
    change profit (P := W.law) B a h c f x N -
      (∫ ξ, controlPayoff W γ t x α ξ ∂W.law) ≤ E at this
    linarith
  have hb : BddAbove (objectives (P := W.law) hm h c f x N) := ⟨_,hobj⟩
  have hc := cascadeV_eq_control_sup hB hm hf hLip h c N x
  have hu : cascadeV h c f N 0 x ≤ value W γ t x+E := by
    rw [hc]
    exact csSup_le (objectives_nonempty hm h c f x N) hobj
  change |cascadeV h c f N 0 x-value W γ t x| ≤ E
  apply abs_sub_le_iff.mpr
  refine ⟨by linarith,?_⟩
  have hl : value W γ t x ≤ cascadeV h c f N 0 x+E := by
    unfold value
    refine csSup_le ⟨_,⟨zeroControl W (Real.toNNReal t),rfl⟩⟩ ?_
    rintro y ⟨α,rfl⟩
    have hh := control_profit_error W γ t x ht0 ht1 α h c N hH hLip he
    have hmem : profit (P := W.law) B α.val h c f x N ∈ objectives (P := W.law) hm h c f x N :=
      ⟨α.val,α.progressive,α.bound,rfl⟩
    have hp := le_csSup hb hmem
    rw [← hc] at hp
    have hh' := (abs_le.mp hh).1
    change -E ≤ profit (P := W.law) B α.val h c f x N -
      (∫ ξ, controlPayoff W γ t x α ξ ∂W.law) at hh'
    linarith
  linarith

theorem finiteValue_control_error (W : BrownianSystem Ω) (γ : OrderParameter)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) (hN : (N:ℝ)*h = 1)
    {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    {ε : ℝ} (he : ∀ z, |f z-abs z| ≤ ε) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |finiteValue c h f N 0 t x-value W γ t x| ≤
      ε+(3/2:ℝ)*∫ s in (0:ℝ)..1, |finiteCoeff c h N 0 s-extend γ.val s| := by
  rw [finiteValue_eq_remaining hf hLip c h N 0 ht0]
  simp only [Nat.zero_add]
  have hH : (time (remainingLengths h t) N:ℝ) = 1-t := by
    rw [remainingLengths_time h ht0,hN,Real.coe_toNNReal _ (by linarith)]
  exact (cascadeV_value_error W γ t x ht0 ht1 (remainingLengths h t) c N hH hf hLip he).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (gridError_remaining_le c h N hN γ ht0 ht1)
      (by norm_num : (0:ℝ) ≤ 3/2)))

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Taylor1Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma taylor1_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {C : ℝ}
    (hC : ∀ x, |deriv (deriv f) x| ≤ C) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d| ≤ C/2*|d|^2 := by
  by_cases hd : d = 0
  · simp [hd]
  have hxd : x ≠ x+d := by intro h; apply hd; linarith
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxd hf.contDiffOn
  have h1 : iteratedDerivWithin 1 f (Set.uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxd)
      (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc, iteratedDeriv_one]
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, h1,
    iteratedDeriv_succ] at he
  norm_num at he
  have he' : f (x+d)-f x-deriv f x*d = deriv (deriv f) y*d^2/2 := by
    calc
      _ = f (x+d)-(f x+d*deriv f x) := by ring
      _ = _ := by convert he using 1
  rw [he', abs_div, abs_mul, abs_pow]
  norm_num
  have := mul_le_mul_of_nonneg_right (hC y) (sq_nonneg d)
  nlinarith

lemma derivative_interpolation {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {A C : ℝ} (hA : ∀ x, |f x| ≤ A) (hC : ∀ x, |deriv (deriv f) x| ≤ C)
    {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |deriv f x| ≤ 2*A/h+h*C/2 := by
  have ht := taylor1_bound hf hC x h
  rw [abs_of_pos hh] at ht
  have hs : |deriv f x*h| ≤ 2*A+C/2*h^2 := by
    calc
      _ = |f (x+h)-f x-(f (x+h)-f x-deriv f x*h)| := by congr 1; ring
      _ ≤ |f (x+h)-f x|+|f (x+h)-f x-deriv f x*h| := abs_sub _ _
      _ ≤ (|f (x+h)|+|f x|)+C/2*h^2 := add_le_add (abs_sub _ _) ht
      _ ≤ 2*A+C/2*h^2 := by linarith [hA (x+h),hA x]
  rw [abs_mul, abs_of_pos hh] at hs
  have he : (2*A/h+h*C/2)*h = 2*A+C/2*h^2 := by field_simp
  nlinarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.CoefficientApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def approxMesh (n : ℕ) : ℝ≥0 := ((n+1:ℕ):ℝ≥0)⁻¹

lemma approxMesh_pos (n : ℕ) : 0 < approxMesh n := by unfold approxMesh; positivity

lemma approxMesh_horizon (n : ℕ) : ((n+1:ℕ):ℝ)*approxMesh n = 1 := by
  simp only [approxMesh,NNReal.coe_inv,NNReal.coe_natCast]
  exact mul_inv_cancel₀ (by positivity)

lemma approxMesh_limit : Tendsto (fun n => (approxMesh n:ℝ)) atTop (𝓝 0) := by
  simpa only [approxMesh,NNReal.coe_inv,NNReal.coe_natCast,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma sample_mem (n j : ℕ) (hj : j < n+1) : (j:ℝ)*approxMesh n ∈ Ico (0:ℝ) 1 := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (approxMesh n).coe_nonneg,?_⟩
  rw [← approxMesh_horizon n]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hj) (by exact_mod_cast approxMesh_pos n)

def approxCoeff (γ : OrderParameter) (n j : ℕ) : ℝ≥0 :=
  if hj : j < n+1 then
    Real.toNNReal (γ.val ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩) else 0

def approxGamma (γ : OrderParameter) (n : ℕ) : ℝ → ℝ :=
  finiteCoeff (approxCoeff γ n) (approxMesh n) (n+1) 0

lemma approxCoeff_eq (γ : OrderParameter) (n j : ℕ) (hj : j < n+1) :
    (approxCoeff γ n j:ℝ) = γ.val ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩ := by
  unfold approxCoeff
  rw [dite_eq_left hj,Real.coe_toNNReal _ (γ.nonneg _)]

lemma approxGamma_samples (γ : OrderParameter) (n : ℕ) (t : Time) :
    ∃ (j : ℕ) (hj : j < n+1), approxGamma γ n t = γ.val ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩ ∧
      (j:ℝ)*approxMesh n ≤ t ∧ (t:ℝ) ≤ ((j+1:ℕ):ℝ)*approxMesh n := by
  obtain ⟨j,hj,he,hl,hu⟩ := finiteCoeff_sample (approxCoeff γ n) (approxMesh_pos n)
    (n+1) 0 t.property.1 (by rw [approxMesh_horizon]; exact t.property.2.le) (by omega)
  refine ⟨j,hj,?_,hl,hu⟩
  simpa only [approxGamma,Nat.zero_add,approxCoeff_eq γ n j hj] using he

lemma approxGamma_bounds (γ : OrderParameter) (n : ℕ) (t : Time) :
    0 ≤ approxGamma γ n t ∧ approxGamma γ n t ≤ γ.val t := by
  obtain ⟨j,hj,he,hl,hu⟩ := approxGamma_samples γ n t
  rw [he]
  exact ⟨γ.nonneg _,γ.monotone hl⟩

lemma approxGamma_tendsto (γ : OrderParameter) (t : Time) (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => approxGamma γ n t) atTop (𝓝 (γ.val t)) := by
  choose j hj he hl hu using fun n => approxGamma_samples γ n t
  let q (n : ℕ) : Time := ⟨(j n:ℝ)*approxMesh n,sample_mem n (j n) (hj n)⟩
  have hq : Tendsto (fun n => (q n:ℝ)) atTop (𝓝 (t:ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => (t:ℝ)-(approxMesh n:ℝ)) atTop (𝓝 (t:ℝ)) by
        simpa only [sub_zero] using tendsto_const_nhds.sub approxMesh_limit)
      tendsto_const_nhds
    · intro n
      have hh := hu n
      push_cast at hh
      dsimp only [q]
      nlinarith
    · exact hl
  have hqt : Tendsto q atTop (𝓝 t) := tendsto_subtype_rng.mpr hq
  have hh := ht.tendsto.comp hqt
  convert hh using 1 <;> try rfl
  funext n
  exact he n

lemma OrderParameter.ae_continuous (γ : OrderParameter) :
    ∀ᵐ s : ℝ, ∀ hs : s ∈ Ico (0:ℝ) 1, ContinuousAt γ.val ⟨s,hs⟩ := by
  have hc := γ.monotone.countable_not_continuousAt.image (fun t : Time => (t:ℝ))
  have hz := hc.measure_zero volume
  have ha : ∀ᵐ s : ℝ, s ∉ (fun t : Time => (t:ℝ)) '' {t | ¬ContinuousAt γ.val t} :=
    (ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hz))
  filter_upwards [ha] with s hs hmem
  by_contra hn
  exact hs ⟨⟨s,hmem⟩,hn,rfl⟩

lemma approxGamma_L1 (γ : OrderParameter) :
    Tendsto (fun n => ∫ s in (0:ℝ)..1, |approxGamma γ n s-extend γ.val s|)
      atTop (𝓝 0) := by
  have hint : ∀ n, AEStronglyMeasurable (fun s => |approxGamma γ n s-extend γ.val s|)
      (volume.restrict (Ioo (0:ℝ) 1)) := fun n =>
    ((measurable_finiteCoeff _ _ _ _).sub γ.measurable_extend).abs.aestronglyMeasurable
  have hb : ∀ n, ∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖|approxGamma γ n s-extend γ.val s|‖ ≤ extend γ.val s := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hm : s ∈ Ico (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
    have hh := approxGamma_bounds γ n ⟨s,hm⟩
    rw [Real.norm_eq_abs,abs_abs,show extend γ.val s = γ.val ⟨s,hm⟩ by simp [extend,hm]]
    rw [abs_of_nonpos (sub_nonpos.mpr hh.2)]
    linarith [hh.1]
  have hlim : ∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun n => |approxGamma γ n s-extend γ.val s|) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      (γ.ae_continuous).filter_mono (ae_mono Measure.restrict_le_self)] with s hs hc
    have hm : s ∈ Ico (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
    have hh := (approxGamma_tendsto γ ⟨s,hm⟩ (hc hm)).sub (tendsto_const_nhds (x := γ.val ⟨s,hm⟩))
    have he : extend γ.val s = γ.val ⟨s,hm⟩ := by simp [extend,hm]
    simpa only [he,sub_self,abs_zero] using hh.abs
  have hh := tendsto_integral_of_dominated_convergence (extend γ.val) hint
    γ.integrable.integrableOn hb hlim
  simp only [integral_zero] at hh
  convert hh using 1 <;> try rfl
  funext n
  exact intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1) |>.trans
    (integral_Ioc_eq_integral_Ioo)

end ZeroTemperatureSK

end
end
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma uniformCauchySeq_deriv_of_bound {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 2 (f n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, |deriv (deriv (f n)) x| ≤ C)
    (hlim : TendstoUniformly f g atTop) :
    UniformCauchySeqOn (fun n => deriv (f n)) atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  rw [Metric.tendstoUniformly_iff] at hlim
  intro ε hε
  let h : ℝ := ε / (2*C+1)
  have hh : 0 < h := div_pos hε (by positivity)
  have hδ : 0 < ε*h/8 := by positivity
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim (ε*h/8) hδ)
  refine ⟨N,fun m hm n hn x _ => ?_⟩
  have hA : ∀ y, |(f m-f n) y| ≤ 2*(ε*h/8) := by
    intro y
    have hm' := hN m hm y
    have hn' := hN n hn y
    simp only [Real.dist_eq] at hm' hn'
    calc
      _ = |(g y-f n y)-(g y-f m y)| := by simp only [Pi.sub_apply]; congr 1; ring
      _ ≤ |g y-f n y|+|g y-f m y| := abs_sub _ _
      _ ≤ _ := by linarith
  have hd (y : ℝ) : deriv (f m-f n) y = deriv (f m) y-deriv (f n) y :=
    deriv_sub ((hf m).differentiable (by norm_num) y) ((hf n).differentiable (by norm_num) y)
  have hdd (y : ℝ) : deriv (deriv (f m-f n)) y =
      deriv (deriv (f m)) y-deriv (deriv (f n)) y := by
    rw [show deriv (f m-f n) = deriv (f m)-deriv (f n) from funext hd]
    exact deriv_sub
      (by simpa only [iteratedDeriv_one] using (hf m).differentiable_iteratedDeriv 1 (by norm_num) y)
      (by simpa only [iteratedDeriv_one] using (hf n).differentiable_iteratedDeriv 1 (by norm_num) y)
  have hdC : ∀ y, |deriv (deriv (f m-f n)) y| ≤ 2*C := by
    intro y
    rw [hdd]
    exact (abs_sub _ _).trans (by linarith [hb m y,hb n y])
  have hi := derivative_interpolation ((hf m).sub (hf n)) hA hdC hh x
  have hc : h*(2*C) < ε := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*C+1)).mpr
    nlinarith
  have he : 2*(2*(ε*h/8))/h = ε/2 := by field_simp; ring
  change |deriv (f m-f n) x| ≤ 2*(2*(ε*h/8))/h+h*(2*C)/2 at hi
  rw [he,hd] at hi
  rw [Real.dist_eq]
  linarith

theorem tendstoUniformly_deriv_of_bound {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 2 (f n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, |deriv (deriv (f n)) x| ≤ C)
    (hlim : TendstoUniformly f g atTop) :
    Differentiable ℝ g ∧
      TendstoUniformly (fun n => deriv (f n)) (deriv g) atTop := by
  have hc := uniformCauchySeq_deriv_of_bound hf hC hb hlim
  let d : ℝ → ℝ := fun x => atTop.limUnder (fun n => deriv (f n) x)
  have hd : TendstoUniformly (fun n => deriv (f n)) d atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun x _ => (hc.cauchySeq (mem_univ x)).tendsto_limUnder)
  have hg (x : ℝ) : HasDerivAt g (d x) x :=
    hasDerivAt_of_tendstoUniformly hd (Filter.Eventually.of_forall
      (fun n x => ((hf n).differentiable (by norm_num) x).hasDerivAt)) hlim.tendsto_at x
  refine ⟨fun x => (hg x).differentiableAt, ?_⟩
  have he : deriv g = d := funext (fun x => (hg x).deriv)
  rwa [he]

lemma contDiff_iteratedDeriv_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv m f) := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem smooth_limit_of_uniform_derivative_bounds {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, |iteratedDeriv (m+2) (f n) x| ≤ C)
    (hlim : TendstoUniformly f g atTop) :
    ContDiff ℝ ∞ g ∧
      ∀ m : ℕ, TendstoUniformly (fun n => iteratedDeriv m (f n)) (iteratedDeriv m g) atTop := by
  have hconv (m : ℕ) :
      TendstoUniformly (fun n => iteratedDeriv m (f n)) (iteratedDeriv m g) atTop := by
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hlim
    | succ m ih =>
      obtain ⟨C,hC,hbC⟩ := hb m
      have hh := tendstoUniformly_deriv_of_bound
        (fun n => (contDiff_iteratedDeriv_infty (hf n) m).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
        hC (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hbC) ih
      simpa only [iteratedDeriv_succ] using hh.2
  refine ⟨?_,hconv⟩
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _hm
  obtain ⟨C,hC,hbC⟩ := hb m
  exact (tendstoUniformly_deriv_of_bound
    (fun n => (contDiff_iteratedDeriv_infty (hf n) m).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hC (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hbC) (hconv m)).1

lemma iteratedDeriv_limit_bound {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (m : ℕ) {C : ℝ}
    (hconv : TendstoUniformly (fun n => iteratedDeriv m (f n)) (iteratedDeriv m g) atTop)
    (hb : ∀ n x, |iteratedDeriv m (f n) x| ≤ C) (x : ℝ) :
    |iteratedDeriv m g x| ≤ C := by
  exact le_of_tendsto (hconv.tendsto_at x).abs (Filter.Eventually.of_forall (fun n => hb n x))

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma finiteValue_tail_of_le {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) ≤ t) : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
  rcases lt_or_eq_of_le ht with ht|rfl
  · exact finiteValue_tail f c h N i ht
  · rw [finiteValue_head f c h N i le_rfl,sub_self,finiteValue_zero hf hLip]
    funext x
    exact backward_terminal _ _ _ _

def finiteSource (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) : ℝ :=
  finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x)^2

lemma measurable_finiteSource {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (fun p : ℝ × ℝ => finiteSource c h f N i p.1 p.2) := by
  exact ((measurable_finiteCoeff c h N i).comp measurable_fst).mul
    ((measurable_spatial_deriv (measurable_finiteValue hf hLip c h N i)
      (fun r => (finiteValue_regular hf hLip c h N i r).smooth.differentiable (by simp))).pow_const 2)

lemma finiteSource_bounded {f : ℝ → ℝ} (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t x, |finiteSource c h f N i t x| ≤ C := by
  obtain ⟨C,hC⟩ := finiteCoeff_bounds c h N i
  refine ⟨C,fun t x => ?_⟩
  have hd : |deriv (finiteValue c h f N i t) x| ≤ 1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) (finiteValue_lipschitz hLip c h N i t)
  rw [finiteSource,abs_mul,abs_pow,abs_of_nonneg (hC t).1]
  have hs : |deriv (finiteValue c h f N i t) x|^2 ≤ 1 := by
    nlinarith [abs_nonneg (deriv (finiteValue c h f N i t) x)]
  nlinarith [(hC t).1,(hC t).2]

lemma intervalIntegrable_heat_finiteSource {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (p a b x : ℝ) :
    IntervalIntegrable (fun r => varianceHeat (r-p) (finiteSource c h f N i r) x) volume a b := by
  obtain ⟨C,hC⟩ := finiteSource_bounded hLip c h N i
  have hm := measurable_varianceHeat_family (measurable_finiteSource hf hLip c h N i)
    (measurable_id.sub_const p)
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun
    (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with r
  simpa only [Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg] using varianceHeat_abs_le (hC r) (r-p) x

lemma finiteSource_head (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : t ≤ h) : finiteSource c h f (N+1) i t =
      fun x => (c i:ℝ)*(deriv (backward (c i) h (cascade c h f N (i+1)) t) x)^2 := by
  funext x
  rw [finiteSource,finiteValue_head f c h N i ht]
  simp only [finiteCoeff,ite_eq_left ht]

lemma finiteSource_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) < t) : finiteSource c h f (N+1) i t = finiteSource c h f N (i+1) (t-h) := by
  funext x
  rw [finiteSource,finiteValue_tail f c h N i ht]
  simp only [finiteCoeff,ite_eq_right (not_le.mpr ht),finiteSource]

lemma integral_heat_finiteSource_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0)
    (N i : ℕ) {a b : ℝ} (ha : (h:ℝ) ≤ a) (hab : a ≤ b) (p x : ℝ) :
    (∫ r in a..b, varianceHeat (r-p) (finiteSource c h f (N+1) i r) x) =
      ∫ r in a-h..b-h, varianceHeat (r-(p-h)) (finiteSource c h f N (i+1) r) x := by
  rw [← intervalIntegral.integral_comp_sub_right (f := fun r => varianceHeat (r-(p-h))
    (finiteSource c h f N (i+1) r) x) (h:ℝ)]
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro r hr
  dsimp only
  rw [finiteSource_tail f c h N i (ha.trans_lt hr.1)]
  rw [show r-(h:ℝ)-(p-h) = r-p by ring]

lemma finiteValue_heat_dual {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {p a b : ℝ} (ha : 0 ≤ a) (hpa : p ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    varianceHeat (b-p) (finiteValue c h f N i b) x =
      varianceHeat (a-p) (finiteValue c h f N i a) x-
        (1/2)*(∫ r in a..b, varianceHeat (r-p) (finiteSource c h f N i r) x) := by
  induction N generalizing i p a b with
  | zero =>
    have hb0 : b = 0 := by simp only [Nat.cast_zero,zero_mul] at hb; linarith
    have ha0 : a = 0 := by linarith
    simp only [ha0,hb0,intervalIntegral.integral_same,mul_zero,sub_zero]
  | succ N ih =>
    by_cases hbh : b ≤ h
    · rw [finiteValue_head f c h N i hbh,finiteValue_head f c h N i (hab.trans hbh)]
      have hi : (∫ r in a..b, varianceHeat (r-p) (finiteSource c h f (N+1) i r) x) =
          (c i:ℝ)*(∫ r in a..b, varianceHeat (r-p)
            (fun z => (deriv (backward (c i) h (cascade c h f N (i+1)) r) z)^2) x) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro r hr
        dsimp only
        rw [finiteSource_head f c h N i (hr.2.le.trans hbh),varianceHeat_const_mul]
      rw [hi]
      have he := backward_heat_dual (cascade_regular hf hLip c h N (i+1))
        (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg ha hpa hab hbh x
      linarith
    · have hhb : (h:ℝ) < b := lt_of_not_ge hbh
      have hbn : b-h ≤ (N:ℝ)*h := by
        push_cast at hb
        nlinarith
      by_cases hah : (h:ℝ) ≤ a
      · rw [finiteValue_tail_of_le hf hLip c h N i hhb.le,
          finiteValue_tail_of_le hf hLip c h N i hah,
          integral_heat_finiteSource_tail f c h N i hah hab]
        have he := ih (i+1) (p := p-h) (a := a-h) (b := b-h)
          (sub_nonneg.mpr hah) (by linarith) (by linarith) hbn
        rw [show b-(h:ℝ)-(p-h) = b-p by ring,
          show a-(h:ℝ)-(p-h) = a-p by ring] at he
        exact he
      · have hah' : a ≤ h := (lt_of_not_ge hah).le
        have hjoin := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_heat_finiteSource hf hLip c h (N+1) i p a h x)
          (intervalIntegrable_heat_finiteSource hf hLip c h (N+1) i p h b x)
        have hhead := backward_heat_dual (cascade_regular hf hLip c h N (i+1))
          (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg ha hpa hah' le_rfl x
        have hihead : (∫ r in a..(h:ℝ), varianceHeat (r-p) (finiteSource c h f (N+1) i r) x) =
            (c i:ℝ)*(∫ r in a..(h:ℝ), varianceHeat (r-p)
              (fun z => (deriv (backward (c i) h (cascade c h f N (i+1)) r) z)^2) x) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr_Ioo_of_le hah'
          intro r hr
          dsimp only
          rw [finiteSource_head f c h N i hr.2.le,varianceHeat_const_mul]
        have htail := ih (i+1) (p := p-h) (a := 0) (b := b-h)
          le_rfl (by linarith) (sub_nonneg.mpr hhb.le) hbn
        rw [finiteValue_zero hf hLip] at htail
        have hseam : backward (c i) h (cascade c h f N (i+1)) h = cascade c h f N (i+1) := by
          funext z; exact backward_terminal _ _ _ _
        rw [hseam] at hhead
        rw [finiteValue_tail_of_le hf hLip c h N i hhb.le,
          finiteValue_head f c h N i hah',← hjoin,hihead,
          integral_heat_finiteSource_tail f c h N i le_rfl hhb.le]
        simp only [sub_self] at *
        have he1 : b-(h:ℝ)-(p-h) = b-p := by ring
        have he2 : 0-(p-(h:ℝ)) = h-p := by ring
        rw [he1,he2] at htail
        linarith

lemma finiteValue_mild {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    finiteValue c h f N i a x = varianceHeat (b-a) (finiteValue c h f N i b) x+
      (1/2)*(∫ r in a..b, varianceHeat (r-a) (finiteSource c h f N i r) x) := by
  have he := finiteValue_heat_dual hf hLip c h N i ha le_rfl hab hb x
  rw [sub_self,varianceHeat_zero] at he
  linarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.BoundedSmoothFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure BoundedSmoothFamily (F : ℝ → ℝ → ℝ) : Prop where
  measurable : Measurable (fun p : ℝ × ℝ => F p.1 p.2)
  regular : ∀ t, BoundedSmooth (F t)
  bounds : ∀ n : ℕ, ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv n (F t) x| ≤ C

lemma BoundedSmoothFamily.bound {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    ∃ C : ℝ≥0, ∀ t x, |F t x| ≤ C := by simpa using hF.bounds 0

lemma BoundedSmoothFamily.deriv {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    BoundedSmoothFamily (fun t => deriv (F t)) := by
  refine ⟨measurable_spatial_deriv hF.measurable
    (fun t => (hF.regular t).smooth.differentiable (by simp)),fun t => (hF.regular t).deriv,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using hF.bounds (n+1)

lemma BoundedSmoothFamily.mul {F G : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hG : BoundedSmoothFamily G) :
    BoundedSmoothFamily (fun t x => F t x*G t x) := by
  classical
  refine ⟨hF.measurable.mul hG.measurable,fun t => (hF.regular t).mul (hG.regular t),?_⟩
  intro n
  choose A hA using hF.bounds
  choose B hB using hG.bounds
  refine ⟨∑ j ∈ Finset.range (n+1), (n.choose j:ℝ≥0)*A j*B (n-j),fun t x => ?_⟩
  rw [iteratedDeriv_fun_mul (n := n)
    ((hF.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((hG.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  push_cast
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ (n.choose j:ℝ) from Nat.cast_nonneg _)]
  gcongr
  · exact hA j t x
  · exact hB (n-j) t x

lemma BoundedSmoothFamily.timeConst {d : ℝ → ℝ} {C : ℝ≥0}
    (hm : Measurable d) (hC : ∀ t, |d t| ≤ C) :
    BoundedSmoothFamily (fun t (_x : ℝ) => d t) := by
  refine ⟨hm.comp measurable_fst,fun t => BoundedSmooth.const (d t),?_⟩
  intro n
  cases n with
  | zero => exact ⟨C,fun t x => by simpa only [iteratedDeriv_zero] using hC t⟩
  | succ n => exact ⟨0,fun t x => by simp [iteratedDeriv_const]⟩

lemma BoundedSmoothFamily.iteratedDeriv {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (n : ℕ) :
    BoundedSmoothFamily (fun t => iteratedDeriv n (F t)) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma finiteGradient_family {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (fun t => deriv (finiteValue c h f N i t)) := by
  refine ⟨measurable_spatial_deriv (measurable_finiteValue hf hLip c h N i)
    (fun t => (finiteValue_regular hf hLip c h N i t).smooth.differentiable (by simp)),
    fun t => (finiteValue_regular hf hLip c h N i t).deriv_bounded,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using finiteValue_uniform_derivative_bounds hf hLip c h N i n

lemma finiteCoeff_family (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (fun t (_x : ℝ) => finiteCoeff c h N i t) := by
  obtain ⟨C,hC⟩ := finiteCoeff_bounds c h N i
  exact BoundedSmoothFamily.timeConst (measurable_finiteCoeff c h N i)
    (fun t => by simpa only [abs_of_nonneg (hC t).1] using (hC t).2)

lemma finiteSource_family {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (finiteSource c h f N i) := by
  have hU := finiteGradient_family hf hLip c h N i
  change BoundedSmoothFamily (fun t x => finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x)^2)
  simpa only [pow_two] using (finiteCoeff_family c h N i).mul (hU.mul hU)

def finiteBurgersSource (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) : ℝ :=
  finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x*deriv (deriv (finiteValue c h f N i t)) x)

lemma finiteBurgersSource_family {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (finiteBurgersSource c h f N i) := by
  have hU := finiteGradient_family hf hLip c h N i
  exact (finiteCoeff_family c h N i).mul (hU.mul hU.deriv)

lemma deriv_finiteSource {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    deriv (finiteSource c h f N i t) = fun x => 2*finiteBurgersSource c h f N i t x := by
  funext x
  have hd := (((finiteValue_regular hf hLip c h N i t).deriv_bounded.smooth.differentiable (by simp) x).hasDerivAt.fun_pow 2).const_mul (finiteCoeff c h N i t)
  change deriv (fun x => finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) x)^2) x = _
  have hd' : deriv (fun z => finiteCoeff c h N i t*(deriv (finiteValue c h f N i t) z)^2) x =
      finiteCoeff c h N i t*(2*deriv (finiteValue c h f N i t) x*deriv (deriv (finiteValue c h f N i t)) x) := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using hd.deriv
  rw [hd']
  simp only [finiteBurgersSource]
  ring

lemma finiteGradient_mild {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    deriv (finiteValue c h f N i a) x = varianceHeat (b-a) (deriv (finiteValue c h f N i b)) x+
      ∫ r in a..b, varianceHeat (r-a) (finiteBurgersSource c h f N i r) x := by
  have hS := finiteSource_family hf hLip c h N i
  obtain ⟨A,hA⟩ := hS.bound
  obtain ⟨B,hB⟩ := hS.deriv.bound
  have hDt := hasDerivAt_integral_varianceHeat hS.measurable hS.regular hA hB a b x
  have hbreg := finiteValue_regular hf hLip c h N i b
  have hbLip := finiteValue_lipschitz hLip c h N i b
  have hHt : HasDerivAt (varianceHeat (b-a) (finiteValue c h f N i b))
      (varianceHeat (b-a) (deriv (finiteValue c h f N i b)) x) x :=
    hasDerivAt_scaled_space (hbreg.smooth.of_le (by simp)) (exponentialBound_of_lipschitz hbLip)
      (ExponentialBound.of_bounded (A := 1) (fun z => by
        simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀ := z) hbLip)) (Real.sqrt (b-a)) x
  have heFun : finiteValue c h f N i a = fun z =>
      varianceHeat (b-a) (finiteValue c h f N i b) z+
        (1/2)*(∫ r in a..b, varianceHeat (r-a) (finiteSource c h f N i r) z) :=
    funext (finiteValue_mild hf hLip c h N i ha hab hb)
  have hdR : deriv (fun z => varianceHeat (b-a) (finiteValue c h f N i b) z+
      (1/2)*(∫ r in a..b, varianceHeat (r-a) (finiteSource c h f N i r) z)) x =
      varianceHeat (b-a) (deriv (finiteValue c h f N i b)) x+
        (1/2)*(∫ r in a..b, varianceHeat (r-a) (deriv (finiteSource c h f N i r)) x) :=
    (hHt.add (hDt.const_mul (1/2))).deriv
  rw [heFun,hdR]
  simp_rw [deriv_finiteSource hf hLip,varianceHeat_const_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

end ZeroTemperatureSK.Heat

open MeasureTheory Set Filter
open scoped Topology
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def forwardTime (a t : ℝ) : ℝ := a+max t 0
def forwardScale (a t : ℝ) : ℝ := a/forwardTime a t
def forwardVariance (a t : ℝ) : ℝ := a*max t 0/forwardTime a t

def forwardCorrection (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*Real.log (forwardScale a t)+
    varianceLogHeat 1 (forwardVariance a t) f (forwardScale a t*x)

def forwardScore (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  x/forwardTime a t-deriv (forwardCorrection a f t) x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.FamilyDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmoothFamily.add {F G : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hG : BoundedSmoothFamily G) :
    BoundedSmoothFamily (fun t x => F t x+G t x) := by
  refine ⟨hF.measurable.add hG.measurable,fun t => (hF.regular t).add (hG.regular t),?_⟩
  intro n
  obtain ⟨A,hA⟩ := hF.bounds n
  obtain ⟨B,hB⟩ := hG.bounds n
  refine ⟨A+B,fun t x => ?_⟩
  rw [iteratedDeriv_fun_add (n := n)
    ((hF.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((hG.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  exact (abs_add_le _ _).trans (add_le_add (hA t x) (hB t x))

lemma BoundedSmoothFamily.const_mul {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (c : ℝ) : BoundedSmoothFamily (fun t x => c*F t x) :=
  (BoundedSmoothFamily.timeConst (C := Real.nnabs c) measurable_const (fun _ => by simp [Real.coe_nnabs])).mul hF

lemma BoundedSmoothFamily.intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (x a b : ℝ) : IntervalIntegrable (fun t => F t x) volume a b := by
  obtain ⟨C,hC⟩ := hF.bound
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun
    (hF.measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg] using hC t x

lemma BoundedSmoothFamily.hasDerivAt_integral {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (a b x : ℝ) :
    HasDerivAt (fun z => ∫ t in a..b, F t z) (∫ t in a..b, _root_.deriv (F t) x) x := by
  obtain ⟨C,hC⟩ := hF.deriv.bound
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => F t z) (F' := fun z t => _root_.deriv (F t) z)
    (bound := fun _ => (C:ℝ)) (s := Set.univ) (Filter.univ_mem)
    (Eventually.of_forall (fun z => (hF.measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    (hF.intervalIntegrable x a b) ((hF.deriv.measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
    (intervalIntegrable_const) ?_).2
  · filter_upwards [] with t ht z hz
    exact hC t z
  · filter_upwards [] with t ht z hz
    exact ((hF.regular t).smooth.differentiable (by simp) z).hasDerivAt

lemma BoundedSmoothFamily.iteratedDeriv_integral {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (n : ℕ) (a b x : ℝ) :
    _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) x =
      ∫ t in a..b, _root_.iteratedDeriv n (F t) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n hn =>
    have he : _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) =
        fun z => ∫ t in a..b, _root_.iteratedDeriv n (F t) z := funext hn
    rw [iteratedDeriv_succ,he]
    simpa only [iteratedDeriv_succ] using ((hF.iteratedDeriv n).hasDerivAt_integral a b x).deriv

end ZeroTemperatureSK.Heat

end
end
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma continuousOn_deriv_family {A : Type*} [TopologicalSpace A] {S : Set A}
    {f : A → ℝ → ℝ} (hc : ContinuousOn (fun p : A × ℝ => f p.1 p.2) (S ×ˢ Set.univ))
    (hf : ∀ t ∈ S, ContDiff ℝ 2 (f t)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ S, ∀ x, |deriv (deriv (f t)) x| ≤ C) :
    ContinuousOn (fun p : A × ℝ => deriv (f p.1) p.2) (S ×ˢ Set.univ) := by
  let h : ℕ → ℝ := fun n => 1/((n+1:ℕ):ℝ)
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hlim : Tendsto h atTop (𝓝 0) := by
    simpa only [h,Nat.cast_add,Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0))
  let F : ℕ → A × ℝ → ℝ := fun n p => (f p.1 (p.2+h n)-f p.1 p.2)/h n
  have hcont (n : ℕ) : ContinuousOn (F n) (S ×ˢ Set.univ) := by
    dsimp [F]
    apply ContinuousOn.div_const
    apply ContinuousOn.sub _ hc
    apply hc.comp (continuous_fst.prodMk (continuous_snd.add_const (h n))).continuousOn
    intro p hp
    exact ⟨hp.1,mem_univ _⟩
  have hconv : TendstoUniformlyOn F (fun p => deriv (f p.1) p.2) atTop (S ×ˢ Set.univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hc0 : Tendsto (fun n => C/2*h n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim (a := C/2)
    filter_upwards [hc0.eventually (Metric.ball_mem_nhds 0 hε)] with n hn p hp
    rw [Real.dist_eq,sub_zero,
      abs_of_nonneg (mul_nonneg (div_nonneg hC (by norm_num)) (hh n).le)] at hn
    have ht := taylor1_bound (hf p.1 hp.1) (hb p.1 hp.1) p.2 (h n)
    have hb' : |F n p-deriv (f p.1) p.2| ≤ C/2*h n := by
      dsimp [F]
      have he : (f p.1 (p.2+h n)-f p.1 p.2)/h n-deriv (f p.1) p.2 =
          (f p.1 (p.2+h n)-f p.1 p.2-deriv (f p.1) p.2*h n)/h n := by field_simp [ne_of_gt (hh n)]
      rw [he,abs_div,abs_of_pos (hh n),div_le_iff₀ (hh n)]
      rw [abs_of_pos (hh n)] at ht
      nlinarith
    rw [Real.dist_eq,abs_sub_comm]
    exact hb'.trans_lt hn
  exact hconv.continuousOn (Filter.Eventually.of_forall hcont).frequently

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.GaussianFlowRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def gaussianRate (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*deriv (deriv (varianceLogHeat c t f)) x+
    c/2*(deriv (varianceLogHeat c t f) x)^2

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def forwardCorrectionRate (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*iteratedDeriv 2 (forwardCorrection a f t) x+
    (1/2:ℝ)*(deriv (forwardCorrection a f t) x)^2-
    (x/forwardTime a t)*deriv (forwardCorrection a f t) x-
    (1/2:ℝ)/forwardTime a t

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def AffineSmoothFamily (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ A B : ℝ → ℝ → ℝ, BoundedSmoothFamily A ∧
    Continuous (fun p : ℝ × ℝ => A p.1 p.2) ∧ BoundedSmoothFamily B ∧
    Continuous (fun p : ℝ × ℝ => B p.1 p.2) ∧ F = fun t x => A t x+x*B t x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.BurgersConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def burgersRate (r : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*iteratedDeriv 2 (r t) x+r t x*deriv (r t) x

structure SmoothBurgers (r : ℝ → ℝ → ℝ) : Prop where
  family : BoundedSmoothFamily r
  continuous : ∀ T, ContinuousOn (fun p : ℝ × ℝ => r p.1 p.2) (Icc (0:ℝ) T ×ˢ univ)
  time_derivative : ∀ n t, 0 < t → ∀ x,
    HasDerivAt (fun s => iteratedDeriv n (r s) x) (iteratedDeriv n (burgersRate r t) x) t

def gaussianBurgers (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  c*deriv (varianceLogHeat c t f) x

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def scoreRate (s : ℝ → ℝ → ℝ) (t x : ℝ) :=
  (1/2:ℝ)*iteratedDeriv 2 (s t) x-s t x*deriv (s t) x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.BurgersJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def backwardWronskian (r : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  r t x*deriv (burgersRate r t) x-deriv (r t) x*burgersRate r t x

def wronskianRate (r : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  burgersRate r t x*deriv (burgersRate r t) x+
    r t x*((1/2:ℝ)*iteratedDeriv 3 (burgersRate r t) x+
      2*deriv (r t) x*deriv (burgersRate r t) x+
      burgersRate r t x*iteratedDeriv 2 (r t) x+
      r t x*iteratedDeriv 2 (burgersRate r t) x)-
    (deriv (burgersRate r t) x*burgersRate r t x+
      deriv (r t) x*((1/2:ℝ)*iteratedDeriv 2 (burgersRate r t) x+
        r t x*deriv (burgersRate r t) x+deriv (r t) x*burgersRate r t x))

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure SmoothForward (s : ℝ → ℝ → ℝ) : Prop where
  family : AffineSmoothFamily s
  deriv_family : BoundedSmoothFamily (fun t => deriv (s t))
  time_derivative : ∀ n t, 0 < t → ∀ x,
    HasDerivAt (fun u => iteratedDeriv n (s u) x) (iteratedDeriv n (scoreRate s t) x) t

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.BackwardRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure BackwardShape (r : ℝ → ℝ) : Prop where
  odd : Function.Odd r
  derivative_pos : ∀ x, 0 < deriv r x
  second_nonpos : ∀ x, 0 ≤ x → iteratedDeriv 2 r x ≤ 0
  rate_nonpos : ∀ x, 0 ≤ x → burgersRate (fun _ => r) 0 x ≤ 0
  wronskian_nonneg : ∀ x, 0 ≤ x → 0 ≤ backwardWronskian (fun _ => r) 0 x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.TerminalShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def tanhDrift (c M x : ℝ) : ℝ := c*Real.tanh (M*x)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure ForwardDatumShape (f : ℝ → ℝ) : Prop where
  even : Function.Even f
  second : ∀ x, iteratedDeriv 2 f x ≤ 0
  third : ∀ x, 0 ≤ x → 0 ≤ iteratedDeriv 3 f x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.InvSqrtNegHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Smoothing

lemma inv_sqrt_eq_neg_half {x : ℝ} (hx : 0 ≤ x) :
    1/Real.sqrt x = x^(-(1/2:ℝ)) := by
  rw [Real.rpow_neg hx,← Real.sqrt_eq_rpow,one_div]

lemma intervalIntegrable_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => 1/Real.sqrt x) volume a b := by
  apply (intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) (r := -(1/2:ℝ)) (by norm_num)).congr
  intro x hx
  rw [uIoc_of_le hab] at hx
  exact (inv_sqrt_eq_neg_half (ha.trans hx.1.le)).symm

lemma integral_inv_sqrt {b : ℝ} (hb : 0 ≤ b) :
    (∫ x in (0:ℝ)..b, 1/Real.sqrt x) = 2*Real.sqrt b := by
  have he : (∫ x in (0:ℝ)..b, 1/Real.sqrt x) = ∫ x in (0:ℝ)..b, x^(-(1/2:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hb] at hx
    exact inv_sqrt_eq_neg_half hx.1
  rw [he,integral_rpow (Or.inl (by norm_num : -(1:ℝ) < -(1/2:ℝ)))]
  norm_num only [neg_add_cancel_left,show -(1/2:ℝ)+1=1/2 by norm_num,Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0),sub_zero]
  rw [← Real.sqrt_eq_rpow]
  ring

lemma intervalIntegrable_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun r => 1/Real.sqrt (r-a)) volume a b := by
  simpa only [zero_add,sub_add_cancel] using
    (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_right a

lemma intervalIntegrable_inv_sqrt_sub' {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun r => 1/Real.sqrt (b-r)) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_left b
  simpa only [sub_zero,sub_sub_cancel] using h.symm

lemma integral_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    (∫ r in a..b, 1/Real.sqrt (r-a)) = 2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1/Real.sqrt x) a,sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma integral_inv_sqrt_sub' {a b : ℝ} (hab : a ≤ b) :
    (∫ r in a..b, 1/Real.sqrt (b-r)) = 2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => 1/Real.sqrt x) b,sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma sqrt_kernel_bound {a r b : ℝ} (har : a < r) (hrb : r < b) :
    1/(Real.sqrt (r-a)*Real.sqrt (b-r)) ≤
      (2/Real.sqrt (b-a))*(1/Real.sqrt (r-a)+1/Real.sqrt (b-r)) := by
  have hp : 0 < Real.sqrt (r-a) := Real.sqrt_pos.mpr (sub_pos.mpr har)
  have hq : 0 < Real.sqrt (b-r) := Real.sqrt_pos.mpr (sub_pos.mpr hrb)
  have hh : 0 < Real.sqrt (b-a) := Real.sqrt_pos.mpr (sub_pos.mpr (har.trans hrb))
  have hps := Real.sq_sqrt (sub_pos.mpr har).le
  have hqs := Real.sq_sqrt (sub_pos.mpr hrb).le
  have hhs := Real.sq_sqrt (sub_pos.mpr (har.trans hrb)).le
  have hs : Real.sqrt (b-a) ≤ 2*(Real.sqrt (r-a)+Real.sqrt (b-r)) := by
    nlinarith [mul_nonneg hp.le hq.le]
  apply (div_le_iff₀ (mul_pos hp hq)).mpr
  have he : (2/Real.sqrt (b-a))*(1/Real.sqrt (r-a)+1/Real.sqrt (b-r)) *
      (Real.sqrt (r-a)*Real.sqrt (b-r)) =
      2*(Real.sqrt (r-a)+Real.sqrt (b-r))/Real.sqrt (b-a) := by
    field_simp
    ring
  rw [he]
  exact (le_div_iff₀ hh).mpr (by simpa using hs)

lemma intervalIntegrable_sqrt_kernel {a b : ℝ} (hab : a < b) :
    IntervalIntegrable (fun r => 1/(Real.sqrt (r-a)*Real.sqrt (b-r))) volume a b := by
  apply (((intervalIntegrable_inv_sqrt_sub hab.le).add
    (intervalIntegrable_inv_sqrt_sub' hab.le)).const_mul (2/Real.sqrt (b-a))).mono_fun'
      ((measurable_const.div ((measurable_id.sub_const a).sqrt.mul ((measurable_const.sub measurable_id).sqrt))).aestronglyMeasurable)
  rw [uIoc_of_le hab.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,show ∀ᵐ r ∂volume.restrict (Ioc a b), r ≠ b from
    (ae_restrict_of_ae (volume.ae_ne b))] with r hr hrb
  simp only [Pi.div_apply,Pi.mul_apply,Pi.sub_apply,id_eq]
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 1/(Real.sqrt (r-a)*Real.sqrt (b-r)) by positivity)]
  exact sqrt_kernel_bound hr.1 (lt_of_le_of_ne hr.2 hrb)

lemma integral_sqrt_kernel_le {a b : ℝ} (hab : a < b) :
    (∫ r in a..b, 1/(Real.sqrt (r-a)*Real.sqrt (b-r))) ≤ 8 := by
  have hL := intervalIntegrable_inv_sqrt_sub hab.le
  have hR := intervalIntegrable_inv_sqrt_sub' hab.le
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab.le
    (intervalIntegrable_sqrt_kernel hab) ((hL.add hR).const_mul (2/Real.sqrt (b-a)))
    (fun r hr => sqrt_kernel_bound hr.1 hr.2)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hL hR,
    integral_inv_sqrt_sub hab.le,integral_inv_sqrt_sub' hab.le] at h
  have hr : Real.sqrt (b-a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hab))
  have he : 2/Real.sqrt (b-a)*(2*Real.sqrt (b-a)+2*Real.sqrt (b-a)) = 8 := by field_simp; ring
  rwa [he] at h

end ZeroTemperatureSK.Smoothing

namespace ZeroTemperatureSK.Smoothing

def weightedValues (F : ℝ → ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {z | ∃ t ∈ Icc a b, ∃ x, z = Real.sqrt (b-t)*|F t x|}

def weightedSize (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := sSup (weightedValues F a b)

lemma weightedValues_nonempty (F : ℝ → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (weightedValues F a b).Nonempty := by
  refine ⟨0,b,⟨hab,le_rfl⟩,0,?_⟩
  simp

lemma weightedValues_bddAbove {F : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) : BddAbove (weightedValues F a b) := by
  refine ⟨Real.sqrt (b-a)*max C 0,?_⟩
  rintro _ ⟨t,ht,x,rfl⟩
  apply mul_le_mul (Real.sqrt_le_sqrt (by linarith [ht.1]))
    ((hC t ht x).trans (le_max_left _ _)) (abs_nonneg _) (Real.sqrt_nonneg _)

lemma weighted_le_size {F : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    Real.sqrt (b-t)*|F t x| ≤ weightedSize F a b :=
  le_csSup (weightedValues_bddAbove hC) ⟨t,ht,x,rfl⟩

lemma weightedSize_nonneg {F : ℝ → ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) : 0 ≤ weightedSize F a b := by
  have h := weighted_le_size hC (t := b) ⟨hab,le_rfl⟩ 0
  simpa using h

lemma abs_le_weightedSize {F : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) {t : ℝ} (ht : t ∈ Ico a b) (x : ℝ) :
    |F t x| ≤ weightedSize F a b/Real.sqrt (b-t) := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (sub_pos.mpr ht.2))).mpr
  simpa only [mul_comm] using weighted_le_size hC ⟨ht.1,ht.2.le⟩ x

lemma weightedSize_le {F : ℝ → ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hK : ∀ t ∈ Icc a b, ∀ x, Real.sqrt (b-t)*|F t x| ≤ K) :
    weightedSize F a b ≤ K := by
  apply csSup_le (weightedValues_nonempty F hab)
  rintro _ ⟨t,ht,x,rfl⟩
  exact hK t ht x

lemma weighted_absorption {F : ℝ → ℝ → ℝ} {a b C K ε : ℝ} (hab : a < b)
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hsmall : ε*Real.sqrt (b-a) ≤ 1/2)
    (hineq : ∀ t ∈ Ico a b, ∀ x,
      Real.sqrt (b-t)*|F t x| ≤ K+ε*Real.sqrt (b-t)*weightedSize F a b) :
    weightedSize F a b ≤ 2*K := by
  have hM := weightedSize_nonneg hab.le hC
  have hsup : weightedSize F a b ≤ K+ε*Real.sqrt (b-a)*weightedSize F a b := by
    apply weightedSize_le hab.le
    intro t ht x
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · apply (hineq t ⟨ht.1,htb⟩ x).trans
      gcongr
      linarith [ht.1]
    · simp only [sub_self,Real.sqrt_zero,zero_mul]
      positivity
  nlinarith [mul_le_mul_of_nonneg_right hsmall hM]

end ZeroTemperatureSK.Smoothing

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.VarianceHeatGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Heat
open ZeroTemperatureSK.Smoothing

lemma varianceHeat_gradient_bound {g : ℝ → ℝ} (hg : BoundedSmooth g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, |g z| ≤ C) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |deriv (varianceHeat h g) x| ≤ kernelConstant*C/Real.sqrt h := by
  change |deriv (scaled (Real.sqrt h) g) x| ≤ _
  exact scaled_gradient_bound hg (C := ⟨C,hC⟩) hbound (Real.sqrt_pos.mpr hh) x

lemma deriv_varianceHeat_of_bounded {g : ℝ → ℝ} (hg : BoundedSmooth g) (h : ℝ) :
    deriv (varianceHeat h g) = varianceHeat h (deriv g) := by
  obtain ⟨A,hA⟩ := hg.bound
  obtain ⟨B,hB⟩ := hg.deriv.bound
  exact deriv_varianceHeat (hg.smooth.of_le (by simp))
    (ExponentialBound.of_bounded hA) (ExponentialBound.of_bounded hB) h

lemma deriv_of_mild {V G : ℝ → ℝ → ℝ} {A B : ℝ≥0} {t b : ℝ}
    (hV : BoundedSmooth (V b)) (hm : Measurable (fun p : ℝ × ℝ => G p.1 p.2))
    (hG : ∀ r, BoundedSmooth (G r)) (hA : ∀ r z, |G r z| ≤ A)
    (hB : ∀ r z, |deriv (G r) z| ≤ B)
    (hmild : ∀ x, V t x = varianceHeat (b-t) (V b) x+
      ∫ r in t..b, varianceHeat (r-t) (G r) x) (x : ℝ) :
    deriv (V t) x = deriv (varianceHeat (b-t) (V b)) x+
      ∫ r in t..b, deriv (varianceHeat (r-t) (G r)) x := by
  have hDt := hasDerivAt_integral_varianceHeat hm hG hA hB t b x
  obtain ⟨C,hC⟩ := hV.bound
  obtain ⟨D,hD⟩ := hV.deriv.bound
  have hHt : HasDerivAt (varianceHeat (b-t) (V b)) (varianceHeat (b-t) (deriv (V b)) x) x :=
    hasDerivAt_scaled_space (hV.smooth.of_le (by simp))
      (ExponentialBound.of_bounded hC) (ExponentialBound.of_bounded hD) (Real.sqrt (b-t)) x
  have heV : V t = fun z => varianceHeat (b-t) (V b) z+∫ r in t..b, varianceHeat (r-t) (G r) z := funext hmild
  have hdR : deriv (fun z => varianceHeat (b-t) (V b) z+∫ r in t..b, varianceHeat (r-t) (G r) z) x =
      varianceHeat (b-t) (deriv (V b)) x+∫ r in t..b, varianceHeat (r-t) (deriv (G r)) x := (hHt.add hDt).deriv
  rw [heV,hdR]
  simp_rw [deriv_varianceHeat_of_bounded hV,deriv_varianceHeat_of_bounded (hG _)]

lemma uniform_gradient_bound_of_mild {V G : ℝ → ℝ → ℝ} {A₀ B₀ : ℝ≥0}
    {a b A D R C : ℝ} (hab : a < b) (hA : 0 ≤ A) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hV : BoundedSmooth (V b)) (hm : Measurable (fun p : ℝ × ℝ => G p.1 p.2))
    (hG : ∀ r, BoundedSmooth (G r)) (hA₀ : ∀ r z, |G r z| ≤ A₀)
    (hB₀ : ∀ r z, |deriv (G r) z| ≤ B₀)
    (hC : ∀ r ∈ Icc a b, ∀ x, |deriv (V r) x| ≤ C)
    (hterminal : ∀ x, |V b x| ≤ A)
    (hsource : ∀ r ∈ Icc a b, ∀ x, |G r x| ≤ D*|deriv (V r) x|+R)
    (hmild : ∀ t ∈ Ico a b, ∀ x, V t x = varianceHeat (b-t) (V b) x+
      ∫ r in t..b, varianceHeat (r-t) (G r) x)
    (hsmall : 8*kernelConstant*D*Real.sqrt (b-a) ≤ 1/2) (x : ℝ) :
    |deriv (V a) x| ≤ 2*kernelConstant*(A+2*R*(b-a))/Real.sqrt (b-a) := by
  let W : ℝ → ℝ → ℝ := fun r => deriv (V r)
  let M : ℝ := weightedSize W a b
  have hM : 0 ≤ M := weightedSize_nonneg hab.le hC
  have hκ := kernelConstant_nonneg
  have hpoint (t : ℝ) (ht : t ∈ Ico a b) (z : ℝ) :
      Real.sqrt (b-t)*|W t z| ≤ kernelConstant*(A+2*R*(b-a))+
        (8*kernelConstant*D)*Real.sqrt (b-t)*M := by
    have htb : 0 < b-t := sub_pos.mpr ht.2
    have hs : 0 < Real.sqrt (b-t) := Real.sqrt_pos.mpr htb
    let H : ℝ → ℝ := fun r => (kernelConstant*D*M)*(1/(Real.sqrt (r-t)*Real.sqrt (b-r)))+
      (kernelConstant*R)*(1/Real.sqrt (r-t))
    have hHi : IntervalIntegrable H volume t b :=
      ((intervalIntegrable_sqrt_kernel ht.2).const_mul _).add
        ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul _)
    have hdom (r : ℝ) (hr : r ∈ Ioo t b) :
        |deriv (varianceHeat (r-t) (G r)) z| ≤ H r := by
      have hrab : r ∈ Ico a b := ⟨ht.1.trans hr.1.le,hr.2⟩
      have hwr (y : ℝ) : |W r y| ≤ M/Real.sqrt (b-r) := abs_le_weightedSize hC hrab y
      have hbnd (y : ℝ) : |G r y| ≤ D*(M/Real.sqrt (b-r))+R :=
        (hsource r ⟨hrab.1,hrab.2.le⟩ y).trans (add_le_add (mul_le_mul_of_nonneg_left (hwr y) hD) le_rfl)
      have hbnd0 : 0 ≤ D*(M/Real.sqrt (b-r))+R := by positivity
      apply (varianceHeat_gradient_bound (hG r) hbnd0 hbnd (sub_pos.mpr hr.1) z).trans_eq
      dsimp only [H]
      field_simp
    have hnorm : |∫ r in t..b, deriv (varianceHeat (r-t) (G r)) z| ≤ ∫ r in t..b, H r := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le ht.2.le _ hHi
      filter_upwards [volume.ae_ne b] with r hrb hr
      simpa only [Real.norm_eq_abs] using hdom r ⟨hr.1,lt_of_le_of_ne hr.2 hrb⟩
    have hHbound : (∫ r in t..b,H r) ≤ 8*kernelConstant*D*M+2*kernelConstant*R*Real.sqrt (b-t) := by
      dsimp only [H]
      rw [intervalIntegral.integral_add ((intervalIntegrable_sqrt_kernel ht.2).const_mul _)
        ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul _),intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,integral_inv_sqrt_sub ht.2.le]
      have hh := mul_le_mul_of_nonneg_left (integral_sqrt_kernel_le ht.2)
        (show 0 ≤ kernelConstant*D*M by positivity)
      nlinarith
    have he := deriv_of_mild hV hm hG hA₀ hB₀ (hmild t ht) z
    have hinitial := varianceHeat_gradient_bound hV hA hterminal htb z
    have hsum : |W t z| ≤ kernelConstant*A/Real.sqrt (b-t)+
        8*kernelConstant*D*M+2*kernelConstant*R*Real.sqrt (b-t) := by
      change |deriv (V t) z| ≤ _
      rw [he]
      have hh := abs_add_le (deriv (varianceHeat (b-t) (V b)) z)
        (∫ r in t..b, deriv (varianceHeat (r-t) (G r)) z)
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hsum hs.le
    have hcancel : Real.sqrt (b-t)*(kernelConstant*A/Real.sqrt (b-t)) = kernelConstant*A := by
      field_simp
    have hsq := Real.sq_sqrt htb.le
    have hgap : b-t ≤ b-a := by linarith [ht.1]
    have hrr := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*kernelConstant*R by positivity)
    have hscaled' : Real.sqrt (b-t)*|W t z| ≤ kernelConstant*A+
        8*kernelConstant*D*Real.sqrt (b-t)*M+2*kernelConstant*R*(b-t) := by
      apply hscaled.trans_eq
      rw [mul_add,mul_add,hcancel]
      have he : Real.sqrt (b-t)*(2*kernelConstant*R*Real.sqrt (b-t)) = 2*kernelConstant*R*(b-t) := by
        calc
          _ = 2*kernelConstant*R*(Real.sqrt (b-t))^2 := by ring
          _ = _ := by rw [hsq]
      rw [he]
      ring
    nlinarith [hscaled']
  have hMbound : M ≤ 2*(kernelConstant*(A+2*R*(b-a))) :=
    weighted_absorption hab hC (by positivity) (by positivity) hsmall hpoint
  have hw := abs_le_weightedSize hC (t := a) ⟨le_rfl,hab⟩ x
  apply hw.trans
  exact (div_le_div_of_nonneg_right hMbound (Real.sqrt_nonneg _)).trans_eq (by ring)

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat
open ZeroTemperatureSK.Smoothing

lemma iteratedDeriv_mild {V G : ℝ → ℝ → ℝ}
    (hV : BoundedSmoothFamily V) (hG : BoundedSmoothFamily G) {a b : ℝ}
    (hmild : ∀ z, V a z = varianceHeat (b-a) (V b) z+
      ∫ r in a..b, varianceHeat (r-a) (G r) z) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (V a) x = varianceHeat (b-a) (iteratedDeriv n (V b)) x+
      ∫ r in a..b, varianceHeat (r-a) (iteratedDeriv n (G r)) x := by
  induction n generalizing x with
  | zero => simpa only [iteratedDeriv_zero] using hmild x
  | succ n ih =>
    have hGn := hG.iteratedDeriv n
    obtain ⟨A,hA⟩ := hGn.bound
    obtain ⟨B,hB⟩ := hGn.deriv.bound
    have hd := deriv_of_mild (V := fun t => iteratedDeriv n (V t))
      ((hV.iteratedDeriv n).regular b) hGn.measurable hGn.regular hA hB ih x
    simp_rw [deriv_varianceHeat_of_bounded ((hV.iteratedDeriv n).regular b),
      deriv_varianceHeat_of_bounded (hGn.regular _)] at hd
    simpa only [iteratedDeriv_succ] using hd

lemma burgers_source_derivative_bound {U : ℝ → ℝ} (hU : BoundedSmooth U)
    {C : ℝ} (hC : 0 ≤ C) (hU1 : ∀ x, |U x| ≤ 1) (n : ℕ)
    (hb : ∀ j ≤ n, ∀ x, |iteratedDeriv j U x| ≤ C) (x : ℝ) :
    |iteratedDeriv n (fun z => U z*deriv U z) x| ≤ |iteratedDeriv (n+1) U x|+
      (∑ j ∈ Finset.range n, (n.choose (j+1):ℝ))*C^2 := by
  rw [iteratedDeriv_fun_mul
    (hU.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    (hU.deriv.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right,Nat.cast_one,iteratedDeriv_zero,one_mul,Nat.sub_zero,
    ← iteratedDeriv_succ']
  apply (abs_add_le _ _).trans
  have hlead : |U x*iteratedDeriv (n+1) U x| ≤ |iteratedDeriv (n+1) U x| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hU1 x) (abs_nonneg (iteratedDeriv (n+1) U x))
  have hrem : |∑ j ∈ Finset.range n,
      (n.choose (j+1):ℝ)*iteratedDeriv (j+1) U x*iteratedDeriv (n-(j+1)+1) U x| ≤
        (∑ j ∈ Finset.range n,(n.choose (j+1):ℝ))*C^2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := hb (j+1) (by omega) x
    have h2 := hb (n-(j+1)+1) (by omega) x
    have hh := mul_le_mul h1 h2 (abs_nonneg _) hC
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ (n.choose (j+1):ℝ) by positivity)
    nlinarith
  simpa only [add_comm] using add_le_add hrem hlead

lemma iteratedDeriv_finiteBurgersSource_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i n : ℕ)
    {C D t : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hcoef : finiteCoeff c h N i t ≤ D)
    (hb : ∀ j ≤ n, ∀ x, |iteratedDeriv j (deriv (finiteValue c h f N i t)) x| ≤ C) (x : ℝ) :
    |iteratedDeriv n (finiteBurgersSource c h f N i t) x| ≤
      D*|deriv (iteratedDeriv n (deriv (finiteValue c h f N i t))) x|+
        D*(∑ j ∈ Finset.range n,(n.choose (j+1):ℝ))*C^2 := by
  have hUnn : 0 ≤ finiteCoeff c h N i t := by
    obtain ⟨K,hK⟩ := finiteCoeff_bounds c h N i; exact (hK t).1
  have hU1 (z : ℝ) : |deriv (finiteValue c h f N i t) z| ≤ 1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := z) (finiteValue_lipschitz hLip c h N i t)
  have hbnd := burgers_source_derivative_bound
    (finiteValue_regular hf hLip c h N i t).deriv_bounded hC hU1 n hb x
  change |iteratedDeriv n (fun z => finiteCoeff c h N i t*
    (deriv (finiteValue c h f N i t) z*deriv (deriv (finiteValue c h f N i t)) z)) x| ≤ _
  rw [iteratedDeriv_const_mul_field,abs_mul,abs_of_nonneg hUnn]
  have hm := mul_le_mul hcoef hbnd (abs_nonneg _) hD
  apply hm.trans_eq
  simp only [iteratedDeriv_succ]
  ring

end ZeroTemperatureSK.Heat

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.SmoothingStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Heat
open ZeroTemperatureSK.Smoothing

lemma exists_smoothing_step {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ/2 ∧
      8*kernelConstant*D*Real.sqrt η ≤ 1/2 := by
  have hκ := kernelConstant_nonneg
  let q : ℝ := 1/(16*(kernelConstant*D+1))
  have hq : 0 < q := by dsimp [q]; positivity
  let η := min (δ/2) (q^2)
  have hη : 0 < η := lt_min (by positivity) (sq_pos_of_pos hq)
  refine ⟨η,hη,min_le_left _ _,?_⟩
  have hs : Real.sqrt η ≤ q := Real.sqrt_le_iff.mpr ⟨hq.le,min_le_right _ _⟩
  calc
    8*kernelConstant*D*Real.sqrt η ≤ 8*kernelConstant*D*q :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (8*kernelConstant*D)/(16*(kernelConstant*D+1)) := by dsimp [q]; ring
    _ ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)

theorem finiteGradient_uniform_smoothing (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ℝ → ℝ), RegularDatum f → LipschitzWith 1 f →
      ∀ (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (L : ℝ), 0 ≤ L →
      L+δ ≤ (N:ℝ)*h →
      (∀ s ∈ Icc (0:ℝ) (L+δ), finiteCoeff c h N i s ≤ D) →
      ∀ j ≤ m, ∀ t ∈ Icc (0:ℝ) L, ∀ x : ℝ,
        |iteratedDeriv j (deriv (finiteValue c h f N i t)) x| ≤ C := by
  induction m with
  | zero =>
    intro δ hδ
    refine ⟨1,by positivity,?_⟩
    intro f hf hLip c h N i L hL hhor hcoef j hj t ht x
    have hj0 : j = 0 := by omega
    subst j
    simpa only [iteratedDeriv_zero,Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) (finiteValue_lipschitz hLip c h N i t)
  | succ m ih =>
    intro δ hδ
    obtain ⟨C,hC,hbounds⟩ := ih (δ/2) (by positivity)
    obtain ⟨η,hη,hηδ,hηsmall⟩ := exists_smoothing_step hD hδ
    let R : ℝ := D*(∑ j ∈ Finset.range m,(m.choose (j+1):ℝ))*C^2
    have hR : 0 ≤ R := by dsimp [R]; positivity
    let K : ℝ := 2*kernelConstant*(C+2*R*η)/Real.sqrt η
    have hκ := kernelConstant_nonneg
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨max C K,le_max_of_le_left hC,?_⟩
    intro f hf hLip c h N i L hL hhor hcoef j hj t ht x
    have hlow : ∀ k ≤ m, ∀ s ∈ Icc (0:ℝ) (L+δ/2), ∀ z : ℝ,
        |iteratedDeriv k (deriv (finiteValue c h f N i s)) z| ≤ C := by
      apply hbounds f hf hLip c h N i (L+δ/2) (by positivity)
      · linarith
      · intro s hs
        apply hcoef s
        constructor
        · exact hs.1
        · linarith [hs.2]
    by_cases hjm : j ≤ m
    · exact (hlow j hjm t ⟨ht.1,by linarith [ht.2]⟩ x).trans (le_max_left _ _)
    have hje : j = m+1 := by omega
    subst j
    let V : ℝ → ℝ → ℝ := fun r => iteratedDeriv m (deriv (finiteValue c h f N i r))
    let G : ℝ → ℝ → ℝ := fun r => iteratedDeriv m (finiteBurgersSource c h f N i r)
    have hU := finiteGradient_family hf hLip c h N i
    have hS := finiteBurgersSource_family hf hLip c h N i
    have hV : BoundedSmoothFamily V := hU.iteratedDeriv m
    have hG : BoundedSmoothFamily G := hS.iteratedDeriv m
    obtain ⟨A₀,hA₀⟩ := hG.bound
    obtain ⟨B₀,hB₀⟩ := hG.deriv.bound
    obtain ⟨C₀,hC₀⟩ := hV.deriv.bound
    have htb : t < t+η := by linarith
    have hbL : t+η ≤ L+δ/2 := by linarith [ht.2]
    have hbhor : t+η ≤ (N:ℝ)*h := by linarith
    have hterminal (z : ℝ) : |V (t+η) z| ≤ C :=
      hlow m le_rfl (t+η) ⟨by linarith [ht.1],hbL⟩ z
    have hsource (r : ℝ) (hr : r ∈ Icc t (t+η)) (z : ℝ) :
        |G r z| ≤ D*|deriv (V r) z|+R := by
      apply iteratedDeriv_finiteBurgersSource_bound hf hLip c h N i m hC hD
      · apply hcoef r
        exact ⟨ht.1.trans hr.1,by linarith [hr.2]⟩
      · intro k hk y
        exact hlow k hk r ⟨ht.1.trans hr.1,hr.2.trans hbL⟩ y
    have hmild (r : ℝ) (hr : r ∈ Ico t (t+η)) (z : ℝ) :
        V r z = varianceHeat (t+η-r) (V (t+η)) z+
          ∫ s in r..t+η, varianceHeat (s-r) (G s) z := by
      exact iteratedDeriv_mild hU hS (finiteGradient_mild hf hLip c h N i
        (ht.1.trans hr.1) hr.2.le hbhor) m z
    have hshort : 8*kernelConstant*D*Real.sqrt (t+η-t) ≤ 1/2 := by
      simpa only [add_sub_cancel_left] using hηsmall
    have hbound := uniform_gradient_bound_of_mild htb hC hD hR
      (hV.regular (t+η)) hG.measurable hG.regular hA₀ hB₀
      (fun r _ z => hC₀ r z) hterminal hsource hmild hshort x
    apply (show |iteratedDeriv (m+1) (deriv (finiteValue c h f N i t)) x| ≤ K from ?_).trans
      (le_max_right _ _)
    simpa only [V,K,iteratedDeriv_succ,add_sub_cancel_left] using hbound

end ZeroTemperatureSK.Heat

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def approxValue (γ : OrderParameter) (n : ℕ) : ℝ → ℝ → ℝ :=
  finiteValue (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0

def approxError (γ : OrderParameter) (n : ℕ) : ℝ :=
  Real.log 2 / ((n+1:ℕ):ℝ)+(3/2:ℝ)*∫ s in (0:ℝ)..1, |approxGamma γ n s-extend γ.val s|

lemma approxError_limit (γ : OrderParameter) : Tendsto (approxError γ) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.log 2 / ((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [approxMesh,NNReal.coe_inv,NNReal.coe_natCast,mul_zero,div_eq_mul_inv] using
      tendsto_const_nhds.mul approxMesh_limit (a := Real.log 2)
  have hi := tendsto_const_nhds.mul (approxGamma_L1 γ) (a := (3/2:ℝ))
  have h := hh.add hi
  unfold approxError
  convert h using 1 <;> try rfl
  simp only [mul_zero,add_zero]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma approxValue_error (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |approxValue γ n t x-value W γ t x| ≤ approxError γ n := by
  apply finiteValue_control_error W γ _ _ _ (approxMesh_horizon n)
    (regularDatum_softAbs (by positivity)) (softAbs_lipschitz (by positivity)) _ ht0 ht1 x
  intro z
  have hh := softAbs_bounds (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity) z
  rw [abs_of_nonneg hh.1]
  exact hh.2

lemma approxValue_uniform (W : BrownianSystem Ω) (γ : OrderParameter) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => approxValue γ n p.1 p.2)
      (fun p => value W γ p.1 p.2) atTop (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(approxError_limit γ).eventually (gt_mem_nhds hε)] with n hn p hp
  rw [Real.dist_eq,abs_sub_comm]
  exact (approxValue_error W γ n hp.1.1 hp.1.2 p.2).trans_lt hn

lemma approxValue_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoUniformly (fun n => approxValue γ n t) (value W γ t) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(approxError_limit γ).eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (approxValue_error W γ n ht0 ht1 x).trans_lt hn

lemma approxValue_regular (γ : OrderParameter) (n : ℕ) (t : ℝ) :
    RegularDatum (approxValue γ n t) :=
  finiteValue_regular (regularDatum_softAbs (by positivity))
    (softAbs_lipschitz (by positivity)) _ _ _ _ _

lemma approxValue_uniform_derivative_bounds (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv (m+1) (approxValue γ n t) x| ≤ C := by
  let δ := (1-T)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : T+δ ∈ Ico (0:ℝ) 1 := by dsimp [δ]; constructor <;> linarith
  let D := γ.val ⟨T+δ,hB⟩
  obtain ⟨C,hC,hbound⟩ := finiteGradient_uniform_smoothing m D (γ.nonneg _) δ hδ
  refine ⟨C,hC,fun n t ht x => ?_⟩
  have hc : ∀ s ∈ Icc (0:ℝ) (T+δ),
      finiteCoeff (approxCoeff γ n) (approxMesh n) (n+1) 0 s ≤ D := by
    intro s hs
    have hmem : s ∈ Ico (0:ℝ) 1 := ⟨hs.1,hs.2.trans_lt hB.2⟩
    exact (approxGamma_bounds γ n ⟨s,hmem⟩).2.trans (γ.monotone hs.2)
  have hh := hbound _ (regularDatum_softAbs (show ((n+1:ℕ):ℝ) ≠ 0 by positivity))
    (softAbs_lipschitz (by positivity)) (approxCoeff γ n) (approxMesh n) (n+1) 0 T hT0
    (by rw [approxMesh_horizon]; exact hB.2.le) hc m le_rfl t ht x
  simpa only [approxValue,iteratedDeriv_succ'] using hh

theorem value_contDiff (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ContDiff ℝ ∞ (value W γ t) := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (approxValue_regular γ n t).smooth) _
    (approxValue_uniform_spatial W γ ht0 ht1.le)).1
  intro m
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ ht0 ht1 (m+1)
  exact ⟨C,hC,fun n x => hb n t ⟨ht0,le_rfl⟩ x⟩

lemma approxValue_derivative_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (m : ℕ) :
    TendstoUniformly (fun n => iteratedDeriv m (approxValue γ n t))
      (iteratedDeriv m (value W γ t)) atTop := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (approxValue_regular γ n t).smooth) _
    (approxValue_uniform_spatial W γ ht0 ht1.le)).2 m
  intro j
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ ht0 ht1 (j+1)
  exact ⟨C,hC,fun n x => hb n t ⟨ht0,le_rfl⟩ x⟩

theorem value_uniform_derivative_bounds (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv (m+1) (value W γ t) x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ hT0 hT1 m
  refine ⟨C,hC,fun t ht x => ?_⟩
  exact iteratedDeriv_limit_bound (m+1)
    (approxValue_derivative_uniform_spatial W γ ht.1 (ht.2.trans_lt hT1) (m+1))
    (fun n x => hb n t ht x) x

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.GaussianBackwardShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def backwardBoundary (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) : ℝ → ℝ :=
  cascade c h f (N-i) i

def forwardBoundary (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ => -(c 0:ℝ)*backwardBoundary c h f N 0 0
  | i+1 => fun x => (if i=0 then
      -(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))-(c 0:ℝ)*backwardBoundary c h f N 0 0
      else forwardCorrection ((i:ℝ)*h) (forwardBoundary c h f N i) h x)-
      ((c (i+1):ℝ)-(c i:ℝ))*backwardBoundary c h f N (i+1) x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.TiltedBackward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def tiltedRate (c : ℝ) (f g : ℝ → ℝ) (t x : ℝ) :=
  (1/2:ℝ)*deriv (deriv (varianceTilted c t f g)) x+
    c*deriv (varianceLogHeat c t f) x*deriv (varianceTilted c t f g) x

def tiltedBackward (c T : ℝ) (f g : ℝ → ℝ) (t x : ℝ) := varianceTilted c (T-t) f g x

def tiltedBackwardRate (c T : ℝ) (f g : ℝ → ℝ) (t x : ℝ) := -tiltedRate c f g (T-t) x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.FiniteContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma finiteValue_time_bound {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ L : ℝ≥0, ∀ r ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ s ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ x,
      |finiteValue c h f N i r x-finiteValue c h f N i s x| ≤ (L:ℝ)*|r-s| := by
  induction N generalizing i with
  | zero => exact ⟨0,by simp [finiteValue]⟩
  | succ N ih =>
    obtain ⟨K,hK⟩ := ih (i+1)
    obtain ⟨L,hL⟩ := backward_joint_bound (cascade_regular hf hLip c h N (i+1))
      (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg (h:ℝ)
    have hhead (r s : ℝ) (hr : r ∈ Icc 0 (h:ℝ)) (hs : s ∈ Icc 0 (h:ℝ)) (x : ℝ) :
        |finiteValue c h f (N+1) i r x-finiteValue c h f (N+1) i s x| ≤ (L:ℝ)*|r-s| := by
      rw [finiteValue_head f c h N i hr.2,finiteValue_head f c h N i hs.2]
      simpa only [sub_self,abs_zero,add_zero] using hL r hr s hs x x
    have htail (r s : ℝ) (hr : r ∈ Icc (h:ℝ) (((N+1:ℕ):ℝ)*h))
        (hs : s ∈ Icc (h:ℝ) (((N+1:ℕ):ℝ)*h)) (x : ℝ) :
        |finiteValue c h f (N+1) i r x-finiteValue c h f (N+1) i s x| ≤ (K:ℝ)*|r-s| := by
      rw [finiteValue_tail_of_le hf hLip c h N i hr.1,finiteValue_tail_of_le hf hLip c h N i hs.1]
      have hr' : r-h ∈ Icc (0:ℝ) ((N:ℝ)*h) := by
        constructor
        · exact sub_nonneg.mpr hr.1
        · have hh := hr.2; push_cast at hh; nlinarith
      have hs' : s-h ∈ Icc (0:ℝ) ((N:ℝ)*h) := by
        constructor
        · exact sub_nonneg.mpr hs.1
        · have hh := hs.2; push_cast at hh; nlinarith
      simpa only [sub_sub_sub_cancel_right] using hK (r-h) hr' (s-h) hs' x
    refine ⟨L+K,?_⟩
    have hsum (A : ℝ) (hA : 0 ≤ A) : (L:ℝ)*A ≤ ((L+K:ℝ≥0):ℝ)*A ∧
        (K:ℝ)*A ≤ ((L+K:ℝ≥0):ℝ)*A := by
      simp only [NNReal.coe_add]
      constructor <;> nlinarith [L.coe_nonneg,K.coe_nonneg]
    have hhN : (h:ℝ) ≤ ((N+1:ℕ):ℝ)*h := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) h.coe_nonneg]
    have hord (r s : ℝ) (hr : r ∈ Icc (0:ℝ) (((N+1:ℕ):ℝ)*h))
        (hs : s ∈ Icc (0:ℝ) (((N+1:ℕ):ℝ)*h)) (hrs : r ≤ s) (x : ℝ) :
        |finiteValue c h f (N+1) i r x-finiteValue c h f (N+1) i s x| ≤ ((L+K:ℝ≥0):ℝ)*|r-s| := by
      by_cases hsh : s ≤ h
      · exact (hhead r s ⟨hr.1,hrs.trans hsh⟩ ⟨hs.1,hsh⟩ x).trans (hsum _ (abs_nonneg _)).1
      by_cases hhr : (h:ℝ) ≤ r
      · exact (htail r s ⟨hhr,hr.2⟩ ⟨hhr.trans hrs,hs.2⟩ x).trans (hsum _ (abs_nonneg _)).2
      have hrh : r ≤ h := (lt_of_not_ge hhr).le
      have hhs : (h:ℝ) ≤ s := (lt_of_not_ge hsh).le
      have ha := hhead r h ⟨hr.1,hrh⟩ ⟨h.coe_nonneg,le_rfl⟩ x
      have hb := htail h s ⟨le_rfl,hhN⟩ ⟨hhs,hs.2⟩ x
      have ht := abs_sub_le (finiteValue c h f (N+1) i r x)
        (finiteValue c h f (N+1) i h x) (finiteValue c h f (N+1) i s x)
      rw [abs_of_nonpos (sub_nonpos.mpr hrh)] at ha
      rw [abs_of_nonpos (sub_nonpos.mpr hhs)] at hb
      rw [abs_of_nonpos (sub_nonpos.mpr hrs),NNReal.coe_add]
      nlinarith [mul_nonneg L.coe_nonneg (sub_nonneg.mpr hhs),
        mul_nonneg K.coe_nonneg (sub_nonneg.mpr hrh)]
    intro r hr s hs x
    rcases le_total r s with hrs|hsr
    · exact hord r s hr hs hrs x
    · simpa only [abs_sub_comm] using hord s r hs hr hsr x

lemma finiteValue_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ L : ℝ≥0, ∀ r ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ s ∈ Icc (0:ℝ) ((N:ℝ)*h), ∀ x y,
      |finiteValue c h f N i r x-finiteValue c h f N i s y| ≤ (L:ℝ)*(|r-s|+|x-y|) := by
  obtain ⟨L,hL⟩ := finiteValue_time_bound hf hLip c h N i
  refine ⟨L+1,fun r hr s hs x y => ?_⟩
  have ht := hL r hr s hs x
  have hl := (finiteValue_lipschitz hLip c h N i s).dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
  have htri := abs_sub_le (finiteValue c h f N i r x) (finiteValue c h f N i s x)
    (finiteValue c h f N i s y)
  simp only [NNReal.coe_add,NNReal.coe_one]
  nlinarith [mul_nonneg L.coe_nonneg (abs_nonneg (x-y)),abs_nonneg (r-s)]

lemma finiteValue_continuousOn {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => finiteValue c h f N i p.1 p.2)
      (Icc (0:ℝ) ((N:ℝ)*h) ×ˢ Set.univ) := by
  obtain ⟨L,hL⟩ := finiteValue_joint_bound hf hLip c h N i
  exact continuousOn_of_joint_bound hL

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def finiteRate (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) : ℝ :=
  -(1/2:ℝ)*deriv (deriv (finiteValue c h f N i t)) x-(1/2:ℝ)*finiteSource c h f N i t x

lemma measurable_finiteRate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (fun p : ℝ × ℝ => finiteRate c h f N i p.1 p.2) := by
  exact (measurable_const.mul (finiteGradient_family hf hLip c h N i).deriv.measurable).sub
    (measurable_const.mul (measurable_finiteSource hf hLip c h N i))

lemma finiteRate_bounded {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t x, |finiteRate c h f N i t x| ≤ C := by
  obtain ⟨A,hA⟩ := (finiteGradient_family hf hLip c h N i).deriv.bound
  obtain ⟨B,hB⟩ := finiteSource_bounded hLip c h N i
  refine ⟨A+B,fun t x => ?_⟩
  have ha := hA t x
  have hb := hB t x
  unfold finiteRate
  refine (abs_sub _ _).trans ?_
  simp only [abs_mul,abs_neg,abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num),NNReal.coe_add]
  nlinarith [abs_nonneg (deriv (deriv (finiteValue c h f N i t)) x),
    abs_nonneg (finiteSource c h f N i t x)]

lemma intervalIntegrable_finiteRate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (a b x : ℝ) :
    IntervalIntegrable (fun t => finiteRate c h f N i t x) volume a b := by
  obtain ⟨C,hC⟩ := finiteRate_bounded hf hLip c h N i
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun
    ((measurable_finiteRate hf hLip c h N i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg] using hC t x

lemma finiteRate_head {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) h) :
    finiteRate c h f (N+1) i t = backwardRate (c i) h (cascade c h f N (i+1)) t := by
  funext x
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hd,hJ,hE⟩ :=
    (backward_verificationData (cascade_regular hf hLip c h N (i+1))
      (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg (h:ℝ)).bounds
  have he := hE t ht x
  rw [finiteRate,finiteSource_head f c h N i ht.2,finiteValue_head f c h N i ht.2]
  linarith

lemma finiteRate_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) < t) : finiteRate c h f (N+1) i t = finiteRate c h f N (i+1) (t-h) := by
  funext x
  rw [finiteRate,finiteValue_tail f c h N i ht,finiteSource_tail f c h N i ht]
  rfl

lemma integral_finiteRate_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    {a b : ℝ} (ha : (h:ℝ) ≤ a) (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, finiteRate c h f (N+1) i t x) =
      ∫ t in a-h..b-h, finiteRate c h f N (i+1) t x := by
  rw [← intervalIntegral.integral_comp_sub_right (f := fun t => finiteRate c h f N (i+1) t x) (h:ℝ)]
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  dsimp only
  rw [finiteRate_tail f c h N i (ha.trans_lt ht.1)]

lemma backward_integral_rate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    {c : ℝ} (hc : 0 ≤ c) {a b T : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    (∫ t in a..b, backwardRate c T f t x) = backward c T f b x-backward c T f a x := by
  obtain ⟨C₂,C₃,Ct,L,h₂,h₃,hm,hCt,hd,hJ,hE⟩ := (backward_verificationData hf hLip hc T).bounds
  have hcont : ContinuousOn (fun t => backward c T f t x) (Icc a b) := by
    intro t ht
    exact (hd t ⟨ha.trans ht.1,ht.2.trans hb⟩ x).continuousWithinAt.mono
      (Icc_subset_Icc ha hb)
  have hrate : ContinuousOn (fun t => backwardRate c T f t x) (Icc a b) := by
    apply ((continuousOn_of_joint_bound hJ).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht,mem_univ _⟩)).mono
      (Icc_subset_Icc ha hb)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont _
    (hrate.intervalIntegrable_of_Icc hab)
  intro t ht
  exact (hd t ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩ x).hasDerivAt
    (Icc_mem_nhds (ha.trans_lt ht.1) (ht.2.trans_le hb))

theorem finiteValue_integral_rate {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (N:ℝ)*h) (x : ℝ) :
    (∫ t in a..b, finiteRate c h f N i t x) = finiteValue c h f N i b x-finiteValue c h f N i a x := by
  induction N generalizing i a b with
  | zero =>
    have hb0 : b = 0 := by simp only [Nat.cast_zero,zero_mul] at hb; linarith
    have ha0 : a = 0 := by linarith
    simp only [ha0,hb0,intervalIntegral.integral_same,sub_self]
  | succ N ih =>
    have hhead {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ h) :
        (∫ t in a..b, finiteRate c h f (N+1) i t x) =
          finiteValue c h f (N+1) i b x-finiteValue c h f (N+1) i a x := by
      rw [finiteValue_head f c h N i hb,finiteValue_head f c h N i (hab.trans hb)]
      have hi : (∫ t in a..b, finiteRate c h f (N+1) i t x) =
          (∫ t in a..b, backwardRate (c i) h (cascade c h f N (i+1)) t x) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro t ht
        dsimp only
        rw [finiteRate_head hf hLip c h N i ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩]
      rw [hi]
      exact backward_integral_rate (cascade_regular hf hLip c h N (i+1))
        (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg ha hab hb x
    have htail {a b : ℝ} (ha : (h:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (((N+1:ℕ):ℝ)*h)) :
        (∫ t in a..b, finiteRate c h f (N+1) i t x) =
          finiteValue c h f (N+1) i b x-finiteValue c h f (N+1) i a x := by
      rw [integral_finiteRate_tail f c h N i ha hab x,
        finiteValue_tail_of_le hf hLip c h N i (ha.trans hab),
        finiteValue_tail_of_le hf hLip c h N i ha]
      apply ih (i+1) (sub_nonneg.mpr ha) (by linarith)
      push_cast at hb
      nlinarith
    by_cases hbh : b ≤ h
    · exact hhead ha hab hbh
    by_cases hah : (h:ℝ) ≤ a
    · exact htail hah hab hb
    have hah' : a ≤ h := (lt_of_not_ge hah).le
    have hhb : (h:ℝ) ≤ b := (lt_of_not_ge hbh).le
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_finiteRate hf hLip c h (N+1) i a h x)
      (intervalIntegrable_finiteRate hf hLip c h (N+1) i h b x),
      hhead ha hah' le_rfl,htail le_rfl hhb hb]
    ring

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.PicardDiffusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto

structure BoundedLipschitzDrift where
  f : ℝ → ℝ → ℝ
  bound : ℝ≥0
  lip : ℝ≥0
  measurable : Measurable (fun p : ℝ × ℝ => f p.1 p.2)
  bounded : ∀ t x, |f t x| ≤ bound
  lipschitz : ∀ t, LipschitzWith lip (f t)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def timePrimitive (α : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0:ℝ)..(t:ℝ), α (Real.toNNReal s) ω

namespace BoundedLipschitzDrift

variable (b : BoundedLipschitzDrift)

def action (B Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := b.f t (B t ω+Y t ω)

def correctionIter (b : BoundedLipschitzDrift) (B : ℝ≥0 → Ω → ℝ) : ℕ → ℝ≥0 → Ω → ℝ
  | 0 => fun _ _ => 0
  | n+1 => timePrimitive (b.action B (correctionIter b B n))

def rate : ℝ := 2*(b.lip:ℝ)+1

def correction (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  atTop.limUnder (fun n => b.correctionIter B n t ω)

def solution (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := B t ω+b.correction B t ω

end BoundedLipschitzDrift
end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.ProgressiveBrownian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

def leftMeshTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌊((n+1:ℕ):ℝ)*(t:ℝ)⌋₊:ℝ≥0)/((n+1:ℕ):ℝ≥0)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def BrownianSystem.progressiveVersion (W : BrownianSystem Ω) (t : ℝ≥0) (ξ : Ω) : ℝ :=
  atTop.limUnder (fun n => W.B (leftMeshTime n t) ξ)

def BrownianSystem.driver (W : BrownianSystem Ω) (t : ℝ≥0) (ξ : Ω) : ℝ :=
  W.progressiveVersion t ξ-W.progressiveVersion 0 ξ

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.GradientAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

lemma gradient_abs_le_one (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : |gradient W γ t x| ≤ 1 := by
  simpa only [gradient, Real.norm_eq_abs, NNReal.coe_one] using
    (norm_deriv_le_of_lipschitz (x₀ := x) (value_lipschitz W γ t ht))

lemma integral_weighted_difference_bound {g h a : ℝ → ℝ} (hg : Integrable g)
    (hh : Integrable h) (ha : Measurable a) (hbound : ∀ s, |a s| ≤ 1)
    (t : ℝ) (ht : t ≤ 1) :
    |(∫ s in t..1, g s*a s) - (∫ s in t..1, h s*a s)| ≤
      ∫ s in t..1, |g s-h s| := by
  have hg' : Integrable (fun s => g s*a s) := hg.mul_bdd ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hbound s))
  have hh' : Integrable (fun s => h s*a s) := hh.mul_bdd ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hbound s))
  rw [← intervalIntegral.integral_sub hg'.intervalIntegrable hh'.intervalIntegrable,
    ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ (hg.sub hh).abs.intervalIntegrable
  exact Filter.Eventually.of_forall (fun s _ => by
    simp only [Pi.sub_apply, Real.norm_eq_abs, ← sub_mul, abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg (g s-h s)))

lemma controlPayoff_coeff_le (W : BrownianSystem Ω) (γ η : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    controlPayoff W γ t x α ω ≤ controlPayoff W η t x α ω +
      (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
  have ha : Measurable (fun s : ℝ => α.val (Real.toNNReal (s-t)) ω) :=
    (α.measurable_elapsed t).comp measurable_prodMk_right
  have hd := integral_weighted_difference_bound γ.integrable η.integrable ha
    (fun s => α.bound _ _) t ht
  have hc := integral_weighted_difference_bound γ.integrable η.integrable (ha.pow_const 2)
    (fun s => by simpa only [abs_pow, one_pow, Function.comp_apply] using
      pow_le_pow_left₀ (abs_nonneg _) (α.bound (Real.toNNReal (s-t)) ω) 2) t ht
  have htri := abs_add_le
    (x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω)
    ((∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω) -
      ∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω)
  have heq : x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      (∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω) +
      ((∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω) -
      ∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω) =
      x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω := by ring
  rw [heq] at htri
  have hcost := neg_le_abs
    ((∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s-t)) ω)^2) -
      ∫ s in t..1, extend η.val s * (α.val (Real.toNNReal (s-t)) ω)^2)
  dsimp [controlPayoff]
  linarith

lemma value_coeff_le (W : BrownianSystem Ω) (γ η : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : value W γ t x ≤ value W η t x +
      (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
  let := W.isProbability
  unfold value
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨zeroControl W (Real.toNNReal t), rfl⟩⟩
  rintro _ ⟨α, rfl⟩
  calc
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤
        ∫ ω, (controlPayoff W η t x α ω +
          (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s|) ∂W.law :=
      integral_mono (controlPayoff_integrable W γ t x ht α)
        ((controlPayoff_integrable W η t x ht α).add (integrable_const _))
        (controlPayoff_coeff_le W γ η t x ht α)
    _ = (∫ ω, controlPayoff W η t x α ω ∂W.law) +
        (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
      rw [integral_add (controlPayoff_integrable W η t x ht α) (integrable_const _)]
      simp
    _ ≤ _ := add_le_add (expected_controlPayoff_le_value W η t x ht α) le_rfl

theorem value_coefficient_stability (W : BrownianSystem Ω) (γ η : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : |value W γ t x - value W η t x| ≤
      (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
  rw [abs_le]
  have h₁ := value_coeff_le W γ η t x ht
  have h₂ := value_coeff_le W η γ t x ht
  simp_rw [abs_sub_comm (extend η.val _) (extend γ.val _)] at h₂
  constructor <;> linarith

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.JointRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform
variable {Ω : Type*} [MeasurableSpace Ω]

lemma approxValue_continuousOn (γ : OrderParameter) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => approxValue γ n p.1 p.2) (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
  simpa only [approxValue,approxMesh_horizon] using finiteValue_continuousOn
    (regularDatum_softAbs (show ((n+1:ℕ):ℝ) ≠ 0 by positivity))
    (softAbs_lipschitz (show ((n+1:ℕ):ℝ) ≠ 0 by positivity)) (approxCoeff γ n) (approxMesh n) (n+1) 0

lemma value_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (fun p : ℝ × ℝ => value W γ p.1 p.2) (Icc (0:ℝ) 1 ×ˢ Set.univ) :=
  (approxValue_uniform W γ).continuousOn (Filter.Eventually.of_forall (approxValue_continuousOn γ)).frequently

theorem value_derivative_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv m (value W γ p.1) p.2)
      (Icc (0:ℝ) T ×ˢ Set.univ) := by
  induction m with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact (value_continuousOn W γ).mono
      (Set.prod_mono (Icc_subset_Icc le_rfl hT1.le) (Subset.refl _))
  | succ m ih =>
    obtain ⟨C,hC,hb⟩ := value_uniform_derivative_bounds W γ hT0 hT1 (m+1)
    have hh := continuousOn_deriv_family (S := Icc (0:ℝ) T)
      (f := fun t => iteratedDeriv m (value W γ t)) ih
      (fun t ht => (contDiff_iteratedDeriv_infty (value_contDiff W γ ht.1 (ht.2.trans_lt hT1)) m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hb)
    simpa only [iteratedDeriv_succ] using hh

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.CompactDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

def stripClamp (T t : ℝ) : ℝ := max 0 (min T t)

lemma stripClamp_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : stripClamp T t ∈ Icc (0:ℝ) T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩

lemma stripClamp_eq {T t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : stripClamp T t = t := by
  simp only [stripClamp,min_eq_right ht.2,max_eq_right ht.1]

lemma continuous_stripClamp (T : ℝ) : Continuous (stripClamp T) :=
  continuous_const.max (continuous_const.min continuous_id)

variable {Ω : Type*} [MeasurableSpace Ω]

def compactGradient (W : BrownianSystem Ω) (γ : OrderParameter) (T : ℝ) (t x : ℝ) : ℝ :=
  gradient W γ (stripClamp T t) x

def compactCoeff (γ : OrderParameter) (T t : ℝ) : ℝ := extend γ.val (stripClamp T t)

def compactDrift (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactCoeff γ T t*compactGradient W γ T t x

lemma compactGradient_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactGradient W γ T p.1 p.2) := by
  have hc := value_derivative_continuousOn W γ hT0 hT1 1
  simp only [iteratedDeriv_one] at hc
  apply continuousOn_univ.mp
  exact hc.comp (((continuous_stripClamp T).comp continuous_fst).prodMk continuous_snd).continuousOn
    (fun p _ => ⟨stripClamp_mem hT0 p.1,mem_univ _⟩)

lemma compactGradient_bound (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactGradient W γ T t x| ≤ 1 :=
  gradient_abs_le_one W γ _ x ((stripClamp_mem hT0 t).2.trans hT1.le)

lemma compactCoeff_measurable (γ : OrderParameter) (T : ℝ) : Measurable (compactCoeff γ T) :=
  γ.measurable_extend.comp (continuous_stripClamp T).measurable

lemma compactCoeff_bounds (γ : OrderParameter) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t : ℝ) :
    0 ≤ compactCoeff γ T t ∧ compactCoeff γ T t ≤ γ.val ⟨T,⟨hT0,hT1⟩⟩ := by
  have ht := stripClamp_mem hT0 t
  have hm : stripClamp T t ∈ Ico (0:ℝ) 1 := ⟨ht.1,ht.2.trans_lt hT1⟩
  simp only [compactCoeff,extend,dite_eq_left hm]
  exact ⟨γ.nonneg _,γ.monotone ht.2⟩

lemma compactDrift_measurable (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Measurable (fun p : ℝ × ℝ => compactDrift W γ T p.1 p.2) :=
  ((compactCoeff_measurable γ T).comp measurable_fst).mul
    (compactGradient_continuous W γ hT0 hT1).measurable

lemma compactDrift_bound (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactDrift W γ T t x| ≤ γ.val ⟨T,⟨hT0,hT1⟩⟩ := by
  have hc := compactCoeff_bounds γ hT0 hT1 t
  rw [compactDrift,abs_mul,abs_of_nonneg hc.1]
  exact (mul_le_of_le_one_right hc.1 (compactGradient_bound W γ hT0 hT1 t x)).trans hc.2

lemma compactGradient_lipschitz (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (compactGradient W γ T t) := by
  obtain ⟨C,hC,hb⟩ := value_uniform_derivative_bounds W γ hT0 hT1 1
  refine ⟨⟨C,hC⟩,fun t => ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le
  · change Differentiable ℝ (deriv (value W γ (stripClamp T t)))
    simpa only [iteratedDeriv_one] using (value_contDiff W γ (stripClamp_mem hT0 t).1
      ((stripClamp_mem hT0 t).2.trans_lt hT1)).differentiable_iteratedDeriv 1 (by simp)
  · intro x
    apply NNReal.coe_le_coe.mp
    change |deriv (deriv (value W γ (stripClamp T t))) x| ≤ C
    simpa only [iteratedDeriv_succ,
      iteratedDeriv_zero] using hb (stripClamp T t) (stripClamp_mem hT0 t) x

lemma compactDrift_lipschitz (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (compactDrift W γ T t) := by
  obtain ⟨L,hL⟩ := compactGradient_lipschitz W γ hT0 hT1
  let D : ℝ≥0 := ⟨γ.val ⟨T,⟨hT0,hT1⟩⟩,γ.nonneg _⟩
  refine ⟨D*L,fun t => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hg := (hL t).dist_le_mul x y
  have hc := compactCoeff_bounds γ hT0 hT1 t
  rw [Real.dist_eq,compactDrift,compactDrift,← mul_sub,abs_mul,abs_of_nonneg hc.1,
    NNReal.coe_mul,Real.dist_eq]
  simp only [Real.dist_eq] at hg
  exact (mul_le_mul_of_nonneg_left hg hc.1).trans (by
    change compactCoeff γ T t * ((L:ℝ) * |x-y|) ≤
      γ.val ⟨T,⟨hT0,hT1⟩⟩ * (L:ℝ) * |x-y|
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hc.2 (mul_nonneg L.coe_nonneg (abs_nonneg _)))

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto

def diffusionHorizon (n : ℕ) : ℝ := 1-1/((n+2:ℕ):ℝ)

lemma diffusionHorizon_mem (n : ℕ) : diffusionHorizon n ∈ Ico (0:ℝ) 1 := by
  have hd : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
  have hge : (1:ℝ) ≤ ((n+2:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ n+2)
  have hh : (1:ℝ)/((n+2:ℕ):ℝ) ≤ 1 := (div_le_one hd).mpr hge
  have hp : (0:ℝ) < 1/((n+2:ℕ):ℝ) := by positivity
  exact ⟨by unfold diffusionHorizon; linarith,by unfold diffusionHorizon; linarith⟩

def diffusionHorizonTime (n : ℕ) : Time := ⟨diffusionHorizon n,diffusionHorizon_mem n⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def stripDrift (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) : BoundedLipschitzDrift where
  f := compactDrift W γ T
  bound := ⟨γ.val T,γ.nonneg T⟩
  lip := (compactDrift_lipschitz W γ T.property.1 T.property.2).choose
  measurable := compactDrift_measurable W γ T.property.1 T.property.2
  bounded := compactDrift_bound W γ T.property.1 T.property.2
  lipschitz := (compactDrift_lipschitz W γ T.property.1 T.property.2).choose_spec

def localDiffusion (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  (stripDrift W γ (diffusionHorizonTime n)).solution W.driver

def rawDiffusion (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) : ℝ :=
  atTop.limUnder (fun n => localDiffusion W γ n t ω)

def beforeOneGradient (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if (t:ℝ) < 1 then gradient W γ t x else 0

def rawFeedback (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) : ℝ :=
  beforeOneGradient W γ t (rawDiffusion W γ t ω)

def diffusion (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) : ℝ :=
  W.driver t ω+∫ s in (0:ℝ)..(t:ℝ), extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Equation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def valueRate (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  -(1/2:ℝ)*curvature W γ t x-(1/2:ℝ)*extend γ.val t*(gradient W γ t x)^2

lemma approxRate_eq (γ : OrderParameter) (n : ℕ) (t x : ℝ) :
    finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x =
      -(1/2:ℝ)*iteratedDeriv 2 (approxValue γ n t) x-
        (1/2:ℝ)*approxGamma γ n t*(iteratedDeriv 1 (approxValue γ n t) x)^2 := by
  simp only [finiteRate,finiteSource,approxValue,approxGamma,iteratedDeriv_succ,
    iteratedDeriv_zero]
  ring

lemma approxRate_tendsto (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : ContinuousAt γ.val t) (x : ℝ) :
    Tendsto (fun n => finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) atTop (𝓝 (valueRate W γ t x)) := by
  have h₂ := (approxValue_derivative_uniform_spatial W γ t.property.1 t.property.2 2).tendsto_at x
  have h₁ := (approxValue_derivative_uniform_spatial W γ t.property.1 t.property.2 1).tendsto_at x
  have hc := approxGamma_tendsto γ t ht
  simp only [approxRate_eq]
  have he : extend γ.val t = γ.val t := by simp [extend,t.property]
  unfold valueRate curvature gradient
  rw [he]
  convert (tendsto_const_nhds.mul h₂ (a := -(1/2:ℝ))).sub
      ((tendsto_const_nhds.mul hc (a := (1/2:ℝ))).mul (h₁.pow 2)) using 1 <;> try rfl
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]

lemma approxRate_bounded_on (γ : OrderParameter) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ hT0 hT1 1
  let D := γ.val ⟨T,⟨hT0,hT1⟩⟩
  have hD : 0 ≤ D := γ.nonneg _
  refine ⟨C+D,add_nonneg hC hD,fun n t ht x => ?_⟩
  rw [approxRate_eq]
  have ha := hb n t ht x
  have hg : |iteratedDeriv 1 (approxValue γ n t) x| ≤ 1 := by
    rw [iteratedDeriv_one]
    exact norm_deriv_le_of_lipschitz (finiteValue_lipschitz
      (softAbs_lipschitz (show ((n+1:ℕ):ℝ) ≠ 0 by positivity)) _ _ _ _ _)
  have hc := approxGamma_bounds γ n (⟨t,⟨ht.1,ht.2.trans_lt hT1⟩⟩ : Time)
  have hcd : approxGamma γ n t ≤ D := hc.2.trans (γ.monotone ht.2)
  have hsq : |iteratedDeriv 1 (approxValue γ n t) x|^2 ≤ 1 := by
    nlinarith [abs_nonneg (iteratedDeriv 1 (approxValue γ n t) x)]
  have hc0 : 0 ≤ approxGamma γ n t := hc.1
  refine (abs_sub _ _).trans ?_
  simp only [abs_mul,abs_neg,abs_pow,
    abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num),abs_of_nonneg hc0]
  change |iteratedDeriv 2 (approxValue γ n t) x| ≤ C at ha
  nlinarith [mul_le_mul_of_nonneg_left hsq hc0]

lemma approxRate_integral_limit (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (x : ℝ) :
    Tendsto (fun n => ∫ t in a..b, finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) atTop (𝓝 (∫ t in a..b, valueRate W γ t x)) := by
  obtain ⟨C,hC,hbound⟩ := approxRate_bounded_on γ (ha.trans hab) hb
  have hm : ∀ n, AEStronglyMeasurable (fun t => finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) (volume.restrict (Ioc a b)) := by
    intro n
    exact ((measurable_finiteRate (regularDatum_softAbs (by positivity))
      (softAbs_lipschitz (by positivity)) _ _ _ _).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hdom : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x‖ ≤ C := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hbound n t ⟨ha.trans ht.1.le,ht.2⟩ x
  have hlim : ∀ᵐ t ∂volume.restrict (Ioc a b), Tendsto
      (fun n => finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x)
      atTop (𝓝 (valueRate W γ t x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (γ.ae_continuous).filter_mono (ae_mono Measure.restrict_le_self)] with t ht hc
    have hmem : t ∈ Ico (0:ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.trans_lt hb⟩
    exact approxRate_tendsto W γ ⟨t,hmem⟩ (hc hmem) x
  have hint : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_const (c := C)).1
  have hh := tendsto_integral_of_dominated_convergence (fun _ => C) hm hint hdom hlim
  simpa only [intervalIntegral.integral_of_le hab] using hh

theorem value_integral_rate (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (x : ℝ) :
    (∫ t in a..b, valueRate W γ t x) = value W γ b x-value W γ a x := by
  have hvb := (approxValue_uniform_spatial W γ (ha.trans hab) hb.le).tendsto_at x
  have hva := (approxValue_uniform_spatial W γ ha (hab.trans hb.le)).tendsto_at x
  have he (n : ℕ) : (∫ t in a..b, finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) = approxValue γ n b x-approxValue γ n a x := by
    exact finiteValue_integral_rate (regularDatum_softAbs (by positivity))
      (softAbs_lipschitz (by positivity)) _ _ _ _ ha hab (by rw [approxMesh_horizon]; exact hb.le) x
  exact tendsto_nhds_unique (approxRate_integral_limit W γ ha hab hb x)
    ((hvb.sub hva).congr (fun n => (he n).symm))

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactGradient_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    BoundedSmoothFamily (compactGradient W γ T) := by
  have hb (n : ℕ) : ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv n (compactGradient W γ T t) x| ≤ C := by
    obtain ⟨C,hC,hb⟩ := value_uniform_derivative_bounds W γ hT0 hT1 n
    refine ⟨⟨C,hC⟩,fun t x => ?_⟩
    change |iteratedDeriv n (deriv (value W γ (stripClamp T t))) x| ≤ C
    simpa only [iteratedDeriv_succ'] using hb (stripClamp T t) (stripClamp_mem hT0 t) x
  refine ⟨(compactGradient_continuous W γ hT0 hT1).measurable,fun t => ?_,hb⟩
  refine ⟨?_,fun n => ?_⟩
  · change ContDiff ℝ ∞ (deriv (value W γ (stripClamp T t)))
    exact (contDiff_infty_iff_deriv.mp (value_contDiff W γ (stripClamp_mem hT0 t).1
      ((stripClamp_mem hT0 t).2.trans_lt hT1))).2
  · obtain ⟨C,hC⟩ := hb n
    exact ⟨C,hC t⟩

def compactValueRate (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  valueRate W γ (stripClamp T t) x

lemma compactValueRate_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    BoundedSmoothFamily (compactValueRate W γ T) := by
  have hu := compactGradient_family W γ hT0 hT1
  have hc : BoundedSmoothFamily (fun t (_x : ℝ) => compactCoeff γ T t) := by
    apply BoundedSmoothFamily.timeConst (C := ⟨γ.val ⟨T,⟨hT0,hT1⟩⟩,γ.nonneg _⟩) (compactCoeff_measurable γ T)
    intro t
    rw [abs_of_nonneg (compactCoeff_bounds γ hT0 hT1 t).1]
    exact (compactCoeff_bounds γ hT0 hT1 t).2
  have hh := (hu.deriv.const_mul (-(1/2:ℝ))).add ((hc.mul (hu.mul hu)).const_mul (-(1/2:ℝ)))
  convert hh using 1 <;> try rfl
  funext t x
  change -(1/2:ℝ)*deriv (deriv (value W γ (stripClamp T t))) x-
    (1/2:ℝ)*extend γ.val (stripClamp T t)*(deriv (value W γ (stripClamp T t)) x)^2 =
      -(1/2:ℝ)*deriv (deriv (value W γ (stripClamp T t))) x+
      -(1/2:ℝ)*(extend γ.val (stripClamp T t)*
        (deriv (value W γ (stripClamp T t)) x*deriv (value W γ (stripClamp T t)) x))
  ring

lemma compactRate_integral_derivative (W : BrownianSystem Ω) (γ : OrderParameter)
    {T a b : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (m : ℕ) (x : ℝ) :
    (∫ t in a..b, iteratedDeriv m (compactValueRate W γ T t) x) =
      iteratedDeriv m (value W γ b) x-iteratedDeriv m (value W γ a) x := by
  have he : (fun z => ∫ t in a..b, compactValueRate W γ T t z) =
      (fun z => value W γ b z-value W γ a z) := by
    funext z
    rw [← value_integral_rate W γ ha hab (hb.trans_lt hT1) z]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp only [compactValueRate,stripClamp_eq ⟨ha.trans ht.1,ht.2.trans hb⟩]
  have hi := (compactValueRate_family W γ hT0 hT1).iteratedDeriv_integral m a b x
  rw [he,iteratedDeriv_fun_sub (n := m)
    ((value_contDiff W γ (ha.trans hab) (hb.trans_lt hT1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt)
    ((value_contDiff W γ ha (hab.trans_lt (hb.trans_lt hT1))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt)] at hi
  exact hi.symm

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.RightRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat

def SpatialRightContinuous (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ t x, ContinuousWithinAt (fun s => iteratedDeriv n (F s) x) (Ici t) t

lemma SpatialRightContinuous.deriv {F : ℝ → ℝ → ℝ} (hF : SpatialRightContinuous F) :
    SpatialRightContinuous (fun t => deriv (F t)) := by
  intro n t x
  simpa only [iteratedDeriv_succ'] using hF (n+1) t x

lemma SpatialRightContinuous.add {F G : ℝ → ℝ → ℝ}
    (hf : BoundedSmoothFamily F) (hg : BoundedSmoothFamily G)
    (hF : SpatialRightContinuous F) (hG : SpatialRightContinuous G) :
    SpatialRightContinuous (fun t x => F t x+G t x) := by
  intro n t x
  have he (s : ℝ) : iteratedDeriv n (fun x => F s x+G s x) x =
      iteratedDeriv n (F s) x+iteratedDeriv n (G s) x :=
    iteratedDeriv_fun_add ((hf.regular s).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      ((hg.regular s).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
  simp_rw [he]
  exact (hF n t x).add (hG n t x)

lemma SpatialRightContinuous.const_mul {F : ℝ → ℝ → ℝ}
    (hf : BoundedSmoothFamily F) (hF : SpatialRightContinuous F) (c : ℝ) :
    SpatialRightContinuous (fun t x => c*F t x) := by
  intro n t x
  simp_rw [iteratedDeriv_const_mul c ((hf.regular _).smooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  exact continuousWithinAt_const.mul (hF n t x)

lemma SpatialRightContinuous.mul {F G : ℝ → ℝ → ℝ}
    (hf : BoundedSmoothFamily F) (hg : BoundedSmoothFamily G)
    (hF : SpatialRightContinuous F) (hG : SpatialRightContinuous G) :
    SpatialRightContinuous (fun t x => F t x*G t x) := by
  intro n t x
  have he (s : ℝ) : iteratedDeriv n (fun x => F s x*G s x) x =
      ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*iteratedDeriv j (F s) x*iteratedDeriv (n-j) (G s) x :=
    iteratedDeriv_fun_mul ((hf.regular s).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      ((hg.regular s).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
  simp_rw [he]
  exact tendsto_finsetSum _ (fun j _ =>
    (continuousWithinAt_const.mul (hF j t x)).mul (hG (n-j) t x))

lemma SpatialRightContinuous.timeConst {c : ℝ → ℝ}
    (hc : ∀ t, ContinuousWithinAt c (Ici t) t) :
    SpatialRightContinuous (fun t (_x : ℝ) => c t) := by
  intro n t x
  cases n with
  | zero => exact hc t
  | succ n => simpa only [iteratedDeriv_const,Nat.succ_ne_zero,ite_false] using
      (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0:ℝ)) (Ici t) t)

lemma compactCoeff_rightContinuous (γ : OrderParameter) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℝ) : ContinuousWithinAt (compactCoeff γ T) (Ici t) t := by
  let g : ℝ → Time := fun s => ⟨stripClamp T s,⟨(stripClamp_mem hT0 s).1,
    (stripClamp_mem hT0 s).2.trans_lt hT1⟩⟩
  have hg : Continuous g := (continuous_stripClamp T).subtype_mk _
  have hm : MapsTo g (Ici t) (Ici (g t)) := by
    intro s hs
    change stripClamp T t ≤ stripClamp T s
    exact max_le_max_left _ (min_le_min_left _ hs)
  have hh := (γ.right_continuous (g t)).comp hg.continuousAt.continuousWithinAt hm
  have he : compactCoeff γ T = fun s => γ.val (g s) := by
    funext s
    exact extend_coe γ.val (g s)
  rw [he]
  exact hh

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactGradient_rightSmooth (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : SpatialRightContinuous (compactGradient W γ T) := by
  intro n t x
  have hc := value_derivative_continuousOn W γ hT0 hT1 (n+1)
  have hh : Continuous (fun s => iteratedDeriv (n+1) (value W γ (stripClamp T s)) x) := by
    have hg : ContinuousOn (fun s : ℝ => (stripClamp T s,x)) univ :=
      ((continuous_stripClamp T).prodMk continuous_const).continuousOn
    have hm : MapsTo (fun s : ℝ => (stripClamp T s,x)) univ (Icc (0:ℝ) T ×ˢ (univ : Set ℝ)) :=
      fun s _ => ⟨stripClamp_mem hT0 s,mem_univ _⟩
    have he : ContinuousOn
        ((fun p : ℝ × ℝ => iteratedDeriv (n+1) (value W γ p.1) p.2) ∘
          (fun s : ℝ => (stripClamp T s,x))) univ :=
      ContinuousOn.comp (f := fun s : ℝ => (stripClamp T s,x))
        (g := fun p : ℝ × ℝ => iteratedDeriv (n+1) (value W γ p.1) p.2) hc hg hm
    exact continuousOn_univ.mp he
  change ContinuousWithinAt (fun s => iteratedDeriv n (deriv (value W γ (stripClamp T s))) x) (Ici t) t
  simpa only [iteratedDeriv_succ'] using hh.continuousAt.continuousWithinAt

lemma compactValueRate_rightSmooth (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : SpatialRightContinuous (compactValueRate W γ T) := by
  have hu := compactGradient_family W γ hT0 hT1
  have hur := compactGradient_rightSmooth W γ hT0 hT1
  have hc : BoundedSmoothFamily (fun t (_x : ℝ) => compactCoeff γ T t) := by
    apply BoundedSmoothFamily.timeConst (C := ⟨γ.val ⟨T,⟨hT0,hT1⟩⟩,γ.nonneg _⟩) (compactCoeff_measurable γ T)
    intro t
    rw [abs_of_nonneg (compactCoeff_bounds γ hT0 hT1 t).1]
    exact (compactCoeff_bounds γ hT0 hT1 t).2
  have hcr := SpatialRightContinuous.timeConst (compactCoeff_rightContinuous γ hT0 hT1)
  have hh := SpatialRightContinuous.add (hu.deriv.const_mul (-(1/2:ℝ)))
    ((hc.mul (hu.mul hu)).const_mul (-(1/2:ℝ)))
    (SpatialRightContinuous.const_mul hu.deriv hur.deriv (-(1/2:ℝ)))
    (SpatialRightContinuous.const_mul (hc.mul (hu.mul hu))
      (SpatialRightContinuous.mul hc (hu.mul hu) hcr (SpatialRightContinuous.mul hu hu hur hur)) (-(1/2:ℝ)))
  convert hh using 1 <;> try rfl
  funext t x
  unfold compactValueRate valueRate compactGradient curvature gradient compactCoeff
  ring

theorem value_derivative_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    {T t : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ht0 : 0 ≤ t) (htT : t < T)
    (m : ℕ) (x : ℝ) :
    HasDerivWithinAt (fun s => iteratedDeriv m (value W γ s) x)
      (iteratedDeriv m (compactValueRate W γ T t) x) (Ioi t) t := by
  have hD := (compactValueRate_family W γ hT0 hT1).iteratedDeriv m
  have hi := intervalIntegral.integral_hasDerivWithinAt_right
    (a := t) (b := t) (s := Ici t) (t := Ioi t)
    (hD.intervalIntegrable x t t)
    ((hD.measurable.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.stronglyMeasurableAtFilter)
    ((compactValueRate_rightSmooth W γ hT0 hT1 m t x).mono Ioi_subset_Ici_self)
  have hh := (hi.mono Ioi_subset_Ici_self).const_add (iteratedDeriv m (value W γ t) x)
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
    rw [compactRate_integral_derivative W γ hT0 hT1 ht0 hs.le hsT.le m x]
    ring
  · simp

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.BoundedDiffusionProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

namespace BoundedLipschitzDrift
variable (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)

def pathDrift (t : ℝ) (ω : Ω) : ℝ :=
  b.f (Real.toNNReal t) (b.solution W.driver (Real.toNNReal t) ω)

def displacement (s t : ℝ) (ω : Ω) : ℝ := ∫ r in s..t, b.pathDrift W r ω

end BoundedLipschitzDrift
end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.TimeFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto

structure TimeField (T : ℝ) where
  f : ℝ → ℝ → ℝ
  d : ℝ → ℝ → ℝ
  smooth : BoundedSmoothFamily f
  rate_smooth : BoundedSmoothFamily d
  continuous : Continuous (fun p : ℝ × ℝ => f p.1 p.2)
  rate_right : ∀ t x, ContinuousWithinAt (fun s => d s x) (Ioi t) t
  time_deriv : ∀ t, 0 ≤ t → t < T → ∀ x,
    HasDerivWithinAt (fun s => f s x) (d t x) (Ioi t) t

namespace TimeField
variable {T : ℝ}

def add (F G : TimeField T) : TimeField T where
  f := fun t x => F.f t x+G.f t x
  d := fun t x => F.d t x+G.d t x
  smooth := F.smooth.add G.smooth
  rate_smooth := F.rate_smooth.add G.rate_smooth
  continuous := F.continuous.add G.continuous
  rate_right := fun t x => (F.rate_right t x).add (G.rate_right t x)
  time_deriv := fun t ht hT x => (F.time_deriv t ht hT x).add (G.time_deriv t ht hT x)

def const_mul (c : ℝ) (F : TimeField T) : TimeField T where
  f := fun t x => c*F.f t x
  d := fun t x => c*F.d t x
  smooth := F.smooth.const_mul c
  rate_smooth := F.rate_smooth.const_mul c
  continuous := continuous_const.mul F.continuous
  rate_right := fun t x => continuousWithinAt_const.mul (F.rate_right t x)
  time_deriv := fun t ht hT x => (F.time_deriv t ht hT x).const_mul c

def mul (F G : TimeField T) : TimeField T where
  f := fun t x => F.f t x*G.f t x
  d := fun t x => F.d t x*G.f t x+F.f t x*G.d t x
  smooth := F.smooth.mul G.smooth
  rate_smooth := (F.rate_smooth.mul G.smooth).add (F.smooth.mul G.rate_smooth)
  continuous := F.continuous.mul G.continuous
  rate_right := fun t x => ((F.rate_right t x).mul
    ((G.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.continuousWithinAt)).add
    (((F.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.continuousWithinAt).mul (G.rate_right t x))
  time_deriv := fun t ht hT x => (F.time_deriv t ht hT x).mul (G.time_deriv t ht hT x)

def generator (F : TimeField T) (b : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (F.f t) x*b t x+(1/2:ℝ)*deriv (deriv (F.f t)) x+F.d t x

variable {Ω : Type*} [MeasurableSpace Ω]

def expected (F : TimeField T) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω) (t : ℝ) : ℝ :=
  ∫ ξ, F.f t (b.solution W.driver (Real.toNNReal t) ξ) ∂W.law

end TimeField
end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.ValueDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def coefficientDistance (β γ : OrderParameter) : ℝ :=
  ∫ s in (0:ℝ)..1, |extend β.val s-extend γ.val s|

lemma coefficientDistance_nonneg (β γ : OrderParameter) : 0 ≤ coefficientDistance β γ :=
  intervalIntegral.integral_nonneg (by norm_num) (fun s _ => abs_nonneg _)

lemma value_difference_bound (W : BrownianSystem Ω) (β γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |value W β t x-value W γ t x| ≤ (3/2:ℝ)*coefficientDistance β γ := by
  apply (value_coefficient_stability W β γ t x ht1).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact intervalIntegral.integral_mono_interval ht0 ht1 le_rfl
    (Eventually.of_forall (fun s => abs_nonneg _)) ((β.integrable.sub γ.integrable).abs.intervalIntegrable)

def compactDifference (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  value W β (stripClamp T t) x-value W γ (stripClamp T t) x

def compactDifferenceRate (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactValueRate W β T t x-compactValueRate W γ T t x

lemma compactDifference_continuous (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactDifference W β γ T p.1 p.2) := by
  have hcl : ContinuousOn (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ :=
    (((continuous_stripClamp T).comp continuous_fst).prodMk continuous_snd).continuousOn
  have hm : MapsTo (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ
      (Icc (0:ℝ) T ×ˢ (univ : Set ℝ)) := fun p _ => ⟨stripClamp_mem hT0 p.1,mem_univ _⟩
  have hβ := (value_derivative_continuousOn W β hT0 hT1 0).comp hcl hm
  have hγ := (value_derivative_continuousOn W γ hT0 hT1 0).comp hcl hm
  exact continuousOn_univ.mp (hβ.sub hγ)

lemma compactDifference_deriv (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t : ℝ) :
    deriv (compactDifference W β γ T t)=fun x => compactGradient W β T t x-compactGradient W γ T t x := by
  funext x
  have hb := ((value_contDiff W β (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1)).differentiable (by simp) x).hasDerivAt
  have hg := ((value_contDiff W γ (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1)).differentiable (by simp) x).hasDerivAt
  exact (hb.sub hg).deriv

lemma compactDifference_family (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactDifference W β γ T) := by
  have hs (t : ℝ) : ContDiff ℝ ∞ (compactDifference W β γ T t) :=
    (value_contDiff W β (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1)).sub
      (value_contDiff W γ (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1))
  have hg : BoundedSmoothFamily (fun t x => compactGradient W β T t x-compactGradient W γ T t x) := by
    convert (compactGradient_family W β hT0 hT1).add ((compactGradient_family W γ hT0 hT1).const_mul (-1)) using 1 <;> try rfl
    funext t x;ring
  have hb (n : ℕ) : ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv n (compactDifference W β γ T t) x| ≤ C := by
    cases n with
    | zero =>
      refine ⟨⟨(3/2:ℝ)*coefficientDistance β γ,mul_nonneg (by norm_num) (coefficientDistance_nonneg β γ)⟩,?_⟩
      intro t x
      exact value_difference_bound W β γ (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans hT1.le) x
    | succ n =>
      obtain ⟨C,hC⟩ := hg.bounds n
      refine ⟨C,fun t x => ?_⟩
      rw [iteratedDeriv_succ',compactDifference_deriv W β γ hT0 hT1]
      exact hC t x
  exact ⟨(compactDifference_continuous W β γ hT0 hT1).measurable,
    fun t => ⟨hs t,fun n => (hb n).imp (fun C hC x => hC t x)⟩,hb⟩

lemma compactDifferenceRate_family (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactDifferenceRate W β γ T) := by
  convert (compactValueRate_family W β hT0 hT1).add ((compactValueRate_family W γ hT0 hT1).const_mul (-1)) using 1 <;> try rfl
  funext t x
  unfold compactDifferenceRate
  ring

def differenceField (W : BrownianSystem Ω) (β γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) : TimeField T where
  f := compactDifference W β γ T
  d := compactDifferenceRate W β γ T
  smooth := compactDifference_family W β γ hT0 hT1
  rate_smooth := compactDifferenceRate_family W β γ hT0 hT1
  continuous := compactDifference_continuous W β γ hT0 hT1
  rate_right := fun t x => ((compactValueRate_rightSmooth W β hT0 hT1 0 t x).mono Ioi_subset_Ici_self).sub
    ((compactValueRate_rightSmooth W γ hT0 hT1 0 t x).mono Ioi_subset_Ici_self)
  time_deriv := by
    intro t ht0 htT x
    have hd := (value_derivative_hasDerivWithinAt_right W β hT0 hT1 ht0 htT 0 x).sub
      (value_derivative_hasDerivWithinAt_right W γ hT0 hT1 ht0 htT 0 x)
    apply hd.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
      simp only [compactDifference,stripClamp_eq ⟨ht0.trans hs.le,hsT.le⟩,iteratedDeriv_zero,Pi.sub_apply]
    · simp only [compactDifference,stripClamp_eq ⟨ht0,htT.le⟩,iteratedDeriv_zero,Pi.sub_apply]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.Certificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ZeroTemperatureSK.Certificate
noncomputable section

abbrev A : ℝ := 1 / 13
abbrev C : ℝ := 53 / 24
abbrev k : ℝ := 19 / 16
abbrev T₀ : ℝ := 73 / 48
abbrev g₀ : ℝ := 2331 / 10000
abbrev h : ℝ := 87 / 2500
abbrev x₀ : ℝ := 4663 / 5000
abbrev y : ℝ := 6853 / 10000
abbrev m : ℝ := -1051 / 400
abbrev n₀ : ℝ := -1073 / 500

def Q (R K v b : ℝ) : ℝ := A * v * b + C * v ^ 2 + k * K * v - 2*k*R*b + T₀*R*v
def T (R v j : ℝ) : ℝ := g₀*R*v + h*j*v
def F₁ (R K v b j : ℝ) : ℝ :=
  b^2*(2*R*k-A*v) + b*(-2*K*k*v-R*g₀*v-2*R*T₀*v-2*C*v^2-h*j*v)
def F₂ (R K v b j : ℝ) : ℝ := x₀*v^2*j + y*v^3 + m*K*v^2 + n₀*R*v^2 - F₁ R K v b j

def P₀ (R v b j : ℝ) : ℝ := R*j*(b-7*v)^2
def P₁ (R v b B : ℝ) : ℝ := R*B*(b-7/3*v)^2
def P₂ (K v b : ℝ) : ℝ := K*v*(b-9/2*v)^2
def P₃ (R K v B : ℝ) : ℝ := v*B*(K+1/4*R-1/7*v)^2
def P₄ (R K v b : ℝ) : ℝ := (v*b-14/5*v^2-13/4*K*v+4/3*R*v)^2

def weightedSquares (R K v b B j : ℝ) : ℝ :=
  337/10000*P₀ R v b j + 183/2500*P₁ R v b B + 411/10000*P₂ K v b +
    11461/5000*P₃ R K v B + 647/10000*P₄ R K v b

def remainder (R K v B j : ℝ) : ℝ :=
  223/160000*R^2*v^2 + 4007/240000*R^2*v*B + 1097/120000*R^2*B^2 +
  83/80000*R*K*v^2 + 3343/24000*R*K*v*B + 16259/23400000*R*v^3 +
  30179/5460000*R*v^2*B + 26/625*R*v^2*j + 107/15000*R*v*B^2 +
  3/2500*R*v*B*j + 121/32500*R*B^3 + 11/10000*R*B^2*j +
  579/20000*K^2*v^2 + 207/2500*K^2*v*B + 911/975000*K*v^3 +
  349/420000*K*v^2*B + 5011/5000*K*v^2*j + 133/130000*K*v*B^2 +
  87/2500*K*v*B*j + 1661507/1521000000*v^4 +
  633799/621075000*v^3*B + 10657/1690000*v^2*B^2

def F₂R (_R _K v b _j : ℝ) : ℝ := n₀*v^2 - 2*k*b^2 + (g₀+2*T₀)*b*v
def F₂K (_R _K v b _j : ℝ) : ℝ := m*v^2 + 2*k*b*v
def F₂v (R K v b j : ℝ) : ℝ :=
  2*x₀*v*j + 3*y*v^2 + 2*m*K*v + 2*n₀*R*v + A*b^2 +
    b*(2*K*k + R*g₀ + 2*R*T₀ + 4*C*v + h*j)
def F₂b (R K v b j : ℝ) : ℝ := 2*Q R K v b + T R v j
def F₂j (_R _K v b _j : ℝ) : ℝ := x₀*v^2 + h*b*v

def DF₂ (R K v b j z L : ℝ) : ℝ :=
  (2*R*v)*F₂R R K v b j + (2*v*K+R*j)*F₂K R K v b j +
  (-R*b)*F₂v R K v b j + (-z-b*v)*F₂b R K v b j +
  (-j*v+K*b-L)*F₂j R K v b j

def WF₂ (R K v b j z L : ℝ) : ℝ := DF₂ R K v b j z L + (v+R-K)*F₂ R K v b j

open MeasureTheory Filter
open scoped Topology

end
end ZeroTemperatureSK.Certificate

end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.RatioJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def ratioWronskian (r s : ℝ → ℝ → ℝ) (t x : ℝ) :=
  r t x*deriv (s t) x-s t x*deriv (r t) x

def ratioWronskianRate (r s : ℝ → ℝ → ℝ) (t x : ℝ) :=
  -burgersRate r t x*deriv (s t) x+r t x*deriv (scoreRate s t) x-
    scoreRate s t x*deriv (r t) x+s t x*deriv (burgersRate r t) x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ReverseBurgers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure ReverseBurgers (r : ℝ → ℝ → ℝ) (H : ℝ) : Prop where
  family : BoundedSmoothFamily r
  continuous : ContinuousOn (fun p : ℝ × ℝ => r p.1 p.2) (Icc (0:ℝ) H ×ˢ univ)
  time_derivative : ∀ n t, 0 < t → t < H → ∀ x,
    HasDerivAt (fun u => iteratedDeriv n (r u) x) (-iteratedDeriv n (burgersRate r t) x) t

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.RatioComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def datumScore (a : ℝ) (L : ℝ → ℝ) (x : ℝ) := x/a-deriv L x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.FiniteForwardRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def backwardSegment (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) :=
  gaussianBurgers (c i) (backwardBoundary c h f N (i+1)) ((h:ℝ)-t) x

def boundaryRatio (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (x : ℝ) :=
  ratioWronskian (fun _ y => (c i:ℝ)*deriv (backwardBoundary c h f N i) y)
    (fun _ => datumScore ((i:ℝ)*h) (forwardBoundary c h f N i)) 0 x

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def certR (r : ℝ → ℝ) (x : ℝ) := (r x)^2
def certK (r s : ℝ → ℝ) (x : ℝ) := r x*s x
def certV (r : ℝ → ℝ) := deriv r
def certW (r : ℝ → ℝ) := iteratedDeriv 2 r
def certZ (r : ℝ → ℝ) := iteratedDeriv 3 r
def certB (r : ℝ → ℝ) (x : ℝ) := -certW r x/r x
def certJ (r s : ℝ → ℝ) (x : ℝ) := deriv s x-(s x/r x)*certV r x
def certL (r s : ℝ → ℝ) (x : ℝ) := -r x*iteratedDeriv 2 s x

def certFlux (r s ρ : ℝ → ℝ) (x : ℝ) :=
  r x*Certificate.F₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)*ρ x

def certDivergence (r s ρ : ℝ → ℝ) (x : ℝ) :=
  ρ x*Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
    (certZ r x) (certL r s x)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.GaussianDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def quotientExtension (g r : ℝ → ℝ) (x : ℝ) := dslope g 0 x/dslope r 0 x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.GaussianLogDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

def gaussianLogDensity (d : ℝ) (U : ℝ → ℝ) (x : ℝ) := Real.exp (-d*x^2+U x)

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def coercivePolynomial (r : ℝ → ℝ) (x : ℝ) :=
  (certZ r x)^2-12*certV r x*(certW r x)^2+6*(certV r x)^4

def quarticMoment (r : ℝ → ℝ) (x : ℝ) := (certV r x)^4

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.FiniteFeedback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma Heat.BoundedSmoothFamily.uniform_lipschitz {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (F t) := by
  obtain ⟨L,hL⟩ := hF.deriv.bound
  exact ⟨L,fun t => lipschitzWith_of_nnnorm_deriv_le
    ((hF.regular t).smooth.differentiable (by simp)) (fun x => hL t x)⟩

def Heat.BoundedSmoothFamily.toDrift {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) : BoundedLipschitzDrift where
  f := F
  bound := hF.bound.choose
  lip := hF.uniform_lipschitz.choose
  measurable := hF.measurable
  bounded := hF.bound.choose_spec
  lipschitz := hF.uniform_lipschitz.choose_spec

def rightCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | N+1, i, t => if t < h then c i else rightCoeff c h N (i+1) (t-h)

lemma rightCoeff_measurable (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : Measurable (rightCoeff c h N i) := by
  induction N generalizing i with
  | zero => exact measurable_const
  | succ N ih =>
    exact Measurable.ite (measurableSet_lt (f := id) (g := fun _ : ℝ => (h:ℝ)) measurable_id measurable_const)
      measurable_const ((ih (i+1)).comp (measurable_id.sub_const (h:ℝ)))

lemma rightCoeff_bounds (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t, 0 ≤ rightCoeff c h N i t ∧ rightCoeff c h N i t ≤ C := by
  induction N generalizing i with
  | zero => exact ⟨0,fun _ => ⟨le_rfl,le_rfl⟩⟩
  | succ N ih =>
    obtain ⟨C,hC⟩ := ih (i+1)
    refine ⟨c i+C,fun t => ?_⟩
    dsimp only [rightCoeff]
    split_ifs with ht
    · exact ⟨(c i).coe_nonneg,by simp only [NNReal.coe_add];linarith [C.coe_nonneg]⟩
    · exact ⟨(hC _).1,by simp only [NNReal.coe_add];linarith [(hC (t-h)).2,(c i).coe_nonneg]⟩

lemma rightCoeff_family (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (fun t (_ : ℝ) => rightCoeff c h N i t) := by
  obtain ⟨C,hC⟩ := rightCoeff_bounds c h N i
  exact BoundedSmoothFamily.timeConst (rightCoeff_measurable c h N i)
    (fun t => by simpa only [abs_of_nonneg (hC t).1] using (hC t).2)

def finiteFeedbackFun (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) :=
  rightCoeff c h N i t*deriv (finiteValue c h f N i t) x

lemma finiteFeedback_family {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : BoundedSmoothFamily (finiteFeedbackFun c h f N i) :=
  (rightCoeff_family c h N i).mul (finiteGradient_family hf hLip c h N i)

def finiteFeedback {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : BoundedLipschitzDrift :=
  (finiteFeedback_family hf hLip c h N i).toDrift

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.ParameterChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

def OrderParameter.chord (γ β : OrderParameter) (ε : ℝ) (hε : ε ∈ Icc (0:ℝ) 1) : OrderParameter where
  val := fun t => (1-ε)*γ.val t+ε*β.val t
  nonneg := fun t => add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (γ.nonneg t)) (mul_nonneg hε.1 (β.nonneg t))
  monotone := fun a b hab => add_le_add (mul_le_mul_of_nonneg_left (γ.monotone hab) (sub_nonneg.mpr hε.2))
    (mul_le_mul_of_nonneg_left (β.monotone hab) hε.1)
  right_continuous := fun t => ((γ.right_continuous t).const_mul (1-ε)).add ((β.right_continuous t).const_mul ε)
  integrable := by
    have he : extend (fun t => (1-ε)*γ.val t+ε*β.val t)=fun t => (1-ε)*extend γ.val t+ε*extend β.val t := by
      funext t
      by_cases ht : t ∈ Ico (0:ℝ) 1 <;> simp [extend,ht]
    rw [he]
    exact (γ.integrable.const_mul (1-ε)).add (β.integrable.const_mul ε)

def variationStep (n : ℕ) : ℝ := 1/((n:ℝ)+1)
lemma variationStep_pos (n : ℕ) : 0 < variationStep n := by unfold variationStep;positivity
lemma variationStep_mem (n : ℕ) : variationStep n ∈ Icc (0:ℝ) 1 := by
  refine ⟨(variationStep_pos n).le,?_⟩
  unfold variationStep
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
  norm_num

def perturbation (γ β : OrderParameter) (n : ℕ) : OrderParameter := γ.chord β (variationStep n) (variationStep_mem n)

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def positiveCoeff (γ : OrderParameter) (n j : ℕ) : ℝ≥0 :=
  approxCoeff γ n (min j n)+approxMesh n

def positiveGamma (γ : OrderParameter) (n : ℕ) : ℝ → ℝ :=
  finiteCoeff (positiveCoeff γ n) (approxMesh n) (n+1) 0

def positiveTerminal (γ : OrderParameter) (n : ℕ) : ℝ :=
  ((n+1:ℕ):ℝ)+(positiveCoeff γ n n:ℝ)

lemma positiveTerminal_pos (γ : OrderParameter) (n : ℕ) : 0 < positiveTerminal γ n := by
  unfold positiveTerminal;positivity

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.PositiveRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def positiveValue (γ : OrderParameter) (n : ℕ) : ℝ → ℝ → ℝ :=
  finiteValue (positiveCoeff γ n) (approxMesh n) (softAbs (positiveTerminal γ n)) (n+1) 0

def positiveError (γ : OrderParameter) (n : ℕ) : ℝ :=
  Real.log 2 / positiveTerminal γ n+(3/2:ℝ)*∫ s in (0:ℝ)..1, |positiveGamma γ n s-extend γ.val s|

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.CoerciveMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

def coerciveJetPolynomial (c A B C : ℝ) : ℝ := c^2*C^2-12*c^3*A*B^2+6*c^4*A^4

def quarticJetPolynomial (c A : ℝ) : ℝ := c^4*A^4

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

def sampleIndex (n : ℕ) (t : Time) : ℕ := ⌊(t:ℝ)/(approxMesh n:ℝ)⌋₊

def sampleNNTime (n : ℕ) (t : Time) : ℝ≥0 := (sampleIndex n t:ℝ≥0)*approxMesh n

lemma sampleNNTime_le (n : ℕ) (t : Time) : (sampleNNTime n t:ℝ) ≤ t := by
  have hh := Nat.floor_le (div_nonneg t.property.1 (approxMesh n).coe_nonneg)
  rw [le_div_iff₀ (by exact_mod_cast approxMesh_pos n)] at hh
  exact hh

def sampleTime (n : ℕ) (t : Time) : Time :=
  ⟨sampleNNTime n t,⟨(sampleNNTime n t).coe_nonneg,(sampleNNTime_le n t).trans_lt t.property.2⟩⟩

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.DensityHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

def heatKernel (t x : ℝ) := gaussianPDFReal 0 (Real.toNNReal t) x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.DensityFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

def finiteDensity (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (x : ℝ) : ℝ :=
  Real.exp ((c i:ℝ)*backwardBoundary c h f N i x-x^2/(2*((i:ℝ)*h))+
    forwardBoundary c h f N i x)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.SquareEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def compactSquare (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactGradient W γ T t x*compactGradient W γ T t x

def compactSquareRate (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  2*compactGradient W γ T t x*deriv (compactValueRate W γ T t) x

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactGradient_derivative_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv n (compactGradient W γ T p.1) p.2) := by
  change Continuous (fun p : ℝ × ℝ => iteratedDeriv n (deriv (value W γ (stripClamp T p.1))) p.2)
  simp only [← iteratedDeriv_succ']
  have hc := value_derivative_continuousOn W γ hT0 hT1 (n+1)
  have hg : ContinuousOn (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ :=
    (((continuous_stripClamp T).comp continuous_fst).prodMk continuous_snd).continuousOn
  have hm : MapsTo (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ
      (Icc (0:ℝ) T ×ˢ (univ : Set ℝ)) := fun p _ => ⟨stripClamp_mem hT0 p.1,mem_univ _⟩
  exact continuousOn_univ.mp (ContinuousOn.comp
    (f := fun p : ℝ × ℝ => (stripClamp T p.1,p.2))
    (g := fun p : ℝ × ℝ => iteratedDeriv (n+1) (value W γ p.1) p.2) hc hg hm)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.StripSquareMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def stripQ (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (t : ℝ) : ℝ :=
  ∫ ω, compactSquare W γ T t ((stripDrift W γ T).solution W.driver (Real.toNNReal t) ω) ∂W.law

def stripA (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (t : ℝ) : ℝ :=
  ∫ ω, (deriv (compactGradient W γ T t) ((stripDrift W γ T).solution W.driver (Real.toNNReal t) ω))^2 ∂W.law

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def curvatureMoment (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ) : ℝ :=
  ∫ ω, (curvature W γ t (diffusion W γ (Real.toNNReal t) ω))^2 ∂W.law

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.DiffusionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def positiveDrift (γ : OrderParameter) (n : ℕ) : BoundedLipschitzDrift :=
  finiteFeedback (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n)))
    (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n)))
    (positiveCoeff γ n) (approxMesh n) (n+1) 0

def positivePath (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  (positiveDrift γ n).solution W.driver

def positiveCoeffError (γ : OrderParameter) (n : ℕ) : ℝ :=
  ∫ s in (0:ℝ)..1, |positiveGamma γ n s-extend γ.val s|

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.PositiveGradientError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def positiveGradientErrors (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) : Set ℝ :=
  Set.range (fun p : ℝ × ℝ => |deriv (positiveValue γ n (stripClamp T p.1)) p.2-compactGradient W γ T p.1 p.2|)

def positiveGradientError (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) : ℝ :=
  sSup (positiveGradientErrors W γ T n)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.SampleJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def sampleJet (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (m : ℕ) (ξ : Ω) : ℝ :=
  iteratedDeriv m (positiveValue γ n (sampleTime n t)) (positivePath W γ n (sampleNNTime n t) ξ)

def actualJet (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (m : ℕ) (ξ : Ω) : ℝ :=
  iteratedDeriv m (value W γ t) (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def sampleQuartic (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (ξ : Ω) : ℝ :=
  quarticJetPolynomial (positiveCoeff γ n (sampleIndex n t)) (sampleJet W γ n t 2 ξ)

def sampleCoercive (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (ξ : Ω) : ℝ :=
  coerciveJetPolynomial (positiveCoeff γ n (sampleIndex n t))
    (sampleJet W γ n t 2 ξ) (sampleJet W γ n t 3 ξ) (sampleJet W γ n t 4 ξ)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.MixedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def compactMixedGradient (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  (compactGradient W β T t x+compactGradient W γ T t x)/2

def compactMixedDrift (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactCoeff β T t*compactMixedGradient W β γ T t x

lemma compactMixedGradient_continuous (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactMixedGradient W β γ T p.1 p.2) :=
  ((compactGradient_continuous W β hT0 hT1).add (compactGradient_continuous W γ hT0 hT1)).div_const 2

lemma compactMixedGradient_bound (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactMixedGradient W β γ T t x| ≤ 1 := by
  have hb := compactGradient_bound W β hT0 hT1 t x
  have hg := compactGradient_bound W γ hT0 hT1 t x
  unfold compactMixedGradient
  rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  linarith [abs_add_le (compactGradient W β T t x) (compactGradient W γ T t x)]

lemma compactMixedDrift_bound (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactMixedDrift W β γ T t x| ≤ β.val ⟨T,⟨hT0,hT1⟩⟩ := by
  unfold compactMixedDrift
  rw [abs_mul,abs_of_nonneg (compactCoeff_bounds β hT0 hT1 t).1]
  exact (mul_le_of_le_one_right (compactCoeff_bounds β hT0 hT1 t).1
    (compactMixedGradient_bound W β γ hT0 hT1 t x)).trans (compactCoeff_bounds β hT0 hT1 t).2

lemma compactMixedDrift_lipschitz (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (compactMixedDrift W β γ T t) := by
  obtain ⟨Lβ,hβ⟩ := compactGradient_lipschitz W β hT0 hT1
  obtain ⟨Lγ,hγ⟩ := compactGradient_lipschitz W γ hT0 hT1
  let D : ℝ≥0 := ⟨β.val ⟨T,⟨hT0,hT1⟩⟩,β.nonneg _⟩
  refine ⟨D*((Lβ+Lγ)/2),fun t => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hsum := abs_add_le (compactGradient W β T t x-compactGradient W β T t y)
    (compactGradient W γ T t x-compactGradient W γ T t y)
  have hb := (hβ t).dist_le_mul x y
  have hg := (hγ t).dist_le_mul x y
  simp only [Real.dist_eq] at hb hg
  have hmix : |compactMixedGradient W β γ T t x-compactMixedGradient W β γ T t y| ≤
      ((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y| := by
    have he : compactMixedGradient W β γ T t x-compactMixedGradient W β γ T t y=
        ((compactGradient W β T t x-compactGradient W β T t y)+
        (compactGradient W γ T t x-compactGradient W γ T t y))/2 := by unfold compactMixedGradient;ring
    rw [he,abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith
  rw [Real.dist_eq,compactMixedDrift,compactMixedDrift,← mul_sub,abs_mul,
    abs_of_nonneg (compactCoeff_bounds β hT0 hT1 t).1]
  calc
    _ ≤ compactCoeff β T t*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|) :=
      mul_le_mul_of_nonneg_left hmix (compactCoeff_bounds β hT0 hT1 t).1
    _ ≤ β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|) :=
      mul_le_mul_of_nonneg_right (compactCoeff_bounds β hT0 hT1 t).2 (by positivity)
    _ = _ := by
      change β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|)=
        ((D:ℝ)*(((Lβ:ℝ)+(Lγ:ℝ))/2))*|x-y|
      change β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|)=
        (β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2))*|x-y|
      ring

def mixedStripDrift (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) : BoundedLipschitzDrift where
  f := compactMixedDrift W β γ T
  bound := ⟨β.val T,β.nonneg T⟩
  lip := (compactMixedDrift_lipschitz W β γ T.property.1 T.property.2).choose
  measurable := ((compactCoeff_measurable β T).comp measurable_fst).mul
    (compactMixedGradient_continuous W β γ T.property.1 T.property.2).measurable
  bounded := compactMixedDrift_bound W β γ T.property.1 T.property.2
  lipschitz := (compactMixedDrift_lipschitz W β γ T.property.1 T.property.2).choose_spec

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.JetFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def compactJet (W : BrownianSystem Ω) (γ : OrderParameter) (T : ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv n (compactGradient W γ T t) x

def compactJetField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) : TimeField T where
  f := compactJet W γ T n
  d := fun t x => iteratedDeriv (n+1) (compactValueRate W γ T t) x
  smooth := (compactGradient_family W γ hT0 hT1).iteratedDeriv n
  rate_smooth := (compactValueRate_family W γ hT0 hT1).iteratedDeriv (n+1)
  continuous := compactGradient_derivative_continuous W γ hT0 hT1 n
  rate_right := fun t x => (compactValueRate_rightSmooth W γ hT0 hT1 (n+1) t x).mono Ioi_subset_Ici_self
  time_deriv := by
    intro t ht0 htT x
    have hh := value_derivative_hasDerivWithinAt_right W γ hT0 hT1 ht0 htT (n+1) x
    apply hh.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
      unfold compactJet compactGradient gradient
      rw [stripClamp_eq ⟨ht0.trans hs.le,hsT.le⟩,iteratedDeriv_succ']
    · unfold compactJet compactGradient gradient
      rw [stripClamp_eq ⟨ht0,htT.le⟩,iteratedDeriv_succ']

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def curvatureField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) : TimeField T :=
  (compactJetField W γ hT0 hT1 1).mul (compactJetField W γ hT0 hT1 1)

def secondCurvatureField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c : ℝ) : TimeField T :=
  ((compactJetField W γ hT0 hT1 2).mul (compactJetField W γ hT0 hT1 2)).add
    (((curvatureField W γ hT0 hT1).mul (compactJetField W γ hT0 hT1 1)).const_mul (-2*c))

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.MixedIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def mixedQ (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) (t : ℝ) : ℝ :=
  ∫ ξ, (compactGradient W γ T t ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal t) ξ))^2 ∂W.law

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.PerturbationLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def perturbationGradientErrors (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) : Set ℝ :=
  Set.range (fun p : ℝ × ℝ => |compactGradient W (perturbation γ β n) T p.1 p.2-compactGradient W γ T p.1 p.2|)

def perturbationGradientError (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) : ℝ :=
  sSup (perturbationGradientErrors W γ β T n)

def perturbationPathError (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) : ℝ :=
  2*(coefficientDistance (perturbation γ β n) γ+γ.val T*(T:ℝ)*perturbationGradientError W γ β T n)*
    Real.exp ((stripDrift W γ T).rate*T)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.ThirdFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def thirdCurvatureField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c : ℝ) : TimeField T :=
  (((compactJetField W γ hT0 hT1 3).mul (compactJetField W γ hT0 hT1 3)).add
    (((compactJetField W γ hT0 hT1 1).mul
      ((compactJetField W γ hT0 hT1 2).mul (compactJetField W γ hT0 hT1 2))).const_mul (-12*c))).add
        (((curvatureField W γ hT0 hT1).mul (curvatureField W γ hT0 hT1)).const_mul (6*c^2))

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def stripSecond (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) : ℝ → ℝ :=
  (secondCurvatureField W γ T.property.1 T.property.2 c).expected (stripDrift W γ T) W

def stripThird (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) : ℝ → ℝ :=
  (thirdCurvatureField W γ T.property.1 T.property.2 c).expected (stripDrift W γ T) W

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.Closure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace ZeroTemperatureSK.SupportDeterministic
abbrev Time := Set.Ico (0 : ℝ) 1

structure IsOrderParameter (γ : ℝ → ℝ) : Prop where
  nonneg : ∀ t ∈ Set.Ico (0 : ℝ) 1, 0 ≤ γ t
  monotone : MonotoneOn γ (Set.Ico (0 : ℝ) 1)
  rightContinuous : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt γ (Set.Ici t) t
  integrable : IntegrableOn γ (Set.Ico (0 : ℝ) 1)

def IsStieltjesMeasure (γ : ℝ → ℝ) (μ : Measure Time) : Prop :=
  ∀ t : Time, μ (Set.Iic t) = ENNReal.ofReal (γ t)

def InSupport (μ : Measure Time) (t : ℝ) : Prop :=
  ∃ ht : t ∈ Ico (0 : ℝ) 1, (⟨t, ht⟩ : Time) ∈ μ.support

end ZeroTemperatureSK.SupportDeterministic

end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.FiniteCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

def finiteCDF (ν : Measure Time) (t : Time) : ℝ := (ν (Iic t)).toReal

lemma finiteCDF_nonneg (ν : Measure Time) (t : Time) : 0 ≤ finiteCDF ν t := ENNReal.toReal_nonneg

lemma finiteCDF_monotone (ν : Measure Time) [IsFiniteMeasure ν] : Monotone (finiteCDF ν) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Iic_subset_Iic.mpr hab))

lemma finiteCDF_bound (ν : Measure Time) [IsFiniteMeasure ν] (t : Time) : finiteCDF ν t ≤ (ν univ).toReal :=
  ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (subset_univ _))

lemma finiteCDF_integral (ν : Measure Time) (t : Time) :
    finiteCDF ν t=∫ r : Time, (if r ≤ t then (1:ℝ) else 0) ∂ν := by
  have he : (fun r : Time => if r ≤ t then (1:ℝ) else 0)=(Iic t).indicator (fun _ => (1:ℝ)) := by
    funext r
    simp only [Set.indicator_apply,mem_Iic]
  rw [he,integral_indicator measurableSet_Iic]
  simp only [finiteCDF,integral_const,measureReal_def,smul_eq_mul,mul_one,Measure.restrict_apply_univ]

lemma finiteCDF_rightContinuous (ν : Measure Time) [IsFiniteMeasure ν] (t : Time) :
    ContinuousWithinAt (finiteCDF ν) (Ici t) t := by
  change Tendsto (fun u => finiteCDF ν u) (𝓝[Ici t] t) (𝓝 (finiteCDF ν t))
  simp only [finiteCDF_integral]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Time => (1:ℝ))
  · exact Eventually.of_forall (fun u => (measurable_const.piecewise measurableSet_Iic measurable_const).aestronglyMeasurable)
  · exact Eventually.of_forall (fun u => Eventually.of_forall (fun r => by split_ifs <;> norm_num))
  · exact integrable_const _
  · filter_upwards [] with r
    by_cases hrt : r ≤ t
    · simp only [ite_eq_left hrt]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [ite_eq_left (hrt.trans hu)]
    · have htr : t < r := lt_of_not_ge hrt
      simp only [ite_eq_right hrt]
      apply tendsto_const_nhds.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htr)] with u hu
      rw [ite_eq_right (not_le_of_gt hu)]

lemma integrable_extend_of_bounded {f : Time → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C) : Integrable (extend f) := by
  have hm : Measurable (extend f) := hf.dite measurable_const measurableSet_Ico
  have hi : Integrable ((Ico (0:ℝ) 1).indicator (fun _ => C)) :=
    (integrableOn_const (C := C) measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : t ∈ Ico (0:ℝ) 1
  · simp only [extend,dite_eq_left ht,Real.norm_eq_abs,indicator_of_mem ht]
    exact hC _
  · simp only [extend,dite_eq_right ht,Real.norm_eq_abs,abs_zero,indicator_of_notMem ht,le_refl]

lemma finiteCDF_integrable (ν : Measure Time) [IsFiniteMeasure ν] : Integrable (extend (finiteCDF ν)) :=
  integrable_extend_of_bounded (finiteCDF_monotone ν).measurable
    (fun t => by rw [abs_of_nonneg (finiteCDF_nonneg ν t)];exact finiteCDF_bound ν t)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.CDFParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma extend_add_fun (f g : Time → ℝ) : extend (fun t => f t+g t)=fun t => extend f t+extend g t := by
  funext t
  by_cases ht : t ∈ Ico (0:ℝ) 1 <;> simp [extend,ht]
lemma extend_sub_fun (f g : Time → ℝ) : extend (fun t => f t-g t)=fun t => extend f t-extend g t := by
  funext t
  by_cases ht : t ∈ Ico (0:ℝ) 1 <;> simp [extend,ht]

def OrderParameter.addCDF (γ : OrderParameter) (ν : Measure Time) [IsFiniteMeasure ν] : OrderParameter where
  val := fun t => γ.val t+finiteCDF ν t
  nonneg := fun t => add_nonneg (γ.nonneg t) (finiteCDF_nonneg ν t)
  monotone := γ.monotone.add (finiteCDF_monotone ν)
  right_continuous := fun t => (γ.right_continuous t).add (finiteCDF_rightContinuous ν t)
  integrable := by rw [extend_add_fun];exact γ.integrable.add (finiteCDF_integrable ν)

lemma stieltjes_real (γ : OrderParameter) {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) (t : Time) :
    (μ (Iic t)).toReal=γ.val t := by rw [hμ t,ENNReal.toReal_ofReal (γ.nonneg t)]

lemma finiteCDF_le_parameter (γ : OrderParameter) {μ ν : Measure Time} (hμ : IsStieltjesMeasure γ μ)
    (hν : ν ≤ μ) (t : Time) : finiteCDF ν t ≤ γ.val t := by
  rw [← stieltjes_real γ hμ t]
  apply ENNReal.toReal_mono
  · rw [hμ t];exact ENNReal.ofReal_ne_top
  · exact hν (Iic t)

lemma cdf_real_add_Ioc {μ : Measure Time} {a b : Time} (hab : a ≤ b) (hfinite : μ (Iic b) ≠ ⊤) :
    (μ (Iic a)).toReal+(μ (Ioc a b)).toReal=(μ (Iic b)).toReal := by
  have hf1 := ne_top_of_le_ne_top hfinite (measure_mono (Iic_subset_Iic.mpr hab))
  have hf2 := ne_top_of_le_ne_top hfinite (measure_mono (show Ioc a b ⊆ Iic b from fun _ h => h.2))
  have he : μ (Iic a)+μ (Ioc a b)=μ (Iic b) := by
    rw [← measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,Iic_union_Ioc_eq_Iic hab]
  have hh := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hf1 hf2] at hh
  exact hh

lemma removeCDF_monotone (γ : OrderParameter) {μ ν : Measure Time} [IsFiniteMeasure ν]
    (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) : Monotone (fun t => γ.val t-finiteCDF ν t) := by
  intro a b hab
  have hf : μ (Iic b) ≠ ⊤ := by rw [hμ b];exact ENNReal.ofReal_ne_top
  have hm := cdf_real_add_Ioc hab hf
  rw [stieltjes_real γ hμ a,stieltjes_real γ hμ b] at hm
  have hn := cdf_real_add_Ioc (μ := ν) hab (measure_ne_top ν _)
  have hi : (ν (Ioc a b)).toReal ≤ (μ (Ioc a b)).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top hf (measure_mono (fun _ h => h.2))) (hν (Ioc a b))
  change γ.val a-(ν (Iic a)).toReal ≤ γ.val b-(ν (Iic b)).toReal
  linarith

def OrderParameter.removeCDF (γ : OrderParameter) {μ ν : Measure Time} [IsFiniteMeasure ν]
    (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) : OrderParameter where
  val := fun t => γ.val t-finiteCDF ν t
  nonneg := fun t => sub_nonneg.mpr (finiteCDF_le_parameter γ hμ hν t)
  monotone := removeCDF_monotone γ hμ hν
  right_continuous := fun t => (γ.right_continuous t).sub (finiteCDF_rightContinuous ν t)
  integrable := by rw [extend_sub_fun];exact γ.integrable.sub (finiteCDF_integrable ν)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.VariationIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def normalizedValueDifference (W : BrownianSystem Ω) (γ β : OrderParameter) (n : ℕ) : ℝ :=
  (value W (perturbation γ β n) 0 0-value W γ 0 0)/variationStep n

def variationTail (γ β : OrderParameter) (T : ℝ) : ℝ :=
  ∫ s in T..1, |extend β.val s-extend γ.val s|

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.ContactPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def contactPotential (W : BrownianSystem Ω) (γ : OrderParameter) (s : ℝ) : ℝ :=
  ∫ t in s..1, squareMoment W γ (diffusion W γ) t-t

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.GapCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

instance timeCompactIccSpace : CompactIccSpace Time where
  isCompact_Icc {a} {b} := by
    rw [Subtype.isCompact_iff]
    have he : Subtype.val '' Icc a b=Icc (a:ℝ) (b:ℝ) := by
      ext t
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact hu
      · intro ht
        exact ⟨⟨t,⟨a.property.1.trans ht.1,ht.2.trans_lt b.property.2⟩⟩,ht,rfl⟩
    rw [he]
    exact isCompact_Icc

def parameterStieltjes (γ : OrderParameter) : StieltjesFunction Time where
  toFun := γ.val
  mono' := γ.monotone
  right_continuous' := γ.right_continuous

def parameterMeasure (γ : OrderParameter) : Measure Time :=
  (parameterStieltjes γ).measure + ENNReal.ofReal (γ.val ⊥) • Measure.dirac ⊥

end ZeroTemperatureSK

end
end

end OAI
end


