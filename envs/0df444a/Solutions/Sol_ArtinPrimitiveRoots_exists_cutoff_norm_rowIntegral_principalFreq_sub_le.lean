-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_norm_rowIntegral_principalFreq_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T14:13:32.043892+00:00
-- url     : https://prove2.me/submissions/019923c4-e439-4a74-844a-76786cdb25fa

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_freqSeries_principalFreq_eq
universe u

section
/-! # C3P_Shift: one-variable contour shifts of vertical line integrals

* `C3P_shift`: no pole, with a decaying integrable majorant `g (Im s)` on the strip;
* `C3P_shift_pole`: one simple pole `p` inside the strip, `f = A / (s - p)`; the majorant is only
  required on the two lines and for `|Im s| ≥ 1`.

The pole computation follows `OAI.SevenEighths.PrincipalMellinResidues.verticalIntegral_simple_pole`
(copied and adapted). -/

set_option maxHeartbeats 1000000

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

lemma integrable_line_of_le {f : ℂ → ℂ} {g : ℝ → ℝ} {c : ℝ}
    (hc : ContinuousOn f {s | s.re = c}) (hg : Integrable g)
    (hb : ∀ t : ℝ, ‖f (c + t * I)‖ ≤ g t) :
    Integrable fun t : ℝ => f (c + t * I) := by
  refine hg.mono' ?_ (Eventually.of_forall hb)
  refine (hc.comp_continuous (by fun_prop) fun t => ?_).aestronglyMeasurable
  simp

lemma horizontal_tendsto {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atTop (𝓝 0)) (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → 1 ≤ T → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + T * I)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun T : ℝ => g T * |b - a|) atTop (𝓝 0) := by
    simpa using hg.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  exact hb x T hx.1.le hx.2 hT

lemma horizontal_tendsto_neg {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atBot (𝓝 0))
    (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → T ≤ -1 → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + (-T) * I)) atTop (𝓝 0) := by
  have hg' : Tendsto (fun T : ℝ => g (-T)) atTop (𝓝 0) := hg.comp tendsto_neg_atTop_atBot
  have hexp : Tendsto (fun T : ℝ => g (-T) * |b - a|) atTop (𝓝 0) := by
    simpa using hg'.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  have := hb x (-T) hx.1.le hx.2 (by linarith)
  simpa using this

/-- Shifting a vertical line integral across a strip on which `f` is holomorphic, given an
integrable majorant `g (Im s)` tending to `0` at `±∞`. -/
theorem C3P_shift {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {s | a ≤ s.re ∧ s.re ≤ b})
    (hg : Integrable g) (hgt : Tendsto g atTop (𝓝 0)) (hgb : Tendsto g atBot (𝓝 0))
    (hb : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ g s.im) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  have hc : ∀ c, a ≤ c → c ≤ b → ContinuousOn f {s | s.re = c} := fun c h1 h2 =>
    hf.continuousOn.mono fun s hs => by simp only [Set.mem_ofPred_eq] at hs ⊢; constructor <;> linarith
  have hia := integrable_line_of_le (hc a le_rfl hab) hg fun t => by
    simpa using hb (a + t * I) (by simp) (by simp [hab])
  have hib := integrable_line_of_le (hc b hab le_rfl) hg fun t => by
    simpa using hb (b + t * I) (by simp [hab]) (by simp)
  have hrect : ∀ T : ℝ, (∫ x : ℝ in a..b, f (x + (-T) * I)) - (∫ x : ℝ in a..b, f (x + T * I)) +
      I • (∫ y : ℝ in -T..T, f (b + y * I)) - I • (∫ y : ℝ in -T..T, f (a + y * I)) = 0 := by
    intro T
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩
      (hf.mono fun z hz => by
        rw [mem_reProdIm, Set.uIcc_of_le hab] at hz
        exact ⟨hz.1.1, hz.1.2⟩)
    simpa using this
  have hup := horizontal_tendsto (f := f) hab hgt fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hlow := horizontal_tendsto_neg (f := f) hab hgb fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hva : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (a + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (a + τ * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (b + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (b + τ * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h1 := ((hlow.sub hup).add ((hvb.const_smul I).sub (hva.const_smul I)))
  have h2 : Tendsto (fun T : ℝ => (0 : ℂ)) atTop
      (𝓝 ((0 - 0) + ((I • ∫ τ : ℝ, f (b + τ * I)) - I • ∫ τ : ℝ, f (a + τ * I)))) := by
    refine h1.congr fun T => ?_
    rw [← hrect T]
    ring
  have h3 := tendsto_nhds_unique tendsto_const_nhds h2
  simp only [sub_self, zero_add, smul_eq_mul] at h3
  rw [← mul_sub, eq_comm, mul_eq_zero, sub_eq_zero] at h3
  exact (h3.resolve_left I_ne_zero).symm

/-! ### A simple pole -/

theorem integral_id_div_sq_add_sq {a b c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, x / (c ^ 2 + x ^ 2) =
      (Real.log (c ^ 2 + b ^ 2) - Real.log (c ^ 2 + a ^ 2)) / 2 := by
  rw [sub_div]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => Real.log (c ^ 2 + x ^ 2) / 2)
  · intro x _
    have h := (((hasDerivAt_pow 2 x).const_add (c ^ 2)).log
      (by dsimp; positivity)).div_const 2
    refine h.congr_deriv ?_
    have : c ^ 2 + x ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  · exact (continuous_id.div (by fun_prop) fun x => by positivity).intervalIntegrable _ _

lemma inverse_vertical_continuous (c : ℝ) (hc : c ≠ 0) :
    Continuous (fun t : ℝ => ((c : ℂ) + t * I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t h
  have he := congrArg Complex.re h
  simp at he
  exact hc he

lemma inverse_vertical_truncated (c T : ℝ) (hc : c ≠ 0) :
    (∫ t : ℝ in -T..T, ((c : ℂ) + t * I)⁻¹) = (2 * Real.arctan (T / c) : ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((c : ℂ) + t * I)⁻¹) volume (-T) T :=
    (inverse_vertical_continuous c hc).intervalIntegrable (-T) T
  apply Complex.ext
  · have hh := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c : ℂ) + t * I)⁻¹).re) =
      (∫ t : ℝ in -T..T, ((c : ℂ) + t * I)⁻¹).re at hh
    rw [← hh]
    have he : (fun t : ℝ => (((c : ℂ) + t * I)⁻¹).re) = (fun t : ℝ => c / (c ^ 2 + t ^ 2)) := by
      funext t
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [he, integral_div_sq_add_sq]
    simp [neg_div, Real.arctan_neg, -Complex.ofReal_arctan]
    ring
  · have hh := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c : ℂ) + t * I)⁻¹).im) =
      (∫ t : ℝ in -T..T, ((c : ℂ) + t * I)⁻¹).im at hh
    rw [← hh]
    have he : (fun t : ℝ => (((c : ℂ) + t * I)⁻¹).im) = (fun t : ℝ => -(t / (c ^ 2 + t ^ 2))) := by
      funext t
      simp [Complex.inv_im, Complex.normSq_apply, pow_two, neg_div]
    rw [he, intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc]
    simp [-Complex.ofReal_arctan]

lemma inverse_vertical_limit_pos (c : ℝ) (hc : 0 < c) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c : ℂ) + t * I)⁻¹) atTop (𝓝 (Real.pi : ℂ)) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne']
  have ht := Real.tendsto_arctan_atTop.comp (Filter.tendsto_id.atTop_div_const hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_vertical_limit_neg (c : ℝ) (hc : c < 0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c : ℂ) + t * I)⁻¹) atTop
      (𝓝 (-(Real.pi : ℂ))) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne]
  have ht := Real.tendsto_arctan_atBot.comp (Filter.tendsto_id.atTop_div_const_of_neg hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_horizontal_limit (a b p : ℝ) (ε : ℝ) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, ((x : ℂ) + (ε * T) * I - p)⁻¹) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ T : ℝ in atTop, ‖∫ x : ℝ in a..b,
      ((x : ℂ) + (ε * T) * I - p)⁻¹‖ ≤ T⁻¹ * |b - a| from ?_) ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x _
    rw [norm_inv]
    apply inv_anti₀ hT
    have h := Complex.abs_im_le_norm ((x : ℂ) + (ε * T) * I - p)
    simpa [abs_mul, hε, abs_of_pos hT] using h
  · simpa using (tendsto_inv_atTop_zero.mul_const |b - a|)

lemma dslope_eq_sub_pole {A F : ℂ → ℂ} {p z : ℂ} (hz : z ≠ p) (hF : F z = A z / (z - p)) :
    dslope A p z = F z - A p * (z - p)⁻¹ := by
  rw [dslope_of_ne A hz, slope, hF]
  simp only [smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

lemma dslope_vertical_truncated (A F : ℂ → ℂ) (p x T : ℝ) (hx : x ≠ p)
    (hF : ∀ z : ℂ, z.re = x → F z = A z / (z - p))
    (hi : Integrable (fun t : ℝ => F ((x : ℂ) + t * I))) :
    (∫ t : ℝ in -T..T, dslope A (p : ℂ) ((x : ℂ) + t * I)) =
      (∫ t : ℝ in -T..T, F ((x : ℂ) + t * I)) -
        A p * (∫ t : ℝ in -T..T, (((x - p : ℝ) : ℂ) + t * I)⁻¹) := by
  have he (t : ℝ) : dslope A (p : ℂ) ((x : ℂ) + t * I) =
      F ((x : ℂ) + t * I) - A p * ((((x - p : ℝ) : ℂ) + t * I)⁻¹) := by
    have hn : (x : ℂ) + t * I ≠ p := by
      intro h
      exact hx (by simpa using congrArg Complex.re h)
    have h := dslope_eq_sub_pole hn (hF _ (by simp))
    rw [h]; push_cast; ring_nf
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi.intervalIntegrable
    (((inverse_vertical_continuous (x - p) (sub_ne_zero.mpr hx)).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

lemma rectangle_limits (G : ℂ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    {Va Vb : ℂ}
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((a : ℂ) + t * I)) atTop (𝓝 Va))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((b : ℂ) + t * I)) atTop (𝓝 Vb))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x : ℂ) + (-T) * I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x : ℂ) + T * I)) atTop (𝓝 0)) :
    Va = Vb := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, G ((x : ℂ) + (-T) * I)) -
      (∫ x : ℝ in a..b, G ((x : ℂ) + T * I)) +
      I * (∫ t : ℝ in -T..T, G ((b : ℂ) + t * I)) -
      I * (∫ t : ℝ in -T..T, G ((a : ℂ) + t * I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a : ℂ) + (-T) * I) ((b : ℂ) + T * I) (hG.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      simpa [uIcc_of_le hab] using hz.1
  have hlim := ((hbot.sub htop).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : (0 : ℂ) - 0 + I * Vb - I * Va = 0 := tendsto_nhds_unique hlim
    (by simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  exact (mul_left_cancel₀ I_ne_zero (show I * Vb = I * Va by simpa using sub_eq_zero.mp hz)).symm

lemma horizontal_quotient_continuousOn (A : ℂ → ℂ) {a b p y : ℝ}
    (hab : a ≤ b) (hy : y ≠ 0)
    (hA : DifferentiableOn ℂ A {z : ℂ | a ≤ z.re ∧ z.re ≤ b}) :
    ContinuousOn (fun x : ℝ => A ((x : ℂ) + y * I) / ((x : ℂ) + y * I - p)) (uIcc a b) := by
  apply ContinuousOn.div
  · apply hA.continuousOn.comp (by fun_prop)
    intro x hx
    simpa [uIcc_of_le hab] using hx
  · fun_prop
  · intro x _ h
    have hh := congrArg Complex.im h
    exact hy (by simpa using hh)

lemma dslope_horizontal_limit (A F : ℂ → ℂ) {a b p : ℝ} (hab : a ≤ b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hF : ∀ z : ℂ, F z = A z / (z - p))
    (ε : ℝ) (hε : |ε| = 1)
    (hlim : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (ε * T) * I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, dslope A p ((x : ℂ) + (ε * T) * I)) atTop (𝓝 0) := by
  have hl := hlim.sub ((inverse_horizontal_limit a b p ε hε).const_mul (A p))
  simp only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hy : ε * T ≠ 0 := mul_ne_zero (by intro h; simp [h] at hε) hT.ne'
  have hn (x : ℝ) : (x : ℂ) + (ε * T) * I ≠ p := by
    intro h
    exact hy (by simpa using congrArg Complex.im h)
  have hfi : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (ε * T) * I)) volume a b := by
    apply ((horizontal_quotient_continuousOn A (p := p) hab hy hA).congr ?_).intervalIntegrable
    intro x _
    simp only [hF]; push_cast; ring_nf
  have hki : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (ε * T) * I - p)⁻¹) volume a b := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    exact hn x (sub_eq_zero.mp h)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hfi (hki.const_mul _)]
  apply intervalIntegral.integral_congr
  intro x _
  exact (dslope_eq_sub_pole (hn x) (hF _)).symm

/-- Shifting a vertical line integral across a simple pole `p` of `f = A / (s - p)`:
`∫ f(b + it) dt = ∫ f(a + it) dt + 2π A(p)`. -/
theorem C3P_shift_pole {f A : ℂ → ℂ} {g : ℝ → ℝ} {a b p : ℝ} (hap : a < p) (hpb : p < b)
    (hA : DifferentiableOn ℂ A {s | a ≤ s.re ∧ s.re ≤ b})
    (hfA : ∀ s, f s = A s / (s - p))
    (hg : Integrable g) (hgt : Tendsto g atTop (𝓝 0)) (hgb : Tendsto g atBot (𝓝 0))
    (hb : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → (s.re = a ∨ s.re = b ∨ 1 ≤ |s.im|) → ‖f s‖ ≤ g s.im) :
    ∫ t : ℝ, f (b + t * I) = (∫ t : ℝ, f (a + t * I)) + 2 * (Real.pi : ℂ) * A p := by
  have hab := hap.le.trans hpb.le
  have hcl : ∀ c, a ≤ c → c ≤ b → c ≠ p → ContinuousOn f {s | s.re = c} := by
    intro c h1 h2 hcp
    have : ContinuousOn (fun s => A s / (s - p)) {s : ℂ | s.re = c} := by
      refine ContinuousOn.div (hA.continuousOn.mono fun s hs => ?_) (by fun_prop) fun s hs h => ?_
      · simp only [Set.mem_ofPred_eq] at hs ⊢; constructor <;> linarith
      · simp only [Set.mem_ofPred_eq] at hs
        exact hcp (by have := congrArg Complex.re h; simp at this; linarith)
    exact this.congr fun s _ => hfA s
  have ha : Integrable fun t : ℝ => f ((a : ℂ) + t * I) :=
    integrable_line_of_le (hcl a le_rfl hab hap.ne) hg fun t => by
      simpa using hb (a + t * I) (by simp) (by simp [hab]) (Or.inl (by simp))
  have hb' : Integrable fun t : ℝ => f ((b : ℂ) + t * I) :=
    integrable_line_of_le (hcl b hab le_rfl hpb.ne') hg fun t => by
      simpa using hb (b + t * I) (by simp [hab]) (by simp) (Or.inr (Or.inl (by simp)))
  have htop := horizontal_tendsto (f := f) hab hgt fun x T h1 h2 hT => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
      (Or.inr (Or.inr (by simp [abs_of_pos (by linarith : (0:ℝ) < T)]; linarith)))
  have hbot := horizontal_tendsto_neg (f := f) hab hgb fun x T h1 h2 hT => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
      (Or.inr (Or.inr (by simp [abs_of_neg (by linarith : T < 0)]; linarith)))
  have hnb : {z : ℂ | a ≤ z.re ∧ z.re ≤ b} ∈ 𝓝 (p : ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a < (p : ℂ).re ∧ (p : ℂ).re < b from ⟨by simpa using hap, by simpa using hpb⟩))
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hG := (Complex.differentiableOn_dslope hnb).mpr hA
  have haF := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbF := intervalIntegral_tendsto_integral hb' tendsto_neg_atTop_atBot tendsto_id
  have haG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p : ℂ) ((a : ℂ) + t * I))
      atTop (𝓝 ((∫ t : ℝ, f ((a : ℂ) + t * I)) - A p * (-(Real.pi : ℂ)))) := by
    simp_rw [dslope_vertical_truncated A f p a _ hap.ne (fun z _ => hfA z) ha]
    exact haF.sub ((inverse_vertical_limit_neg (a - p) (sub_neg.mpr hap)).const_mul (A p))
  have hbG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p : ℂ) ((b : ℂ) + t * I))
      atTop (𝓝 ((∫ t : ℝ, f ((b : ℂ) + t * I)) - A p * (Real.pi : ℂ))) := by
    simp_rw [dslope_vertical_truncated A f p b _ hpb.ne' (fun z _ => hfA z) hb']
    exact hbF.sub ((inverse_vertical_limit_pos (b - p) (sub_pos.mpr hpb)).const_mul (A p))
  have hbotG := dslope_horizontal_limit A f hab hA hfA (-1) (by norm_num)
    (by simpa using hbot)
  have htopG := dslope_horizontal_limit A f hab hA hfA 1 (by norm_num)
    (by simpa using htop)
  have he := rectangle_limits (dslope A p) hab hG haG hbG
    (by simpa using hbotG) (by simpa using htopG)
  linear_combination -he

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Maj: the majorants and the Fubini swaps

`u t = (1 + t²)⁻¹`, `γ x = exp(−x²/2)`, and the three-variable majorant
`u t₁ · u t₂ · γ (t₁ + t₃)`; `e^{−(t₁+t₃)²} u t₃ ≤ 4 u t₁ γ(t₁+t₃)` moves the Gaussian's decay onto
the outer variable. -/

open MeasureTheory Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable def uu (t : ℝ) : ℝ := (1 + t ^ 2)⁻¹

noncomputable def gg (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)

lemma uu_pos (t : ℝ) : 0 < uu t := by unfold uu; positivity

lemma gg_pos (x : ℝ) : 0 < gg x := Real.exp_pos _

lemma gg_le_one (x : ℝ) : gg x ≤ 1 := by
  unfold gg; rw [Real.exp_le_one_iff]; nlinarith

lemma continuous_uu : Continuous uu :=
  Continuous.inv₀ (by fun_prop) fun t => by positivity

lemma continuous_gg : Continuous gg := by unfold gg; fun_prop

lemma integrable_uu : Integrable uu := integrable_inv_one_add_sq

lemma integrable_gg : Integrable gg := by
  have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [gg]; ring_nf

lemma integrable_gg_add (a : ℝ) : Integrable fun t => gg (a + t) :=
  integrable_gg.comp_add_left a

lemma integral_gg_add (a : ℝ) : ∫ t, gg (a + t) = ∫ t, gg t :=
  integral_add_left_eq_self (fun t => gg t) a

lemma tendsto_uu_atTop : Tendsto uu atTop (𝓝 0) := by
  unfold uu
  refine tendsto_inv_atTop_zero.comp ?_
  exact tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)

lemma tendsto_uu_atBot : Tendsto uu atBot (𝓝 0) := by
  unfold uu
  refine tendsto_inv_atTop_zero.comp ?_
  refine tendsto_atTop_add_const_left _ _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp tendsto_neg_atBot_atTop |>.congr fun t => by simp

lemma tendsto_gg_atTop : Tendsto gg atTop (𝓝 0) := by
  unfold gg
  refine Real.tendsto_exp_atBot.comp ?_
  have : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  exact (tendsto_neg_atTop_atBot.comp this).congr fun x => by simp [neg_div]

lemma tendsto_gg_atBot : Tendsto gg atBot (𝓝 0) := by
  have h : gg = fun x => gg (-x) := funext fun x => by simp [gg]
  rw [h]
  exact tendsto_gg_atTop.comp tendsto_neg_atBot_atTop

lemma tendsto_gg_add_atTop (a : ℝ) : Tendsto (fun t => gg (a + t)) atTop (𝓝 0) :=
  tendsto_gg_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id)

lemma tendsto_gg_add_atBot (a : ℝ) : Tendsto (fun t => gg (a + t)) atBot (𝓝 0) :=
  tendsto_gg_atBot.comp (tendsto_atBot_add_const_left _ _ tendsto_id)

/-- `e^{−(a+b)²} (1 + b²)⁻¹ ≤ 4 (1 + a²)⁻¹ e^{−(a+b)²/2}`. -/
lemma exp_mul_uu_le (a b : ℝ) :
    Real.exp (-(a + b) ^ 2) * uu b ≤ 4 * uu a * gg (a + b) := by
  set s := a + b
  have h1 : 1 + a ^ 2 ≤ 2 * (1 + s ^ 2) * (1 + b ^ 2) := by
    have : a = s - b := by simp [s]
    rw [this]; nlinarith [sq_nonneg (s + b), sq_nonneg (s * b)]
  have h2 : (1 + s ^ 2) * Real.exp (-s ^ 2) ≤ 2 * gg s := by
    have he : Real.exp (-s ^ 2) = Real.exp (-(s ^ 2) / 2) * Real.exp (-(s ^ 2) / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hb : 1 + s ^ 2 ≤ 2 * Real.exp (s ^ 2 / 2) := by
      have := Real.add_one_le_exp (s ^ 2 / 2); nlinarith
    have hx : Real.exp (s ^ 2 / 2) * Real.exp (-(s ^ 2) / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    unfold gg
    rw [he]
    have hp := Real.exp_pos (-(s ^ 2) / 2)
    nlinarith
  have hb0 : 0 < 1 + b ^ 2 := by positivity
  have ha0 : 0 < 1 + a ^ 2 := by positivity
  have hg := gg_pos s
  have hE := Real.exp_pos (-s ^ 2)
  have key : Real.exp (-s ^ 2) * (1 + a ^ 2) ≤ 4 * gg s * (1 + b ^ 2) :=
    calc Real.exp (-s ^ 2) * (1 + a ^ 2)
        ≤ Real.exp (-s ^ 2) * (2 * (1 + s ^ 2) * (1 + b ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hE.le
      _ = 2 * ((1 + s ^ 2) * Real.exp (-s ^ 2)) * (1 + b ^ 2) := by ring
      _ ≤ 2 * (2 * gg s) * (1 + b ^ 2) := by gcongr
      _ = 4 * gg s * (1 + b ^ 2) := by ring
  unfold uu
  calc Real.exp (-(a + b) ^ 2) * (1 + b ^ 2)⁻¹
      = (Real.exp (-s ^ 2) * (1 + a ^ 2)) / ((1 + a ^ 2) * (1 + b ^ 2)) := by
        field_simp; rfl
    _ ≤ (4 * gg s * (1 + b ^ 2)) / ((1 + a ^ 2) * (1 + b ^ 2)) := by gcongr
    _ = 4 * (1 + a ^ 2)⁻¹ * gg (a + b) := by field_simp; rfl

/-! ### Integrability of the majorants -/

lemma integrable_uu_mul_gg (a : ℝ) :
    Integrable (fun q : ℝ × ℝ => uu q.1 * gg (a + q.2)) (volume.prod volume) :=
  integrable_uu.mul_prod (integrable_gg_add a)

lemma integrable_m3 :
    Integrable (fun p : ℝ × ℝ × ℝ => uu p.1 * uu p.2.1 * gg (p.1 + p.2.2))
      (volume.prod (volume.prod volume)) := by
  rw [integrable_prod_iff]
  · constructor
    · refine Eventually.of_forall fun a => ?_
      have := (integrable_uu_mul_gg a).const_mul (uu a)
      simpa [mul_assoc] using this
    · have hI : ∀ a, ∫ q : ℝ × ℝ, ‖uu a * uu q.1 * gg (a + q.2)‖ ∂(volume.prod volume) =
          uu a * ((∫ t, uu t) * ∫ t, gg t) := by
        intro a
        have hn : ∀ q : ℝ × ℝ, ‖uu a * uu q.1 * gg (a + q.2)‖ =
            uu a * (uu q.1 * gg (a + q.2)) := fun q => by
          have h1 := uu_pos a
          have h2 := uu_pos q.1
          have h3 := gg_pos (a + q.2)
          rw [Real.norm_of_nonneg (by positivity)]
          ring
        simp_rw [hn]
        rw [integral_const_mul, integral_prod_mul (fun t => uu t) (fun t => gg (a + t)),
          integral_gg_add]
      simp_rw [hI]
      exact integrable_uu.mul_const _
  · have hc : Continuous fun p : ℝ × ℝ × ℝ => uu p.1 * uu p.2.1 * gg (p.1 + p.2.2) :=
      ((continuous_uu.comp continuous_fst).mul (continuous_uu.comp
        (continuous_fst.comp continuous_snd))).mul
        (continuous_gg.comp (continuous_fst.add (continuous_snd.comp continuous_snd)))
    exact hc.aestronglyMeasurable

/-! ### Fubini -/

/-- Moving the outermost of three iterated integrals innermost. -/
theorem swap3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → ℝ → ℝ → E}
    (hf : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (volume.prod (volume.prod volume))) :
    ∫ a, ∫ b, ∫ c, f a b c = ∫ b, ∫ c, ∫ a, f a b c := by
  have h1 : ∀ᵐ a, ∫ b, ∫ c, f a b c = ∫ q : ℝ × ℝ, f a q.1 q.2 ∂(volume.prod volume) := by
    filter_upwards [hf.prod_right_ae] with a ha
    exact (integral_prod (fun q : ℝ × ℝ => f a q.1 q.2) ha).symm
  rw [integral_congr_ae h1]
  have h2 := integral_integral_swap (μ := volume) (ν := volume.prod volume)
    (f := fun a (q : ℝ × ℝ) => f a q.1 q.2) hf
  rw [h2]
  have h3 : Integrable (fun q : ℝ × ℝ => ∫ a, f a q.1 q.2) (volume.prod volume) :=
    hf.integral_prod_right
  rw [integral_prod _ h3]

/-- Dominated integrability on `ℝ³`. -/
lemma integrable_of_le_m3 {f : ℝ × ℝ × ℝ → ℂ} (hf : Continuous f) {K : ℝ}
    (hb : ∀ p : ℝ × ℝ × ℝ, ‖f p‖ ≤ K * (uu p.1 * uu p.2.1 * gg (p.1 + p.2.2))) :
    Integrable f (volume.prod (volume.prod volume)) :=
  (integrable_m3.const_mul K).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)

/-- `‖∫ a ∫ c ∫ b f‖ ≤ K (∫u)² ∫γ` when `‖f a c b‖ ≤ K u a u b γ(a + c)`. -/
lemma norm_iter3_le {f : ℝ → ℝ → ℝ → ℂ} {K : ℝ}
    (hb : ∀ a c b, ‖f a c b‖ ≤ K * (uu a * uu b * gg (a + c))) :
    ‖∫ a, ∫ c, ∫ b, f a c b‖ ≤ K * ((∫ t, uu t) * (∫ t, uu t) * ∫ t, gg t) := by
  have h1 : ∀ a c, ‖∫ b, f a c b‖ ≤ K * uu a * gg (a + c) * ∫ t, uu t := by
    intro a c
    have := norm_integral_le_of_norm_le ((integrable_uu.const_mul (K * uu a * gg (a + c))))
      (Eventually.of_forall fun b => (hb a c b).trans_eq (by ring))
    rwa [integral_const_mul] at this
  have h2 : ∀ a, ‖∫ c, ∫ b, f a c b‖ ≤ K * uu a * (∫ t, uu t) * ∫ t, gg t := by
    intro a
    have := norm_integral_le_of_norm_le
      ((integrable_gg_add a).const_mul (K * uu a * ∫ t, uu t))
      (Eventually.of_forall fun c => (h1 a c).trans_eq (by ring))
    rw [integral_const_mul, integral_gg_add] at this
    exact this.trans_eq (by ring)
  have := norm_integral_le_of_norm_le
    (integrable_uu.const_mul (K * (∫ t, uu t) * ∫ t, gg t))
    (Eventually.of_forall fun a => (h2 a).trans_eq (by ring))
  rw [integral_const_mul] at this
  exact this.trans_eq (by ring)

/-- `‖∫ a ∫ c f‖ ≤ K ∫u ∫γ` when `‖f a c‖ ≤ K u a γ(a + c)`. -/
lemma norm_iter2_le {f : ℝ → ℝ → ℂ} {K : ℝ}
    (hb : ∀ a c, ‖f a c‖ ≤ K * (uu a * gg (a + c))) :
    ‖∫ a, ∫ c, f a c‖ ≤ K * ((∫ t, uu t) * ∫ t, gg t) := by
  have h2 : ∀ a, ‖∫ c, f a c‖ ≤ K * uu a * ∫ t, gg t := by
    intro a
    have := norm_integral_le_of_norm_le ((integrable_gg_add a).const_mul (K * uu a))
      (Eventually.of_forall fun c => (hb a c).trans_eq (by ring))
    rwa [integral_const_mul, integral_gg_add] at this
  have := norm_integral_le_of_norm_le (integrable_uu.const_mul (K * ∫ t, gg t))
    (Eventually.of_forall fun a => (h2 a).trans_eq (by ring))
  rw [integral_const_mul] at this
  exact this.trans_eq (by ring)

/-- Inner part of `norm_iter3_le`: `‖∫ c ∫ b f c b‖ ≤ K u(a) ∫u ∫γ`. -/
lemma norm_iter2_inner_le {f : ℝ → ℝ → ℂ} {K a : ℝ}
    (hb : ∀ c b, ‖f c b‖ ≤ K * (uu a * uu b * gg (a + c))) :
    ‖∫ c, ∫ b, f c b‖ ≤ K * uu a * ((∫ t, uu t) * ∫ t, gg t) := by
  have h1 : ∀ c, ‖∫ b, f c b‖ ≤ K * uu a * gg (a + c) * ∫ t, uu t := by
    intro c
    have := norm_integral_le_of_norm_le ((integrable_uu.const_mul (K * uu a * gg (a + c))))
      (Eventually.of_forall fun b => (hb c b).trans_eq (by ring))
    rwa [integral_const_mul] at this
  have := norm_integral_le_of_norm_le
    ((integrable_gg_add a).const_mul (K * uu a * ∫ t, uu t))
    (Eventually.of_forall fun c => (h1 c).trans_eq (by ring))
  rw [integral_const_mul, integral_gg_add] at this
  exact this.trans_eq (by ring)

/-- `‖∫ c f c‖ ≤ K u(a) ∫γ` when `‖f c‖ ≤ K u(a) γ(a + c)`. -/
lemma norm_iter1_inner_le {f : ℝ → ℂ} {K a : ℝ}
    (hb : ∀ c, ‖f c‖ ≤ K * (uu a * gg (a + c))) :
    ‖∫ c, f c‖ ≤ K * uu a * ∫ t, gg t := by
  have := norm_integral_le_of_norm_le ((integrable_gg_add a).const_mul (K * uu a))
    (Eventually.of_forall fun c => (hb c).trans_eq (by ring))
  rwa [integral_const_mul, integral_gg_add] at this

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Bound: the principal-row integrand and its majorant

`Phi ξ w z = E(ξ,w,z) M(z) Ŵ(w) ζ(6z) ζ(w) G(ξ,w,z)` with `ζ(s) = R(s)/(s − 1)`, where
`E = X^{1/2−z} Z^{ξ+z−1} Y^{w−1} e^{(ξ+z−1)²}`; `Aw` and `Bz` are the numerators at the poles
`w = 1` and `z = 1/6`. -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

/-- The `Z`-dependent factor `X^{1/2−z} Z^{ξ+z−1} Y^{w−1} e^{(ξ+z−1)²}` of (7.10). -/
def Ef (X Y Z : ℝ) (ξ w z : ℂ) : ℂ :=
  (X : ℂ) ^ ((1 / 2 : ℂ) - z) * (Z : ℂ) ^ (ξ + z - 1) * (Y : ℂ) ^ (w - 1) * cexp ((ξ + z - 1) ^ 2)

/-- The principal-row integrand. -/
def Phi (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (ξ w z : ℂ) : ℂ :=
  Ef X Y Z ξ w z * M z * Wh w * (R (6 * z) / (6 * z - 1)) * (R w / (w - 1)) * G ξ w z

/-- The numerator at the pole `w = 1`: `Phi = Aw / (w − 1)`. -/
def Aw (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (ξ w z : ℂ) : ℂ :=
  Ef X Y Z ξ w z * M z * Wh w * (R (6 * z) / (6 * z - 1)) * R w * G ξ w z

/-- The numerator at the pole `z = 1/6` of `Aw ξ 1 z`. -/
def Bz (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (ξ z : ℂ) : ℂ :=
  Ef X Y Z ξ 1 z * M z * Wh 1 * (R (6 * z) / 6) * R 1 * G ξ 1 z

lemma Phi_eq (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (ξ w z : ℂ) :
    Phi X Y Z M Wh R G ξ w z = Aw X Y Z M Wh R G ξ w z / (w - 1) := by
  unfold Phi Aw; ring

lemma Aw_one_eq (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (ξ z : ℂ) :
    Aw X Y Z M Wh R G ξ 1 z = Bz X Y Z M Wh R G ξ z / (z - ((1 / 6 : ℝ) : ℂ)) := by
  unfold Aw Bz
  have h : (6 * z - 1) = 6 * (z - ((1 / 6 : ℝ) : ℂ)) := by push_cast; ring
  rw [h, ← div_div]
  ring

def sig1 : ℝ := 10001 / 10000

/-- The open box on which `G` is continuous and separately holomorphic. -/
def Om : Set (ℂ × ℂ × ℂ) :=
  {p | 1 < p.1.re ∧ p.1.re < 5 ∧ 9 / 10 < p.2.1.re ∧ p.2.1.re < 5 ∧ 3 / 20 < p.2.2.re ∧
    p.2.2.re < 3}

/-- The analytic hypotheses on the weights, the regularized zeta function and the correction. -/
structure Hyp (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) : Prop where
  hM : DifferentiableOn ℂ M {z | 0 < z.re}
  hMd : ∀ A : ℝ, ∃ C : ℝ, ∀ z : ℂ, 4 / 25 ≤ z.re → z.re ≤ 2 → ‖M z‖ ≤ C * (1 + |z.im|) ^ (-A)
  hW : Differentiable ℂ Wh
  hWd : ∀ A : ℝ, ∃ C : ℝ, ∀ w : ℂ, 19 / 20 ≤ w.re → w.re ≤ 4 →
    ‖Wh w‖ ≤ C * (1 + |w.im|) ^ (-A)
  hR : Differentiable ℂ R
  hRg : ∃ C k : ℝ, 0 ≤ k ∧ ∀ s : ℂ, 9 / 10 ≤ s.re → s.re ≤ 12 → ‖R s‖ ≤ C * (2 + |s.im|) ^ k
  hGc : ContinuousOn (fun p : ℂ × ℂ × ℂ => G p.1 p.2.1 p.2.2) Om
  hG1 : ∀ p ∈ Om, DifferentiableAt ℂ (fun x => G x p.2.1 p.2.2) p.1
  hG2 : ∀ p ∈ Om, DifferentiableAt ℂ (fun x => G p.1 x p.2.2) p.2.1
  hG3 : ∀ p ∈ Om, DifferentiableAt ℂ (fun x => G p.1 p.2.1 x) p.2.2
  hGb : ∃ B : ℝ, ∀ ξ w z : ℂ, sig1 ≤ ξ.re → ξ.re ≤ 4 → 19 / 20 ≤ w.re → w.re ≤ 4 →
    4 / 25 ≤ z.re → z.re ≤ 2 → ‖G ξ w z‖ ≤ B

/-! ### Elementary bounds -/

lemma norm_cexp_sq (u : ℂ) : ‖cexp (u ^ 2)‖ = Real.exp (u.re ^ 2 - u.im ^ 2) := by
  rw [Complex.norm_exp]; congr 1; simp [sq]

lemma norm_Ef {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (ξ w z : ℂ) :
    ‖Ef X Y Z ξ w z‖ = X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) * Y ^ (w.re - 1) *
      Real.exp ((ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2) := by
  unfold Ef
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_cpow_eq_rpow_re_of_pos hY, norm_cexp_sq]
  simp

/-- `(2 + λ|t|)^k (1+|t|)^{−(k+2)} ≤ (2λ)^k u(t)` for `λ ≥ 1`, `k ≥ 0`. -/
lemma poly_le {k l : ℝ} (hk : 0 ≤ k) (hl : 1 ≤ l) (t : ℝ) :
    (2 + l * |t|) ^ k * (1 + |t|) ^ (-(k + 2)) ≤ (2 * l) ^ k * uu t := by
  have h1 : 0 < 1 + |t| := by positivity
  have h2 : 2 + l * |t| ≤ (2 * l) * (1 + |t|) := by nlinarith [abs_nonneg t]
  have h3 : (2 + l * |t|) ^ k ≤ (2 * l) ^ k * (1 + |t|) ^ k := by
    rw [← Real.mul_rpow (by positivity) h1.le]
    exact Real.rpow_le_rpow (by positivity) h2 hk
  have h4 : (1 + |t|) ^ k * (1 + |t|) ^ (-(k + 2)) = ((1 + |t|) ^ 2)⁻¹ := by
    rw [← Real.rpow_add h1]
    rw [show k + -(k + 2) = -(2 : ℝ) by ring, Real.rpow_neg h1.le]
    norm_cast
  have h5 : ((1 + |t|) ^ 2)⁻¹ ≤ uu t := by
    unfold uu
    apply inv_anti₀ (by positivity)
    nlinarith [sq_abs t, abs_nonneg t]
  calc (2 + l * |t|) ^ k * (1 + |t|) ^ (-(k + 2))
      ≤ (2 * l) ^ k * (1 + |t|) ^ k * (1 + |t|) ^ (-(k + 2)) := by gcongr
    _ = (2 * l) ^ k * ((1 + |t|) ^ k * (1 + |t|) ^ (-(k + 2))) := by ring
    _ ≤ (2 * l) ^ k * uu t := by rw [h4]; gcongr

/-- The `z`-factor `M(z) ζ(6z)`. -/
lemma bound_Fz {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 4 / 25 ≤ z.re → z.re ≤ 2 → 1 / 25 ≤ ‖6 * z - 1‖ →
      ‖M z * (R (6 * z) / (6 * z - 1))‖ ≤ K * uu z.im := by
  obtain ⟨CR, k, hk, hR⟩ := h.hRg
  obtain ⟨CM, hM⟩ := h.hMd (k + 2)
  refine ⟨max CM 0 * (25 * max CR 0) * (2 * 6) ^ k, by positivity, fun z h1 h2 h3 => ?_⟩
  have hR' := hR (6 * z) (by simp; linarith) (by simp; linarith)
  have hM' := hM z h1 h2
  have him : (6 * z).im = 6 * z.im := by simp
  rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)] at hR'
  have hd : ‖R (6 * z) / (6 * z - 1)‖ ≤ 25 * max CR 0 * (2 + 6 * |z.im|) ^ k := by
    rw [norm_div]
    have hp : 0 < ‖6 * z - 1‖ := by linarith
    rw [div_le_iff₀ hp]
    have hRR : ‖R (6 * z)‖ ≤ max CR 0 * (2 + 6 * |z.im|) ^ k :=
      hR'.trans (by gcongr; exact le_max_left _ _)
    have hpos : 0 ≤ max CR 0 * (2 + 6 * |z.im|) ^ k := by positivity
    nlinarith
  have hMM : ‖M z‖ ≤ max CM 0 * (1 + |z.im|) ^ (-(k + 2)) :=
    hM'.trans (by gcongr; exact le_max_left _ _)
  rw [norm_mul]
  calc ‖M z‖ * ‖R (6 * z) / (6 * z - 1)‖
      ≤ (max CM 0 * (1 + |z.im|) ^ (-(k + 2))) * (25 * max CR 0 * (2 + 6 * |z.im|) ^ k) :=
        mul_le_mul hMM hd (norm_nonneg _) (by positivity)
    _ = max CM 0 * (25 * max CR 0) * ((2 + 6 * |z.im|) ^ k * (1 + |z.im|) ^ (-(k + 2))) := by
        ring
    _ ≤ max CM 0 * (25 * max CR 0) * ((2 * 6) ^ k * uu z.im) :=
        mul_le_mul_of_nonneg_left (poly_le hk (by norm_num) _) (by positivity)
    _ = _ := by ring

/-- The `w`-factor `Ŵ(w) ζ(w)`. -/
lemma bound_Fw {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, 19 / 20 ≤ w.re → w.re ≤ 4 → 1 / 20 ≤ ‖w - 1‖ →
      ‖Wh w * (R w / (w - 1))‖ ≤ K * uu w.im := by
  obtain ⟨CR, k, hk, hR⟩ := h.hRg
  obtain ⟨CW, hW⟩ := h.hWd (k + 2)
  refine ⟨max CW 0 * (20 * max CR 0) * (2 * 1) ^ k, by positivity, fun w h1 h2 h3 => ?_⟩
  have hR' := hR w (by linarith) (by linarith)
  have hd : ‖R w / (w - 1)‖ ≤ 20 * max CR 0 * (2 + 1 * |w.im|) ^ k := by
    rw [norm_div]
    have hp : 0 < ‖w - 1‖ := by linarith
    rw [div_le_iff₀ hp, one_mul]
    have hRR : ‖R w‖ ≤ max CR 0 * (2 + |w.im|) ^ k :=
      hR'.trans (by gcongr; exact le_max_left _ _)
    have hpos : 0 ≤ max CR 0 * (2 + |w.im|) ^ k := by positivity
    nlinarith
  have hWW : ‖Wh w‖ ≤ max CW 0 * (1 + |w.im|) ^ (-(k + 2)) :=
    (hW w h1 h2).trans (by gcongr; exact le_max_left _ _)
  rw [norm_mul]
  calc ‖Wh w‖ * ‖R w / (w - 1)‖
      ≤ (max CW 0 * (1 + |w.im|) ^ (-(k + 2))) * (20 * max CR 0 * (2 + 1 * |w.im|) ^ k) :=
        mul_le_mul hWW hd (norm_nonneg _) (by positivity)
    _ = max CW 0 * (20 * max CR 0) * ((2 + 1 * |w.im|) ^ k * (1 + |w.im|) ^ (-(k + 2))) := by
        ring
    _ ≤ max CW 0 * (20 * max CR 0) * ((2 * 1) ^ k * uu w.im) :=
        mul_le_mul_of_nonneg_left (poly_le hk le_rfl _) (by positivity)
    _ = _ := by ring

lemma sq_re_le {a c : ℝ} (ha1 : sig1 ≤ a) (ha2 : a ≤ 4) (hc1 : 4 / 25 ≤ c) (hc2 : c ≤ 2) :
    (a + c - 1) ^ 2 ≤ 25 := by
  unfold sig1 at ha1; nlinarith

/-- The majorant of the integrand on the box, away from the poles. -/
theorem key_Phi {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z → ∀ ξ w z : ℂ,
      sig1 ≤ ξ.re → ξ.re ≤ 4 → 19 / 20 ≤ w.re → w.re ≤ 4 → 4 / 25 ≤ z.re → z.re ≤ 2 →
      1 / 20 ≤ ‖w - 1‖ → 1 / 25 ≤ ‖6 * z - 1‖ →
      ‖Phi X Y Z M Wh R G ξ w z‖ ≤
        K * (X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) * Y ^ (w.re - 1)) *
          (uu ξ.im * uu w.im * gg (ξ.im + z.im)) := by
  obtain ⟨Kz, hKz, hz⟩ := bound_Fz h
  obtain ⟨Kw, hKw, hw⟩ := bound_Fw h
  obtain ⟨B, hB⟩ := h.hGb
  refine ⟨Real.exp 25 * Kz * Kw * max B 0 * 4, by positivity, ?_⟩
  intro X Y Z hX hY hZ ξ w z h1 h2 h3 h4 h5 h6 h7 h8
  have hE := norm_Ef hX hY hZ ξ w z
  have hexp : Real.exp ((ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2) ≤
      Real.exp 25 * Real.exp (-(ξ.im + z.im) ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have := sq_re_le h1 h2 h5 h6; linarith
  have hfz := hz z h5 h6 h8
  have hfw := hw w h3 h4 h7
  have hG : ‖G ξ w z‖ ≤ max B 0 := (hB ξ w z h1 h2 h3 h4 h5 h6).trans (le_max_left _ _)
  have hrw : Phi X Y Z M Wh R G ξ w z =
      Ef X Y Z ξ w z * (M z * (R (6 * z) / (6 * z - 1))) * (Wh w * (R w / (w - 1))) *
        G ξ w z := by unfold Phi; ring
  rw [hrw, norm_mul, norm_mul, norm_mul, hE]
  set P := X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) * Y ^ (w.re - 1)
  have hP : 0 ≤ P := by positivity
  have hm := exp_mul_uu_le ξ.im z.im
  have hgg := gg_pos (ξ.im + z.im)
  have huw := uu_pos w.im
  have hu1 := uu_pos ξ.im
  have huz := uu_pos z.im
  calc P * Real.exp ((ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2) *
        ‖M z * (R (6 * z) / (6 * z - 1))‖ * ‖Wh w * (R w / (w - 1))‖ * ‖G ξ w z‖
      ≤ P * (Real.exp 25 * Real.exp (-(ξ.im + z.im) ^ 2)) * (Kz * uu z.im) * (Kw * uu w.im) *
          max B 0 := by gcongr
    _ = P * Real.exp 25 * Kz * Kw * max B 0 * uu w.im *
          (Real.exp (-(ξ.im + z.im) ^ 2) * uu z.im) := by ring
    _ ≤ P * Real.exp 25 * Kz * Kw * max B 0 * uu w.im * (4 * uu ξ.im * gg (ξ.im + z.im)) := by
        gcongr
    _ = _ := by ring

/-- The majorant of the `w = 1` residue. -/
theorem key_Psi {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z → ∀ ξ z : ℂ,
      sig1 ≤ ξ.re → ξ.re ≤ 4 → 4 / 25 ≤ z.re → z.re ≤ 2 → 1 / 25 ≤ ‖6 * z - 1‖ →
      ‖Aw X Y Z M Wh R G ξ 1 z‖ ≤
        K * (X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1)) * (uu ξ.im * gg (ξ.im + z.im)) := by
  obtain ⟨Kz, hKz, hz⟩ := bound_Fz h
  obtain ⟨B, hB⟩ := h.hGb
  refine ⟨Real.exp 25 * Kz * ‖Wh 1 * R 1‖ * max B 0 * 4, by positivity, ?_⟩
  intro X Y Z hX hY hZ ξ z h1 h2 h5 h6 h8
  have hE := norm_Ef hX hY hZ ξ 1 z
  have hexp : Real.exp ((ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2) ≤
      Real.exp 25 * Real.exp (-(ξ.im + z.im) ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have := sq_re_le h1 h2 h5 h6; linarith
  have hfz := hz z h5 h6 h8
  have hG : ‖G ξ 1 z‖ ≤ max B 0 :=
    (hB ξ 1 z h1 h2 (by norm_num) (by norm_num) h5 h6).trans (le_max_left _ _)
  have hrw : Aw X Y Z M Wh R G ξ 1 z =
      Ef X Y Z ξ 1 z * (M z * (R (6 * z) / (6 * z - 1))) * (Wh 1 * R 1) * G ξ 1 z := by
    unfold Aw; ring
  rw [hrw, norm_mul, norm_mul, norm_mul, hE]
  simp only [one_re, sub_self, Real.rpow_zero, mul_one]
  set P := X ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1)
  have hP : 0 ≤ P := by positivity
  have hm := exp_mul_uu_le ξ.im z.im
  have hgg := gg_pos (ξ.im + z.im)
  have hu1 := uu_pos ξ.im
  have huz := uu_pos z.im
  calc P * Real.exp ((ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2) *
        ‖M z * (R (6 * z) / (6 * z - 1))‖ * ‖Wh 1 * R 1‖ * ‖G ξ 1 z‖
      ≤ P * (Real.exp 25 * Real.exp (-(ξ.im + z.im) ^ 2)) * (Kz * uu z.im) * ‖Wh 1 * R 1‖ *
          max B 0 := by gcongr
    _ = P * Real.exp 25 * Kz * ‖Wh 1 * R 1‖ * max B 0 *
          (Real.exp (-(ξ.im + z.im) ^ 2) * uu z.im) := by ring
    _ ≤ P * Real.exp 25 * Kz * ‖Wh 1 * R 1‖ * max B 0 * (4 * uu ξ.im * gg (ξ.im + z.im)) := by
        gcongr
    _ = _ := by ring

/-- The majorant of the double residue. -/
theorem key_Bz {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ} (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z → ∀ ξ : ℂ,
      sig1 ≤ ξ.re → ξ.re ≤ 4 →
      ‖Bz X Y Z M Wh R G ξ ((1 / 6 : ℝ) : ℂ)‖ ≤
        K * (X ^ (1 / 2 - (1 / 6 : ℝ)) * Z ^ (ξ.re + (1 / 6 : ℝ) - 1)) * uu ξ.im := by
  obtain ⟨B, hB⟩ := h.hGb
  refine ⟨Real.exp 25 * ‖M ((1 / 6 : ℝ) : ℂ) * Wh 1 * (R (6 * ((1 / 6 : ℝ) : ℂ)) / 6) * R 1‖ *
    max B 0, by positivity, ?_⟩
  intro X Y Z hX hY hZ ξ h1 h2
  have hE := norm_Ef hX hY hZ ξ 1 ((1 / 6 : ℝ) : ℂ)
  have hexp : Real.exp ((ξ.re + ((1 / 6 : ℝ) : ℂ).re - 1) ^ 2 -
      (ξ.im + ((1 / 6 : ℝ) : ℂ).im) ^ 2) ≤ Real.exp 25 * uu ξ.im := by
    simp only [ofReal_re, ofReal_im, add_zero]
    have hsq : (ξ.re + 1 / 6 - 1) ^ 2 ≤ 25 := sq_re_le h1 h2 (by norm_num) (by norm_num)
    have he : Real.exp (-(ξ.im ^ 2)) ≤ uu ξ.im := by
      unfold uu
      rw [Real.exp_neg]
      apply inv_anti₀ (by positivity)
      have := Real.add_one_le_exp (ξ.im ^ 2); linarith
    calc Real.exp ((ξ.re + 1 / 6 - 1) ^ 2 - ξ.im ^ 2)
        = Real.exp ((ξ.re + 1 / 6 - 1) ^ 2) * Real.exp (-(ξ.im ^ 2)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 25 * uu ξ.im := by
          gcongr
  have hG : ‖G ξ 1 ((1 / 6 : ℝ) : ℂ)‖ ≤ max B 0 :=
    (hB ξ 1 _ h1 h2 (by norm_num) (by norm_num) (by simp; norm_num) (by simp; norm_num)).trans
      (le_max_left _ _)
  have hrw : Bz X Y Z M Wh R G ξ ((1 / 6 : ℝ) : ℂ) =
      Ef X Y Z ξ 1 ((1 / 6 : ℝ) : ℂ) *
        (M ((1 / 6 : ℝ) : ℂ) * Wh 1 * (R (6 * ((1 / 6 : ℝ) : ℂ)) / 6) * R 1) *
        G ξ 1 ((1 / 6 : ℝ) : ℂ) := by
    unfold Bz; ring
  rw [hrw, norm_mul, norm_mul, hE]
  simp only [one_re, sub_self, Real.rpow_zero, mul_one, ofReal_re, ofReal_im, add_zero]
  set P := X ^ (1 / 2 - (1 / 6 : ℝ)) * Z ^ (ξ.re + (1 / 6 : ℝ) - 1)
  have hP : 0 ≤ P := by positivity
  set c := ‖M ((1 / 6 : ℝ) : ℂ) * Wh 1 * (R (6 * ((1 / 6 : ℝ) : ℂ)) / 6) * R 1‖
  have hc : 0 ≤ c := norm_nonneg _
  have hexp' := hexp
  simp only [ofReal_re, ofReal_im, add_zero] at hexp'
  have hu1 := uu_pos ξ.im
  calc P * Real.exp ((ξ.re + 1 / 6 - 1) ^ 2 - ξ.im ^ 2) * c * ‖G ξ 1 ((1 / 6 : ℝ) : ℂ)‖
      ≤ P * (Real.exp 25 * uu ξ.im) * c * max B 0 := by gcongr
    _ = Real.exp 25 * c * max B 0 * P * uu ξ.im := by ring

end

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Reg: continuity of the integrand on lines and holomorphy on strips -/

open Complex MeasureTheory Filter Topology Set

set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

lemma rpow_le_add {x e e1 e2 : ℝ} (hx : 0 < x) (h1 : e1 ≤ e) (h2 : e ≤ e2) :
    x ^ e ≤ x ^ e1 + x ^ e2 := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hx h h1
    linarith [Real.rpow_nonneg hx.le e2]
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    linarith [Real.rpow_nonneg hx.le e1]

lemma line_re (c t : ℝ) : ((c : ℂ) + t * I).re = c := by simp

lemma line_im (c t : ℝ) : ((c : ℂ) + t * I).im = t := by simp

lemma continuous_line (c : ℝ) : Continuous fun t : ℝ => (c : ℂ) + t * I := by fun_prop

variable {X Y Z : ℝ} {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ}

section Cont

variable {α : Type*} [TopologicalSpace α] {ξf wf zf : α → ℂ}

lemma cont_G (h : Hyp M Wh R G) (hξ : Continuous ξf) (hw : Continuous wf) (hz : Continuous zf)
    (hm : ∀ x, (ξf x, wf x, zf x) ∈ Om) : Continuous fun x => G (ξf x) (wf x) (zf x) :=
  h.hGc.comp_continuous (hξ.prodMk (hw.prodMk hz)) hm

lemma cont_Ef (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hξ : Continuous ξf) (hw : Continuous wf) (hz : Continuous zf) :
    Continuous fun x => Ef X Y Z (ξf x) (wf x) (zf x) := by
  unfold Ef
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hY' : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  refine ((((continuous_const.sub hz).const_cpow (Or.inl hX')).mul
    (((hξ.add hz).sub continuous_const).const_cpow (Or.inl hZ'))).mul
    ((hw.sub continuous_const).const_cpow (Or.inl hY'))).mul ?_
  exact Complex.continuous_exp.comp (((hξ.add hz).sub continuous_const).pow 2)

lemma cont_M (h : Hyp M Wh R G) (hz : Continuous zf) (hz0 : ∀ x, 0 < (zf x).re) :
    Continuous fun x => M (zf x) :=
  h.hM.continuousOn.comp_continuous hz hz0

lemma cont_Phi (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hξ : Continuous ξf) (hw : Continuous wf) (hz : Continuous zf)
    (hz0 : ∀ x, 0 < (zf x).re) (hw1 : ∀ x, wf x - 1 ≠ 0) (hz1 : ∀ x, 6 * zf x - 1 ≠ 0)
    (hm : ∀ x, (ξf x, wf x, zf x) ∈ Om) :
    Continuous fun x => Phi X Y Z M Wh R G (ξf x) (wf x) (zf x) := by
  unfold Phi
  have h6 : Continuous fun x => 6 * zf x := continuous_const.mul hz
  exact (((((cont_Ef hX hY hZ hξ hw hz).mul (cont_M h hz hz0)).mul
    (h.hW.continuous.comp hw)).mul ((h.hR.continuous.comp h6).div (h6.sub continuous_const)
      hz1)).mul ((h.hR.continuous.comp hw).div (hw.sub continuous_const) hw1)).mul
    (cont_G h hξ hw hz hm)

lemma cont_Aw1 (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hξ : Continuous ξf) (hz : Continuous zf)
    (hz0 : ∀ x, 0 < (zf x).re) (hz1 : ∀ x, 6 * zf x - 1 ≠ 0)
    (hm : ∀ x, (ξf x, (1 : ℂ), zf x) ∈ Om) :
    Continuous fun x => Aw X Y Z M Wh R G (ξf x) 1 (zf x) := by
  unfold Aw
  have h6 : Continuous fun x => 6 * zf x := continuous_const.mul hz
  exact (((((cont_Ef hX hY hZ hξ continuous_const hz).mul (cont_M h hz hz0)).mul
    continuous_const).mul ((h.hR.continuous.comp h6).div (h6.sub continuous_const)
      hz1)).mul continuous_const).mul
    (cont_G h hξ continuous_const hz hm)

lemma cont_Bz (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hξ : Continuous ξf) (hz : Continuous zf)
    (hz0 : ∀ x, 0 < (zf x).re) (hm : ∀ x, (ξf x, (1 : ℂ), zf x) ∈ Om) :
    Continuous fun x => Bz X Y Z M Wh R G (ξf x) (zf x) := by
  unfold Bz
  have h6 : Continuous fun x => 6 * zf x := continuous_const.mul hz
  exact (((((cont_Ef hX hY hZ hξ continuous_const hz).mul (cont_M h hz hz0)).mul
    continuous_const).mul ((h.hR.continuous.comp h6).div_const 6)).mul continuous_const).mul
    (cont_G h hξ continuous_const hz hm)

end Cont

section Diff

lemma diffAt_M (h : Hyp M Wh R G) {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ M z :=
  h.hM.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

lemma diff_Phi_xi (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {w z : ℂ}
    {S : Set ℂ} (hm : ∀ ξ ∈ S, (ξ, w, z) ∈ Om) :
    DifferentiableOn ℂ (fun ξ => Phi X Y Z M Wh R G ξ w z) S := by
  intro ξ hξ
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Phi Ef
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hG := h.hG1 _ (hm ξ hξ)
  simp only at hG
  have h1 : DifferentiableAt ℂ (fun ξ : ℂ => (Z : ℂ) ^ (ξ + z - 1)) ξ :=
    ((differentiableAt_id.add_const z).sub_const 1).const_cpow (Or.inl hZ')
  have h2 : DifferentiableAt ℂ (fun ξ : ℂ => cexp ((ξ + z - 1) ^ 2)) ξ :=
    (((differentiableAt_id.add_const z).sub_const 1).pow 2).cexp
  exact (((((((differentiableAt_const _).mul h1).mul (differentiableAt_const _)).mul h2).mul
    (differentiableAt_const _)).mul (differentiableAt_const _)).mul
    (differentiableAt_const _)).mul (differentiableAt_const _) |>.mul hG

lemma diff_Phi_z (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {ξ w : ℂ}
    {S : Set ℂ} (hm : ∀ z ∈ S, (ξ, w, z) ∈ Om) (hz0 : ∀ z ∈ S, 0 < z.re)
    (hz1 : ∀ z ∈ S, 6 * z - 1 ≠ 0) :
    DifferentiableOn ℂ (fun z => Phi X Y Z M Wh R G ξ w z) S := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Phi Ef
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hG := h.hG3 _ (hm z hz)
  simp only at hG
  have h0 : DifferentiableAt ℂ (fun z : ℂ => (X : ℂ) ^ ((1 / 2 : ℂ) - z)) z :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hX')
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Z : ℂ) ^ (ξ + z - 1)) z :=
    (((differentiableAt_const _).add differentiableAt_id).sub_const 1).const_cpow (Or.inl hZ')
  have h2 : DifferentiableAt ℂ (fun z : ℂ => cexp ((ξ + z - 1) ^ 2)) z :=
    ((((differentiableAt_const _).add differentiableAt_id).sub_const 1).pow 2).cexp
  have h6 : DifferentiableAt ℂ (fun z : ℂ => 6 * z) z := differentiableAt_id.const_mul 6
  have h3 : DifferentiableAt ℂ (fun z : ℂ => R (6 * z) / (6 * z - 1)) z :=
    ((h.hR _).comp z h6).div (h6.sub_const 1) (hz1 z hz)
  exact (((((h0.mul h1).mul (differentiableAt_const _)).mul h2).mul (diffAt_M h (hz0 z hz))).mul
    (differentiableAt_const _)).mul h3 |>.mul (differentiableAt_const _) |>.mul hG

lemma diff_Aw_w (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {ξ z : ℂ}
    {S : Set ℂ} (hm : ∀ w ∈ S, (ξ, w, z) ∈ Om) :
    DifferentiableOn ℂ (fun w => Aw X Y Z M Wh R G ξ w z) S := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Aw Ef
  have hY' : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hG := h.hG2 _ (hm w hw)
  simp only at hG
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ (w - 1)) w :=
    (differentiableAt_id.sub_const 1).const_cpow (Or.inl hY')
  exact (((((((differentiableAt_const _).mul (differentiableAt_const _)).mul h1).mul
    (differentiableAt_const _)).mul (differentiableAt_const _)).mul (h.hW w)).mul
    (differentiableAt_const _)).mul (h.hR w) |>.mul hG

lemma diff_Bz_z (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {ξ : ℂ}
    {S : Set ℂ} (hm : ∀ z ∈ S, (ξ, (1 : ℂ), z) ∈ Om) (hz0 : ∀ z ∈ S, 0 < z.re) :
    DifferentiableOn ℂ (fun z => Bz X Y Z M Wh R G ξ z) S := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Bz Ef
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hG := h.hG3 _ (hm z hz)
  simp only at hG
  have h0 : DifferentiableAt ℂ (fun z : ℂ => (X : ℂ) ^ ((1 / 2 : ℂ) - z)) z :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hX')
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Z : ℂ) ^ (ξ + z - 1)) z :=
    (((differentiableAt_const _).add differentiableAt_id).sub_const 1).const_cpow (Or.inl hZ')
  have h2 : DifferentiableAt ℂ (fun z : ℂ => cexp ((ξ + z - 1) ^ 2)) z :=
    ((((differentiableAt_const _).add differentiableAt_id).sub_const 1).pow 2).cexp
  have h6 : DifferentiableAt ℂ (fun z : ℂ => 6 * z) z := differentiableAt_id.const_mul 6
  have h3 : DifferentiableAt ℂ (fun z : ℂ => R (6 * z) / 6) z :=
    ((h.hR _).comp z h6).div_const 6
  exact (((((h0.mul h1).mul (differentiableAt_const _)).mul h2).mul (diffAt_M h (hz0 z hz))).mul
    (differentiableAt_const _)).mul h3 |>.mul (differentiableAt_const _) |>.mul hG

lemma diff_Bz_xi (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {z : ℂ}
    {S : Set ℂ} (hm : ∀ ξ ∈ S, (ξ, (1 : ℂ), z) ∈ Om) :
    DifferentiableOn ℂ (fun ξ => Bz X Y Z M Wh R G ξ z) S := by
  intro ξ hξ
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Bz Ef
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hG := h.hG1 _ (hm ξ hξ)
  simp only at hG
  have h1 : DifferentiableAt ℂ (fun ξ : ℂ => (Z : ℂ) ^ (ξ + z - 1)) ξ :=
    ((differentiableAt_id.add_const z).sub_const 1).const_cpow (Or.inl hZ')
  have h2 : DifferentiableAt ℂ (fun ξ : ℂ => cexp ((ξ + z - 1) ^ 2)) ξ :=
    (((differentiableAt_id.add_const z).sub_const 1).pow 2).cexp
  exact ((((((((differentiableAt_const _).mul h1).mul (differentiableAt_const _)).mul h2).mul
    (differentiableAt_const _)).mul (differentiableAt_const _)).mul
    (differentiableAt_const _)).mul (differentiableAt_const _)).mul hG

end Diff

end

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Contour: the contour moves of the principal row

1. `step_xi`: ξ from 4 to σ₁ (Fubini on ℝ³, then a pole-free shift);
2. `step_z`: z from 2 to 1/5;
3. `step_w`: w from 4 to 19/20 (pole at 1) and, in the residue, z from 1/5 to 4/25 (pole at 1/6);
4. `step_main`: the double residue's ξ-line from σ₁ to 2. -/

open Complex MeasureTheory Filter Topology Set

set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

lemma norm_line_sub_ge (c t d : ℝ) : |c - d| ≤ ‖((c : ℂ) + t * I) - d‖ := by
  have := Complex.abs_re_le_norm (((c : ℂ) + t * I) - d)
  simpa using this

lemma norm_six_line_sub_ge (c t : ℝ) : |6 * c - 1| ≤ ‖6 * ((c : ℂ) + t * I) - 1‖ := by
  have := Complex.abs_re_le_norm (6 * ((c : ℂ) + t * I) - 1)
  simpa using this

lemma mem_Om {ξ w z : ℂ} (h1 : 1 < ξ.re) (h2 : ξ.re < 5) (h3 : 9 / 10 < w.re) (h4 : w.re < 5)
    (h5 : 3 / 20 < z.re) (h6 : z.re < 3) : (ξ, w, z) ∈ Om := ⟨h1, h2, h3, h4, h5, h6⟩

lemma sig1_gt : 1 < sig1 := by unfold sig1; norm_num

lemma sig1_le : sig1 ≤ 2 := by unfold sig1; norm_num

/-- The integrand on the lines `(a, b, c)`. -/
def L3 (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (a b c t1 t2 t3 : ℝ) : ℂ :=
  Phi X Y Z M Wh R G ((a : ℂ) + t1 * I) ((b : ℂ) + t2 * I) ((c : ℂ) + t3 * I)

/-- The `w = 1` residue on the lines `(a, c)`. -/
def L2 (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (a c t1 t3 : ℝ) : ℂ :=
  Aw X Y Z M Wh R G ((a : ℂ) + t1 * I) 1 ((c : ℂ) + t3 * I)

/-- The double residue on the line `a`. -/
def L1 (X Y Z : ℝ) (M Wh R : ℂ → ℂ) (G : ℂ → ℂ → ℂ → ℂ) (a t1 : ℝ) : ℂ :=
  Bz X Y Z M Wh R G ((a : ℂ) + t1 * I) ((1 / 6 : ℝ) : ℂ)

variable {X Y Z : ℝ} {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ}

/-- Step 1: the ξ-line moves from 4 to σ₁. -/
theorem step_xi (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ, L3 X Y Z M Wh R G 4 4 2 t1 t2 t3 =
      ∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ, L3 X Y Z M Wh R G sig1 4 2 t1 t2 t3 := by
  obtain ⟨K, hK0, hK⟩ := key_Phi h
  have hw : ∀ t : ℝ, 1 / 20 ≤ ‖((4 : ℝ) : ℂ) + t * I - 1‖ := fun t => by
    have := norm_line_sub_ge 4 t 1; norm_num at this ⊢; linarith
  have hz : ∀ t : ℝ, 1 / 25 ≤ ‖6 * (((2 : ℝ) : ℂ) + t * I) - 1‖ := fun t => by
    have := norm_six_line_sub_ge 2 t; norm_num at this ⊢; linarith
  have hint : ∀ a : ℝ, sig1 ≤ a → a ≤ 4 → Integrable (fun p : ℝ × ℝ × ℝ =>
      L3 X Y Z M Wh R G a 4 2 p.1 p.2.1 p.2.2) (volume.prod (volume.prod volume)) := by
    intro a ha1 ha2
    have h1 := sig1_gt
    refine integrable_of_le_m3 (K := K * (X ^ (1 / 2 - (2 : ℝ)) * Z ^ (a + 2 - 1) *
      Y ^ ((4 : ℝ) - 1))) ?_ ?_
    · unfold L3
      refine cont_Phi h hX hY hZ ((continuous_line a).comp continuous_fst)
        ((continuous_line 4).comp (continuous_fst.comp continuous_snd))
        ((continuous_line 2).comp (continuous_snd.comp continuous_snd))
        (fun p => by simp) (fun p => ?_) (fun p => ?_) (fun p => mem_Om ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first
        | (intro h0; have := congrArg Complex.re h0; norm_num at this)
        | (simp; linarith)
        | (simp; norm_num)
    · intro p
      have := hK X Y Z hX hY hZ ((a : ℂ) + p.1 * I) (((4 : ℝ) : ℂ) + p.2.1 * I)
        (((2 : ℝ) : ℂ) + p.2.2 * I) (by simpa using ha1) (by simpa using ha2) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (hw _) (hz _)
      simpa [L3, mul_assoc] using this
  rw [swap3 (hint 4 (by unfold sig1; norm_num) le_rfl),
    swap3 (hint sig1 le_rfl (by unfold sig1; norm_num))]
  refine integral_congr_ae (Eventually.of_forall fun t2 => ?_)
  refine integral_congr_ae (Eventually.of_forall fun t3 => ?_)
  unfold L3
  set C := K * (X ^ (1 / 2 - (2 : ℝ)) * (Z ^ (sig1 + 2 - 1) + Z ^ ((4 : ℝ) + 2 - 1)) *
    Y ^ ((4 : ℝ) - 1)) * uu t2
  have hC : 0 ≤ C := by have := uu_pos t2; positivity
  refine (C3P_shift (g := fun t => C * uu t) (by unfold sig1; norm_num)
    (diff_Phi_xi h hX hY hZ fun ξ hξ => mem_Om (by linarith [sig1_gt, hξ.1]) (by linarith [hξ.2])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (integrable_uu.const_mul C) (by simpa using tendsto_uu_atTop.const_mul C)
    (by simpa using tendsto_uu_atBot.const_mul C) ?_).symm
  intro s hs1 hs2
  have hk := hK X Y Z hX hY hZ s (((4 : ℝ) : ℂ) + t2 * I) (((2 : ℝ) : ℂ) + t3 * I) hs1 (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hw t2) (hz t3)
  simp only [line_re, line_im] at hk
  refine hk.trans ?_
  have hZb : Z ^ (s.re + 2 - 1) ≤ Z ^ (sig1 + 2 - 1) + Z ^ ((4 : ℝ) + 2 - 1) :=
    rpow_le_add hZ (by linarith) (by linarith)
  have hg := gg_le_one (s.im + t3)
  have hu := uu_pos s.im
  have hu2 := uu_pos t2
  have hg0 := gg_pos (s.im + t3)
  calc K * (X ^ (1 / 2 - (2 : ℝ)) * Z ^ (s.re + 2 - 1) * Y ^ ((4 : ℝ) - 1)) *
        (uu s.im * uu t2 * gg (s.im + t3))
      ≤ K * (X ^ (1 / 2 - (2 : ℝ)) * (Z ^ (sig1 + 2 - 1) + Z ^ ((4 : ℝ) + 2 - 1)) *
          Y ^ ((4 : ℝ) - 1)) * (uu s.im * uu t2 * 1) := by gcongr
    _ = C * uu s.im := by simp only [C]; ring

/-- Step 2: the z-line moves from 2 to 1/5. -/
theorem step_z (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ, L3 X Y Z M Wh R G sig1 4 2 t1 t2 t3 =
      ∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ, L3 X Y Z M Wh R G sig1 4 (1 / 5) t1 t2 t3 := by
  obtain ⟨K, hK0, hK⟩ := key_Phi h
  refine integral_congr_ae (Eventually.of_forall fun t1 => ?_)
  refine integral_congr_ae (Eventually.of_forall fun t2 => ?_)
  unfold L3
  set C := K * ((X ^ (1 / 2 - (2 : ℝ)) + X ^ (1 / 2 - (1 / 5 : ℝ))) *
    (Z ^ (sig1 + 1 / 5 - 1) + Z ^ (sig1 + 2 - 1)) * Y ^ ((4 : ℝ) - 1)) * uu t1 * uu t2
  have hC : 0 ≤ C := by have := uu_pos t1; have := uu_pos t2; positivity
  have hs1 := sig1_gt
  have hs2 := sig1_le
  refine (C3P_shift (g := fun t => C * gg (t1 + t)) (by norm_num)
    (diff_Phi_z h hX hY hZ (fun z hz => mem_Om (by norm_num; linarith) (by norm_num; linarith)
      (by norm_num) (by norm_num) (by linarith [hz.1]) (by linarith [hz.2]))
      (fun z hz => by linarith [hz.1])
      (fun z hz h0 => by have := congrArg Complex.re h0; simp at this; linarith [hz.1]))
    ((integrable_gg_add t1).const_mul C) (by simpa using (tendsto_gg_add_atTop t1).const_mul C)
    (by simpa using (tendsto_gg_add_atBot t1).const_mul C) ?_).symm
  intro s hs1' hs2'
  have h6 : 1 / 25 ≤ ‖6 * s - 1‖ := by
    have := Complex.abs_re_le_norm (6 * s - 1)
    simp at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  have hk := hK X Y Z hX hY hZ ((sig1 : ℂ) + t1 * I) (((4 : ℝ) : ℂ) + t2 * I) s
    (by norm_num) (by norm_num; linarith) (by norm_num) (by norm_num) (by linarith) hs2'
    (by have := norm_line_sub_ge 4 t2 1; norm_num at this ⊢; linarith) h6
  simp only [line_re, line_im] at hk
  refine hk.trans ?_
  have hXb : X ^ (1 / 2 - s.re) ≤ X ^ (1 / 2 - (2 : ℝ)) + X ^ (1 / 2 - (1 / 5 : ℝ)) :=
    rpow_le_add hX (by linarith) (by linarith)
  have hZb : Z ^ (sig1 + s.re - 1) ≤ Z ^ (sig1 + 1 / 5 - 1) + Z ^ (sig1 + 2 - 1) :=
    rpow_le_add hZ (by linarith) (by linarith)
  have hu1 := uu_pos t1
  have hu2 := uu_pos t2
  have hg0 := gg_pos (t1 + s.im)
  calc K * (X ^ (1 / 2 - s.re) * Z ^ (sig1 + s.re - 1) * Y ^ ((4 : ℝ) - 1)) *
        (uu t1 * uu t2 * gg (t1 + s.im))
      ≤ K * ((X ^ (1 / 2 - (2 : ℝ)) + X ^ (1 / 2 - (1 / 5 : ℝ))) *
          (Z ^ (sig1 + 1 / 5 - 1) + Z ^ (sig1 + 2 - 1)) * Y ^ ((4 : ℝ) - 1)) *
          (uu t1 * uu t2 * gg (t1 + s.im)) := by gcongr
    _ = C * gg (t1 + s.im) := by simp only [C]; ring

/-- Integrability in `(t₂, t₃)` on the lines `(σ₁, b, 1/5)`. -/
lemma int2_L3 (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (t1 : ℝ) {b : ℝ}
    (hb1 : 19 / 20 ≤ b) (hb2 : b ≤ 4) (hbw : 1 / 20 ≤ |b - 1|) :
    Integrable (fun q : ℝ × ℝ => L3 X Y Z M Wh R G sig1 b (1 / 5) t1 q.1 q.2)
      (volume.prod volume) := by
  obtain ⟨K, hK0, hK⟩ := key_Phi h
  have hs1 := sig1_gt
  have hs2 := sig1_le
  have hb0 : b ≠ 1 := fun h' => by rw [h'] at hbw; norm_num at hbw
  have hP := (integrable_uu_mul_gg t1).const_mul
    (K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) * Y ^ (b - 1)) * uu t1)
  refine hP.mono' ?_ (Eventually.of_forall fun q => ?_)
  · unfold L3
    refine (cont_Phi h hX hY hZ continuous_const ((continuous_line b).comp continuous_fst)
      ((continuous_line (1 / 5)).comp continuous_snd) (fun p => by norm_num)
      (fun p h0 => ?_) (fun p h0 => ?_) (fun p => mem_Om ?_ ?_ ?_ ?_ ?_ ?_)).aestronglyMeasurable
    · have := congrArg Complex.re h0; simp at this; exact hb0 (by linarith)
    · have := congrArg Complex.re h0; norm_num at this
    all_goals norm_num
    all_goals linarith
  · have hk := hK X Y Z hX hY hZ ((sig1 : ℂ) + t1 * I) ((b : ℂ) + q.1 * I)
      (((1 / 5 : ℝ) : ℂ) + q.2 * I) (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
      (by norm_num; linarith) (by norm_num) (by norm_num)
      (by have := norm_line_sub_ge b q.1 1; push_cast at this ⊢; linarith)
      (by have := norm_six_line_sub_ge (1 / 5) q.2; norm_num at this ⊢; linarith)
    simp only [line_re, line_im] at hk
    unfold L3
    refine hk.trans (le_of_eq ?_)
    ring

/-- Continuity and the majorant of the `w = 1` residue on the lines `(σ₁, c)`. -/
lemma cont_L2 (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {c : ℝ}
    (hc1 : 4 / 25 ≤ c) (hc2 : c ≤ 2) (hc : 1 / 25 ≤ |6 * c - 1|) :
    Continuous (fun p : ℝ × ℝ => L2 X Y Z M Wh R G sig1 c p.1 p.2) := by
  have hs1 := sig1_gt
  have hs2 := sig1_le
  have hc0 : 6 * c - 1 ≠ 0 := fun h' => by rw [h'] at hc; norm_num at hc
  unfold L2
  refine cont_Aw1 h hX hY hZ ((continuous_line sig1).comp continuous_fst)
    ((continuous_line c).comp continuous_snd) (fun p => by norm_num; linarith)
    (fun p h0 => ?_) (fun p => mem_Om ?_ ?_ ?_ ?_ ?_ ?_)
  · have := congrArg Complex.re h0; simp at this; exact hc0 (by linarith)
  all_goals norm_num
  all_goals linarith

lemma bound_L2 (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z → ∀ {c : ℝ}, 4 / 25 ≤ c → c ≤ 2 →
      1 / 25 ≤ |6 * c - 1| → ∀ t1 t3 : ℝ,
      ‖L2 X Y Z M Wh R G sig1 c t1 t3‖ ≤
        K * (X ^ (1 / 2 - c) * Z ^ (sig1 + c - 1)) * (uu t1 * gg (t1 + t3)) := by
  obtain ⟨K, hK0, hK⟩ := key_Psi h
  refine ⟨K, hK0, fun X Y Z hX hY hZ c hc1 hc2 hc t1 t3 => ?_⟩
  have hs1 := sig1_gt
  have hs2 := sig1_le
  have hk := hK X Y Z hX hY hZ ((sig1 : ℂ) + t1 * I) ((c : ℂ) + t3 * I) (by norm_num)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by have := norm_six_line_sub_ge c t3; linarith)
  simp only [line_re, line_im] at hk
  exact hk

/-- Step 3, for one ξ = σ₁ + i t₁: the w-line moves from 4 to 19/20 across the pole at 1, and in
the residue the z-line moves from 1/5 to 4/25 across the pole at 1/6. -/
theorem step_w_inner (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (t1 : ℝ) :
    ∫ t2 : ℝ, ∫ t3 : ℝ, L3 X Y Z M Wh R G sig1 4 (1 / 5) t1 t2 t3 =
      (∫ t3 : ℝ, ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3) +
        2 * (Real.pi : ℂ) * ((∫ t3 : ℝ, L2 X Y Z M Wh R G sig1 (4 / 25) t1 t3) +
          2 * (Real.pi : ℂ) * L1 X Y Z M Wh R G sig1 t1) := by
  obtain ⟨K, hK0, hK⟩ := key_Phi h
  obtain ⟨K', hK'0, hK'⟩ := bound_L2 h
  obtain ⟨K'', hK''0, hK''⟩ := key_Psi h
  have hs1 := sig1_gt
  have hs2 := sig1_le
  rw [integral_integral_swap (int2_L3 h hX hY hZ t1 (by norm_num) le_rfl (by norm_num))]
  -- the w-shift, for each t3
  have hw : ∀ t3 : ℝ, ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 4 (1 / 5) t1 t2 t3 =
      (∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3) +
        2 * (Real.pi : ℂ) * L2 X Y Z M Wh R G sig1 (1 / 5) t1 t3 := by
    intro t3
    unfold L3 L2
    set C := K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) *
      (Y ^ ((19 / 20 : ℝ) - 1) + Y ^ ((4 : ℝ) - 1))) * uu t1
    have hC : 0 ≤ C := by have := uu_pos t1; positivity
    have := C3P_shift_pole (f := fun w => Phi X Y Z M Wh R G ((sig1 : ℂ) + t1 * I) w
        (((1 / 5 : ℝ) : ℂ) + t3 * I))
      (A := fun w => Aw X Y Z M Wh R G ((sig1 : ℂ) + t1 * I) w (((1 / 5 : ℝ) : ℂ) + t3 * I))
      (g := fun t => C * uu t) (a := 19 / 20) (b := 4) (p := 1) (by norm_num) (by norm_num)
      (diff_Aw_w h hX hY hZ fun w hw => mem_Om (by norm_num; linarith) (by norm_num; linarith)
        (by linarith [hw.1]) (by linarith [hw.2]) (by norm_num) (by norm_num))
      (fun s => by simp only [Phi_eq, ofReal_one])
      (integrable_uu.const_mul C) (by simpa using tendsto_uu_atTop.const_mul C)
      (by simpa using tendsto_uu_atBot.const_mul C) ?_
    · simpa only [ofReal_one] using this
    intro s hs1' hs2' hs3
    have hw1 : 1 / 20 ≤ ‖s - 1‖ := by
      rcases hs3 with h' | h' | h'
      · have := Complex.abs_re_le_norm (s - 1)
        simp [h'] at this; norm_num at this; linarith
      · have := Complex.abs_re_le_norm (s - 1)
        simp [h'] at this; norm_num at this; linarith
      · have := Complex.abs_im_le_norm (s - 1)
        simp at this; linarith
    have hk := hK X Y Z hX hY hZ ((sig1 : ℂ) + t1 * I) s (((1 / 5 : ℝ) : ℂ) + t3 * I)
      (by norm_num) (by norm_num; linarith) hs1' hs2' (by norm_num) (by norm_num) hw1
      (by have := norm_six_line_sub_ge (1 / 5) t3; norm_num at this ⊢; linarith)
    simp only [line_re, line_im] at hk
    refine hk.trans ?_
    have hYb : Y ^ (s.re - 1) ≤ Y ^ ((19 / 20 : ℝ) - 1) + Y ^ ((4 : ℝ) - 1) :=
      rpow_le_add hY (by linarith) (by linarith)
    have hu1 := uu_pos t1
    have hu2 := uu_pos s.im
    have hg1 := gg_le_one (t1 + t3)
    have hg0 := gg_pos (t1 + t3)
    calc K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) * Y ^ (s.re - 1)) *
          (uu t1 * uu s.im * gg (t1 + t3))
        ≤ K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) *
            (Y ^ ((19 / 20 : ℝ) - 1) + Y ^ ((4 : ℝ) - 1))) * (uu t1 * uu s.im * 1) := by gcongr
      _ = C * uu s.im := by simp only [C]; ring
  rw [integral_congr_ae (Eventually.of_forall hw)]
  have hi1 : Integrable fun t3 : ℝ =>
      ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3 :=
    (int2_L3 h hX hY hZ t1 (b := 19 / 20) (by norm_num) (by norm_num) (by norm_num)).swap
      |>.integral_prod_left
  have hi2 : ∀ c : ℝ, 4 / 25 ≤ c → c ≤ 2 → 1 / 25 ≤ |6 * c - 1| →
      Integrable fun t3 : ℝ => L2 X Y Z M Wh R G sig1 c t1 t3 := by
    intro c hc1 hc2 hc
    refine ((integrable_gg_add t1).const_mul
      (K' * (X ^ (1 / 2 - c) * Z ^ (sig1 + c - 1)) * uu t1)).mono' ?_
      (Eventually.of_forall fun t3 => (hK' X Y Z hX hY hZ hc1 hc2 hc t1 t3).trans_eq (by ring))
    exact ((cont_L2 h hX hY hZ hc1 hc2 hc).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [integral_add hi1 ((hi2 (1 / 5) (by norm_num) (by norm_num) (by norm_num)).const_mul _),
    integral_const_mul]
  congr 2
  -- the z-shift in the residue
  unfold L2 L1
  set C := K'' * ((X ^ (1 / 2 - (1 / 5 : ℝ)) + X ^ (1 / 2 - (4 / 25 : ℝ))) *
    (Z ^ (sig1 + 4 / 25 - 1) + Z ^ (sig1 + 1 / 5 - 1))) * uu t1
  have hC : 0 ≤ C := by have := uu_pos t1; positivity
  refine C3P_shift_pole (f := fun z => Aw X Y Z M Wh R G ((sig1 : ℂ) + t1 * I) 1 z)
    (A := fun z => Bz X Y Z M Wh R G ((sig1 : ℂ) + t1 * I) z)
    (g := fun t => C * gg (t1 + t)) (a := 4 / 25) (b := 1 / 5) (p := 1 / 6) (by norm_num)
    (by norm_num)
    (diff_Bz_z h hX hY hZ (fun z hz => mem_Om (by norm_num; linarith) (by norm_num; linarith)
      (by norm_num) (by norm_num) (by linarith [hz.1]) (by linarith [hz.2]))
      (fun z hz => by linarith [hz.1]))
    (fun s => Aw_one_eq _ _ _ _ _ _ _ _ _)
    ((integrable_gg_add t1).const_mul C) (by simpa using (tendsto_gg_add_atTop t1).const_mul C)
    (by simpa using (tendsto_gg_add_atBot t1).const_mul C) ?_
  intro s hs1' hs2' hs3
  have h6 : 1 / 25 ≤ ‖6 * s - 1‖ := by
    rcases hs3 with h' | h' | h'
    · have := Complex.abs_re_le_norm (6 * s - 1)
      simp [h'] at this; norm_num at this; linarith
    · have := Complex.abs_re_le_norm (6 * s - 1)
      simp [h'] at this; norm_num at this; linarith
    · have := Complex.abs_im_le_norm (6 * s - 1)
      simp [abs_mul] at this; linarith
  have hk := hK'' X Y Z hX hY hZ ((sig1 : ℂ) + t1 * I) s (by norm_num) (by norm_num; linarith)
    hs1' (by linarith) h6
  simp only [line_re, line_im] at hk
  refine hk.trans ?_
  have hXb : X ^ (1 / 2 - s.re) ≤ X ^ (1 / 2 - (1 / 5 : ℝ)) + X ^ (1 / 2 - (4 / 25 : ℝ)) :=
    rpow_le_add hX (by linarith) (by linarith)
  have hZb : Z ^ (sig1 + s.re - 1) ≤ Z ^ (sig1 + 4 / 25 - 1) + Z ^ (sig1 + 1 / 5 - 1) :=
    rpow_le_add hZ (by linarith) (by linarith)
  have hu1 := uu_pos t1
  have hg0 := gg_pos (t1 + s.im)
  calc K'' * (X ^ (1 / 2 - s.re) * Z ^ (sig1 + s.re - 1)) * (uu t1 * gg (t1 + s.im))
      ≤ K'' * ((X ^ (1 / 2 - (1 / 5 : ℝ)) + X ^ (1 / 2 - (4 / 25 : ℝ))) *
          (Z ^ (sig1 + 4 / 25 - 1) + Z ^ (sig1 + 1 / 5 - 1))) * (uu t1 * gg (t1 + s.im)) := by
        gcongr
    _ = C * gg (t1 + s.im) := by simp only [C]; ring

lemma bound_L3 (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z → ∀ t1 t2 t3 : ℝ,
      ‖L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3‖ ≤
        K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) * Y ^ ((19 / 20 : ℝ) - 1)) *
          (uu t1 * uu t2 * gg (t1 + t3)) := by
  obtain ⟨K, hK0, hK⟩ := key_Phi h
  refine ⟨K, hK0, fun X Y Z hX hY hZ t1 t2 t3 => ?_⟩
  have hs1 := sig1_gt
  have hs2 := sig1_le
  have hk := hK X Y Z hX hY hZ ((sig1 : ℂ) + t1 * I) (((19 / 20 : ℝ) : ℂ) + t2 * I)
    (((1 / 5 : ℝ) : ℂ) + t3 * I) (by norm_num) (by norm_num; linarith) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have := norm_line_sub_ge (19 / 20) t2 1; norm_num at this ⊢; linarith)
    (by have := norm_six_line_sub_ge (1 / 5) t3; norm_num at this ⊢; linarith)
  simp only [line_re, line_im] at hk
  exact hk

lemma bound_L1 (h : Hyp M Wh R G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z → ∀ {a : ℝ}, sig1 ≤ a → a ≤ 4 →
      ∀ t1 : ℝ, ‖L1 X Y Z M Wh R G a t1‖ ≤
        K * (X ^ (1 / 2 - (1 / 6 : ℝ)) * Z ^ (a + (1 / 6 : ℝ) - 1)) * uu t1 := by
  obtain ⟨K, hK0, hK⟩ := key_Bz h
  refine ⟨K, hK0, fun X Y Z hX hY hZ a ha1 ha2 t1 => ?_⟩
  have hk := hK X Y Z hX hY hZ ((a : ℂ) + t1 * I) (by norm_num; linarith) (by norm_num; linarith)
  simp only [line_re, line_im] at hk
  exact hk

lemma cont_L1 (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {a : ℝ}
    (ha1 : 1 < a) (ha2 : a < 5) : Continuous (fun t : ℝ => L1 X Y Z M Wh R G a t) := by
  unfold L1
  exact cont_Bz h hX hY hZ (continuous_line a) continuous_const (fun _ => by norm_num)
    (fun _ => mem_Om (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))

/-- Step 3, integrated over ξ. -/
theorem step_w (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ, L3 X Y Z M Wh R G sig1 4 (1 / 5) t1 t2 t3 =
      (∫ t1 : ℝ, ∫ t3 : ℝ, ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3) +
        2 * (Real.pi : ℂ) * ((∫ t1 : ℝ, ∫ t3 : ℝ, L2 X Y Z M Wh R G sig1 (4 / 25) t1 t3) +
          2 * (Real.pi : ℂ) * ∫ t1 : ℝ, L1 X Y Z M Wh R G sig1 t1) := by
  obtain ⟨K, hK0, hK⟩ := bound_L3 h
  obtain ⟨K', hK'0, hK'⟩ := bound_L2 h
  obtain ⟨K'', hK''0, hK''⟩ := bound_L1 h
  have hs1 := sig1_gt
  have hs2 := sig1_le
  rw [integral_congr_ae (Eventually.of_forall (step_w_inner h hX hY hZ))]
  -- integrability in t1 of the three pieces
  have hm1 : AEStronglyMeasurable (fun t1 : ℝ =>
      ∫ t3 : ℝ, ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3) volume := by
    have hc : Continuous fun p : (ℝ × ℝ) × ℝ =>
        L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) p.1.1 p.2 p.1.2 := by
      unfold L3
      refine cont_Phi h hX hY hZ ((continuous_line sig1).comp (continuous_fst.comp continuous_fst))
        ((continuous_line (19 / 20)).comp continuous_snd)
        ((continuous_line (1 / 5)).comp (continuous_snd.comp continuous_fst))
        (fun p => by norm_num) (fun p h0 => ?_) (fun p h0 => ?_)
        (fun p => mem_Om ?_ ?_ ?_ ?_ ?_ ?_)
      · have := congrArg Complex.re h0; norm_num at this
      · have := congrArg Complex.re h0; norm_num at this
      all_goals norm_num
      all_goals linarith
    have h1 := (hc.aestronglyMeasurable (μ := (volume : Measure (ℝ × ℝ)).prod volume)
      ).integral_prod_right'
    exact h1.integral_prod_right'
  have hi1 : Integrable (fun t1 : ℝ =>
      ∫ t3 : ℝ, ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3) := by
    refine (integrable_uu.const_mul (K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) *
      Y ^ ((19 / 20 : ℝ) - 1)) * ((∫ t, uu t) * ∫ t, gg t))).mono' hm1
      (Eventually.of_forall fun t1 => ?_)
    refine (norm_iter2_inner_le (fun c b => hK X Y Z hX hY hZ t1 b c)).trans_eq (by ring)
  have hm2 : AEStronglyMeasurable (fun t1 : ℝ =>
      ∫ t3 : ℝ, L2 X Y Z M Wh R G sig1 (4 / 25) t1 t3) volume :=
    ((cont_L2 h hX hY hZ (by norm_num) (by norm_num) (by norm_num)).aestronglyMeasurable
      (μ := (volume : Measure ℝ).prod volume)).integral_prod_right'
  have hi2 : Integrable (fun t1 : ℝ => ∫ t3 : ℝ, L2 X Y Z M Wh R G sig1 (4 / 25) t1 t3) := by
    refine (integrable_uu.const_mul (K' * (X ^ (1 / 2 - (4 / 25 : ℝ)) *
      Z ^ (sig1 + 4 / 25 - 1)) * ∫ t, gg t)).mono' hm2 (Eventually.of_forall fun t1 => ?_)
    refine (norm_iter1_inner_le (fun c => hK' X Y Z hX hY hZ (by norm_num) (by norm_num)
      (by norm_num) t1 c)).trans_eq (by ring)
  have hi3 : Integrable (fun t1 : ℝ => L1 X Y Z M Wh R G sig1 t1) :=
    (integrable_uu.const_mul (K'' * (X ^ (1 / 2 - (1 / 6 : ℝ)) * Z ^ (sig1 + (1 / 6 : ℝ) - 1))
      )).mono' (cont_L1 h hX hY hZ hs1 (by linarith)).aestronglyMeasurable
      (Eventually.of_forall fun t1 => hK'' X Y Z hX hY hZ le_rfl (by linarith) t1)
  have hi23 : Integrable (fun t1 : ℝ => 2 * (Real.pi : ℂ) *
      ((∫ t3 : ℝ, L2 X Y Z M Wh R G sig1 (4 / 25) t1 t3) +
        2 * (Real.pi : ℂ) * L1 X Y Z M Wh R G sig1 t1)) :=
    (hi2.add (hi3.const_mul _)).const_mul _
  have hi3' : Integrable (fun t1 : ℝ => 2 * (Real.pi : ℂ) * L1 X Y Z M Wh R G sig1 t1) :=
    hi3.const_mul _
  rw [integral_add hi1 hi23, integral_const_mul, integral_add hi2 hi3', integral_const_mul]

/-- Step 4: the double residue's ξ-line moves from σ₁ to 2. -/
theorem step_main (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∫ t1 : ℝ, L1 X Y Z M Wh R G sig1 t1 = ∫ t1 : ℝ, L1 X Y Z M Wh R G 2 t1 := by
  obtain ⟨K, hK0, hK⟩ := key_Bz h
  have hs1 := sig1_gt
  have hs2 := sig1_le
  set C := K * (X ^ (1 / 2 - (1 / 6 : ℝ)) * (Z ^ (sig1 + (1 / 6 : ℝ) - 1) +
    Z ^ ((2 : ℝ) + (1 / 6 : ℝ) - 1)))
  have hC : 0 ≤ C := by positivity
  unfold L1
  refine C3P_shift (g := fun t => C * uu t) hs2
    (diff_Bz_xi h hX hY hZ fun ξ hξ => mem_Om (by linarith [hξ.1]) (by linarith [hξ.2])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (integrable_uu.const_mul C) (by simpa using tendsto_uu_atTop.const_mul C)
    (by simpa using tendsto_uu_atBot.const_mul C) ?_
  intro s hs1' hs2'
  refine (hK X Y Z hX hY hZ s hs1' (by linarith)).trans ?_
  have hZb : Z ^ (s.re + (1 / 6 : ℝ) - 1) ≤ Z ^ (sig1 + (1 / 6 : ℝ) - 1) +
      Z ^ ((2 : ℝ) + (1 / 6 : ℝ) - 1) := rpow_le_add hZ (by linarith) (by linarith)
  have hu := uu_pos s.im
  calc K * (X ^ (1 / 2 - (1 / 6 : ℝ)) * Z ^ (s.re + (1 / 6 : ℝ) - 1)) * uu s.im
      ≤ K * (X ^ (1 / 2 - (1 / 6 : ℝ)) * (Z ^ (sig1 + (1 / 6 : ℝ) - 1) +
          Z ^ ((2 : ℝ) + (1 / 6 : ℝ) - 1))) * uu s.im := by gcongr
    _ = C * uu s.im := rfl

/-- The contour identity: the principal row on its initial lines is `R_w + 2π R_z + 4π² ∫ main`. -/
theorem core_identity (h : Hyp M Wh R G) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ, L3 X Y Z M Wh R G 4 4 2 t1 t2 t3 =
      (∫ t1 : ℝ, ∫ t3 : ℝ, ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3) +
        2 * (Real.pi : ℂ) * ((∫ t1 : ℝ, ∫ t3 : ℝ, L2 X Y Z M Wh R G sig1 (4 / 25) t1 t3) +
          2 * (Real.pi : ℂ) * ∫ t1 : ℝ, L1 X Y Z M Wh R G 2 t1) := by
  rw [step_xi h hX hY hZ, step_z h hX hY hZ, step_w h hX hY hZ, step_main h hX hY hZ]

end

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Core: the principal row equals `c₀ f + O(Z^{7/15 − 1/2000})`, abstractly

With `X = Z^{9/10}`, `Y = Z^{133/1000}`, the remainders `R_w` (lines σ₁, 19/20, 1/5) and `R_z`
(lines σ₁, 1, 4/25) have `Z`-exponents `.46345` and `.4661`, below `7/15 − 1/2000 = .46616…`. -/

open Complex MeasureTheory Filter Topology Set

set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

variable {M Wh R : ℂ → ℂ} {G : ℂ → ℂ → ℂ → ℂ}

lemma rpow_three {Z : ℝ} (hZ : 0 < Z) (a b c d e : ℝ) :
    (Z ^ a) ^ b * Z ^ c * (Z ^ d) ^ e = Z ^ (a * b + c + d * e) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ, ← Real.rpow_add hZ]

lemma rpow_two {Z : ℝ} (hZ : 0 < Z) (a b c : ℝ) :
    (Z ^ a) ^ b * Z ^ c = Z ^ (a * b + c) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]

/-- The double residue on the line 2, written as the integrand of `principalMellinOf`. -/
lemma L1_eq {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    L1 (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh R G 2 t =
      R 1 ^ 2 / 6 * M (1 / 6) * Wh 1 *
        ((Z : ℂ) ^ ((2 : ℂ) + t * I - 8 / 15) * cexp (((2 : ℂ) + t * I - 5 / 6) ^ 2) *
          G (2 + t * I) 1 (1 / 6)) := by
  unfold L1 Bz Ef
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hX : ((Z ^ (9 / 10 : ℝ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - ((1 / 6 : ℝ) : ℂ)) =
      (Z : ℂ) ^ ((3 / 10 : ℝ) : ℂ) := by
    have h1 : (1 / 2 : ℂ) - ((1 / 6 : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_cpow (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le,
      Complex.ofReal_cpow hZ.le]
    norm_num
  have hZZ : (Z : ℂ) ^ ((3 / 10 : ℝ) : ℂ) * (Z : ℂ) ^ ((2 : ℝ) + t * I + ((1 / 6 : ℝ) : ℂ) - 1) =
      (Z : ℂ) ^ ((2 : ℂ) + t * I - 8 / 15) := by
    rw [← Complex.cpow_add _ _ hZ']
    congr 1
    push_cast; ring
  rw [hX]
  simp only [sub_self, Complex.cpow_zero, mul_one]
  have h6 : (6 : ℂ) * ((1 / 6 : ℝ) : ℂ) = 1 := by push_cast; ring
  have he : ((2 : ℝ) : ℂ) + t * I + ((1 / 6 : ℝ) : ℂ) - 1 = (2 : ℂ) + t * I - 5 / 6 := by
    push_cast; ring
  rw [h6, ← hZZ, he]
  push_cast
  ring

/-- The principal row, abstractly: `(2π)^{-3} ∫∫∫ Φ` on the lines `(4, 4, 2)` is
`R(1)²/6 · M(1/6) · Ŵ(1) · (1/2π) ∫ Z^{s − 8/15} e^{(s−5/6)²} G(s, 1, 1/6) ds` up to
`O(Z^{7/15 − 1/2000})`. -/
theorem core_main (h : Hyp M Wh R G) :
    ∃ C : ℝ, ∀ Z : ℝ, 1 ≤ Z →
      ‖((2 * Real.pi) ^ 3 : ℂ)⁻¹ * (∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ,
          L3 (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh R G 4 4 2 t1 t2 t3) -
        R 1 ^ 2 / 6 * M (1 / 6) * Wh 1 * ((1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ,
          (Z : ℂ) ^ ((2 : ℂ) + τ * I - 8 / 15) * cexp (((2 : ℂ) + τ * I - 5 / 6) ^ 2) *
            G (2 + τ * I) 1 (1 / 6))‖ ≤ C * Z ^ ((7 : ℝ) / 15 - 1 / 2000) := by
  obtain ⟨K, hK0, hK⟩ := bound_L3 h
  obtain ⟨K', hK'0, hK'⟩ := bound_L2 h
  set Iu := ∫ t, uu t
  set Ig := ∫ t, gg t
  have hIu : 0 ≤ Iu := integral_nonneg fun t => (uu_pos t).le
  have hIg : 0 ≤ Ig := integral_nonneg fun t => (gg_pos t).le
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (K * (Iu * Iu * Ig)) + ((2 * Real.pi) ^ 2)⁻¹ * (K' * (Iu * Ig)),
    fun Z hZ1 => ?_⟩
  have hZ : 0 < Z := by linarith
  set X := Z ^ (9 / 10 : ℝ)
  set Y := Z ^ (133 / 1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  rw [core_identity h hX hY hZ]
  have hmain : ∫ t1 : ℝ, L1 X Y Z M Wh R G 2 t1 = R 1 ^ 2 / 6 * M (1 / 6) * Wh 1 * ∫ τ : ℝ,
      (Z : ℂ) ^ ((2 : ℂ) + τ * I - 8 / 15) * cexp (((2 : ℂ) + τ * I - 5 / 6) ^ 2) *
        G (2 + τ * I) 1 (1 / 6) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun t => L1_eq hZ t)
  rw [hmain]
  set Rw := ∫ t1 : ℝ, ∫ t3 : ℝ, ∫ t2 : ℝ, L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) t1 t2 t3
  set Rz := ∫ t1 : ℝ, ∫ t3 : ℝ, L2 X Y Z M Wh R G sig1 (4 / 25) t1 t3
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  set Im := ∫ τ : ℝ, (Z : ℂ) ^ ((2 : ℂ) + τ * I - 8 / 15) *
        cexp (((2 : ℂ) + τ * I - 5 / 6) ^ 2) * G (2 + τ * I) 1 (1 / 6)
  set c := R 1 ^ 2 / 6 * M (1 / 6) * Wh 1
  have halg : ((2 * Real.pi) ^ 3 : ℂ)⁻¹ * (Rw + 2 * (Real.pi : ℂ) * (Rz + 2 * (Real.pi : ℂ) *
      (c * Im))) - c * ((1 / (2 * Real.pi) : ℂ) * Im) =
      ((2 * Real.pi) ^ 3 : ℂ)⁻¹ * Rw + ((2 * Real.pi) ^ 2 : ℂ)⁻¹ * Rz := by
    field_simp
    ring
  rw [halg]
  -- the two remainders
  have hRw : ‖Rw‖ ≤ K * (Iu * Iu * Ig) * Z ^ ((7 : ℝ) / 15 - 1 / 2000) := by
    have h1 := norm_iter3_le (f := fun a c b => L3 X Y Z M Wh R G sig1 (19 / 20) (1 / 5) a b c)
      (K := K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) * Y ^ ((19 / 20 : ℝ) - 1)))
      (fun a c b => hK X Y Z hX hY hZ a b c)
    have hP : X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) * Y ^ ((19 / 20 : ℝ) - 1) ≤
        Z ^ ((7 : ℝ) / 15 - 1 / 2000) := by
      rw [rpow_three hZ]
      apply Real.rpow_le_rpow_of_exponent_le hZ1
      unfold sig1; norm_num
    calc ‖Rw‖ ≤ K * (X ^ (1 / 2 - (1 / 5 : ℝ)) * Z ^ (sig1 + 1 / 5 - 1) *
          Y ^ ((19 / 20 : ℝ) - 1)) * (Iu * Iu * Ig) := h1
      _ ≤ K * Z ^ ((7 : ℝ) / 15 - 1 / 2000) * (Iu * Iu * Ig) := by gcongr
      _ = _ := by ring
  have hRz : ‖Rz‖ ≤ K' * (Iu * Ig) * Z ^ ((7 : ℝ) / 15 - 1 / 2000) := by
    have h1 := norm_iter2_le (f := fun a c => L2 X Y Z M Wh R G sig1 (4 / 25) a c)
      (K := K' * (X ^ (1 / 2 - (4 / 25 : ℝ)) * Z ^ (sig1 + 4 / 25 - 1)))
      (fun a c => hK' X Y Z hX hY hZ (by norm_num) (by norm_num) (by norm_num) a c)
    have hP : X ^ (1 / 2 - (4 / 25 : ℝ)) * Z ^ (sig1 + 4 / 25 - 1) ≤
        Z ^ ((7 : ℝ) / 15 - 1 / 2000) := by
      rw [rpow_two hZ]
      apply Real.rpow_le_rpow_of_exponent_le hZ1
      unfold sig1; norm_num
    calc ‖Rz‖ ≤ K' * (X ^ (1 / 2 - (4 / 25 : ℝ)) * Z ^ (sig1 + 4 / 25 - 1)) * (Iu * Ig) := h1
      _ ≤ K' * Z ^ ((7 : ℝ) / 15 - 1 / 2000) * (Iu * Ig) := by gcongr
      _ = _ := by ring
  have hn3 : ‖((2 * Real.pi) ^ 3 : ℂ)⁻¹‖ = ((2 * Real.pi) ^ 3)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  have hn2 : ‖((2 * Real.pi) ^ 2 : ℂ)⁻¹‖ = ((2 * Real.pi) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  calc ‖((2 * Real.pi) ^ 3 : ℂ)⁻¹ * Rw + ((2 * Real.pi) ^ 2 : ℂ)⁻¹ * Rz‖
      ≤ ‖((2 * Real.pi) ^ 3 : ℂ)⁻¹‖ * ‖Rw‖ + ‖((2 * Real.pi) ^ 2 : ℂ)⁻¹‖ * ‖Rz‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (K * (Iu * Iu * Ig) * Z ^ ((7 : ℝ) / 15 - 1 / 2000)) +
        ((2 * Real.pi) ^ 2)⁻¹ * (K' * (Iu * Ig) * Z ^ ((7 : ℝ) / 15 - 1 / 2000)) := by
        rw [hn3, hn2]
        gcongr
    _ = _ := by ring

end

end C3P

end ArtinPrimitiveRoots
end

section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

theorem toFun_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊥ = 0 :=
  (χ.eq_zero_iff' ⊥).2 (Or.inl rfl)

theorem toFun_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (n : ℕ) :
    χ.toFun (I ^ n) = χ.toFun I ^ n := by
  induction n with
  | zero => simp [Ideal.one_eq_top, toFun_top]
  | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- **(a)** A Hecke character of nonzero modulus takes values of norm `≤ 1`. -/
theorem norm_le_one {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) :
    ‖χ.toFun I‖ ≤ 1 := by
  by_cases h0 : χ.toFun I = 0
  · simp [h0]
  have hI : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
    have := (χ.eq_zero_iff' I).not.1 h0
    push Not at this
    exact this
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI.1
  have hIh0 : I ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem hI0 h
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hIh0]
    have : (⟨I ^ h, hIh0⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI0⟩ ^ h := rfl
    rw [this, map_pow, hh, pow_card_eq_one]
  set β := Submodule.IsPrincipal.generator (I ^ h)
  have hβ : Ideal.span {β} = I ^ h := Ideal.span_singleton_generator (I ^ h)
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb, Ideal.span_singleton_eq_bot.2 rfl] at hβ
    exact hI.1 (pow_eq_zero_iff hpos.ne' |>.1 hβ.symm)
  have hcop : Ideal.span {β} ⊔ 𝔪 = ⊤ := by
    rw [hβ, sup_comm]
    exact Ideal.sup_pow_eq_top' (by rw [sup_comm]; exact hI.2)
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {β} ⊔ 𝔪 := by rw [hcop]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 a) ?_
    rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.2 hyz.symm, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.2 hz, sub_zero]
  have : Finite (𝓞 F ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  have : Finite (𝓞 F ⧸ 𝔪)ˣ := Finite.of_injective _ Units.val_injective
  set k := Nat.card (𝓞 F ⧸ 𝔪)ˣ
  have hk : 0 < k := Nat.card_pos
  have hβk : Ideal.Quotient.mk 𝔪 (β ^ k) = Ideal.Quotient.mk 𝔪 1 := by
    rw [map_pow, map_one, ← hunit.unit_spec, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
      Units.val_one]
  have hval := χ.map_principal' (β ^ k) (pow_ne_zero _ hβ0) (Ideal.Quotient.eq.1 hβk)
  rw [← Ideal.span_singleton_pow, hβ, ← pow_mul, toFun_pow] at hval
  exact (Complex.norm_eq_one_of_pow_eq_one hval (Nat.mul_ne_zero hpos.ne' hk.ne')).le

/-! ### The Dirichlet series as a sum over ideals -/

/-- `g_s(I) = χ(I) N(I)^{-s}`. -/
noncomputable def gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  χ.toFun I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)

theorem gs_mul {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I J : Ideal (𝓞 F)) :
    gs χ s (I * J) = gs χ s I * gs χ s J := by
  simp only [gs, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, χ.map_mul']
  ring

theorem gs_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊥ = 0 := by
  simp [gs, toFun_bot]

theorem gs_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊤ = 1 := by
  simp [gs, toFun_top]

theorem norm_gs_le {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} {σ : ℝ} (hσ : σ ≤ s.re) (I : Ideal (𝓞 F)) :
    ‖gs χ s I‖ ≤ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  by_cases hI : Ideal.absNorm I = 0
  · rw [Ideal.absNorm_eq_zero_iff.1 hI, gs_bot, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hI
  rw [gs, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hI), Complex.neg_re]
  calc ‖χ.toFun I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re)
      ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-σ) :=
        mul_le_mul (hχ I) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
          (Real.rpow_nonneg (by positivity) _) zero_le_one
    _ = _ := one_mul _

theorem summable_gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (gs χ s) :=
  Summable.of_norm_bounded (summable_absNorm_rpow hs) (norm_gs_le χ hχ le_rfl)

/-- `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` on `Re s > 1`. -/
theorem lseries_eq_tsum {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : χ.LSeries s = ∑' I, gs χ s I := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hsum := summable_gs χ hχ hs
  have hs2 : Summable (fun p => gs χ s (e p)) := (e.summable_iff).2 hsum
  rw [← e.tsum_eq, hs2.tsum_sigma, HeckeChar.LSeries, LSeries]
  congr 1
  funext n
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      gs χ s (e ⟨n, y⟩) = χ.toFun y.1 * (n : ℂ) ^ (-s) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, gs, y.2]
  simp only [hfib]
  rw [tsum_mul_right]
  have hcoeff : (∑' y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, χ.toFun y.1) = χ.coeff n := by
    rw [HeckeChar.coeff, finsum_mem_def,
      ← tsum_eq_finsum (L := SummationFilter.unconditional (Ideal (𝓞 F)))
        ((Ideal.finite_setOfPred_absNorm_eq n).subset
        Set.support_indicator_subset),
      ← tsum_subtype]
    rfl
  rw [hcoeff]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow, mul_zero]
    intro h
    have : s = 0 := neg_eq_zero.1 h
    rw [this, Complex.zero_re] at hs
    linarith
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-! ### The finite sieve -/

/-- The ideals not contained in any member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Ideal (𝓞 F)) := {I | ∀ P ∈ T, ¬ I ≤ P}

theorem sieve (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J) (hg : Summable g)
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    (∑' I, g I) * ∏ P ∈ T, (1 - g P) = ∑' I, (Cop T).indicator g I := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cop]
  | insert P T hPT ih =>
    have hP := hT P (Finset.mem_insert_self P T)
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.prod_insert hPT, mul_left_comm, mul_comm, ih']
    set h := (Cop T).indicator g with hh
    have hhs : Summable h := hg.indicator _
    have hPI : ∀ I, h (P * I) = g P * h I := by
      intro I
      by_cases hI : I ∈ Cop T
      · have hPI' : P * I ∈ Cop T := by
          intro Q hQ hle
          rcases (hT Q (Finset.mem_insert_of_mem hQ)).1.mul_le.1 hle with h1 | h1
          · have := (hP.1.isMaximal hP.2).eq_of_le (hT Q (Finset.mem_insert_of_mem hQ)).1.ne_top h1
            exact hPT (this ▸ hQ)
          · exact hI Q hQ h1
        rw [hh, Set.indicator_of_mem hPI', Set.indicator_of_mem hI, hmul]
      · have hPI' : P * I ∉ Cop T := by
          intro hc
          simp only [Cop, Set.mem_setOf_eq, not_forall, not_not] at hI
          obtain ⟨Q, hQ, hle⟩ := hI
          exact hc Q hQ (Ideal.mul_le_right.trans hle)
        rw [hh, Set.indicator_of_notMem hPI', Set.indicator_of_notMem hI, mul_zero]
    have hshift : g P * ∑' I, h I = ∑' J, {J | J ≤ P}.indicator h J := by
      rw [← hhs.tsum_mul_left]
      have hinj : Function.Injective (fun I : Ideal (𝓞 F) => P * I) := by
        intro a b hab
        have hP0 : P ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hP.2
        exact mul_left_cancel₀ hP0 hab
      rw [← hinj.tsum_eq (f := {J | J ≤ P}.indicator h)]
      · congr 1
        funext I
        rw [Set.indicator_of_mem (show P * I ∈ {J | J ≤ P} from Ideal.mul_le_left), hPI]
      · intro J hJ
        have hle : J ≤ P := by
          by_contra hc
          exact hJ (Set.indicator_of_notMem hc _)
        obtain ⟨c, rfl⟩ := Ideal.dvd_iff_le.2 hle
        exact ⟨c, rfl⟩
    rw [mul_sub, mul_one, mul_comm, hshift, ← hhs.tsum_sub (hhs.indicator _)]
    congr 1
    funext J
    simp only [hh, Set.indicator, Cop, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : J ≤ P <;> by_cases h2 : ∀ Q ∈ T, ¬J ≤ Q <;> simp [h1, h2]

/-- For each `I ∈ S` with `I ≠ ⊥, ⊤`, a chosen maximal ideal containing it. -/
noncomputable def primesOf (S : Finset (Ideal (𝓞 F))) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (S.filter (fun I => I ≠ ⊤ ∧ I ≠ ⊥)).image
    (fun I => if h : I ≠ ⊤ then (Ideal.exists_le_maximal I h).choose else ⊤)

theorem primesOf_spec (S : Finset (Ideal (𝓞 F))) :
    (∀ P ∈ primesOf S, P.IsPrime ∧ P ≠ ⊥) ∧
      ∀ I ∈ S, I ≠ ⊤ → I ≠ ⊥ → ∃ P ∈ primesOf S, I ≤ P := by
  classical
  constructor
  · intro P hP
    simp only [primesOf, Finset.mem_image, Finset.mem_filter] at hP
    obtain ⟨I, ⟨-, hI, hI0⟩, rfl⟩ := hP
    rw [dif_pos hI]
    obtain ⟨hM, hle⟩ := (Ideal.exists_le_maximal I hI).choose_spec
    refine ⟨hM.isPrime, fun hb => hI0 ?_⟩
    rw [hb] at hle
    exact le_bot_iff.1 hle
  · intro I hI hIt hIb
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hI, hIt, hIb⟩), ?_⟩
    simp only [dif_pos hIt]
    exact (Ideal.exists_le_maximal I hIt).choose_spec.2

theorem sieve_bound (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J)
    (h0 : g ⊥ = 0) (h1 : g ⊤ = 1) (f : Ideal (𝓞 F) → ℝ) (hf : Summable f)
    (hgf : ∀ I, ‖g I‖ ≤ f I) (S : Finset (Ideal (𝓞 F))) :
    ‖(∑' I, g I) * ∏ P ∈ primesOf S, (1 - g P) - 1‖ ≤ ∑' I : {I // I ∉ S}, f I := by
  classical
  have hg : Summable g := Summable.of_norm_bounded hf hgf
  obtain ⟨hT, hcov⟩ := primesOf_spec S
  rw [sieve g hmul hg _ hT]
  have hite : Summable (fun I : Ideal (𝓞 F) => if I = ⊤ then (1 : ℂ) else 0) :=
    (hasSum_ite_eq ⊤ (1 : ℂ)).summable
  have hf0 : ∀ I, 0 ≤ f I := fun I => (norm_nonneg _).trans (hgf I)
  have hpt : ∀ I, ‖(Cop (primesOf S)).indicator g I - (if I = ⊤ then (1 : ℂ) else 0)‖ ≤
      ({I | I ∉ S} : Set (Ideal (𝓞 F))).indicator f I := by
    intro I
    by_cases hIt : I = ⊤
    · subst hIt
      have : (⊤ : Ideal (𝓞 F)) ∈ Cop (primesOf S) := fun P hP hle =>
        (hT P hP).1.ne_top (top_le_iff.1 hle)
      rw [Set.indicator_of_mem this, h1, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun I _ => hf0 I) _
    rw [if_neg hIt, sub_zero]
    by_cases hS : I ∈ S
    · rw [Set.indicator_of_notMem (show I ∉ {I | I ∉ S} from fun h => h hS)]
      by_cases hIb : I = ⊥
      · subst hIb
        rw [norm_le_zero_iff]
        simp [Set.indicator, h0]
      · obtain ⟨P, hP, hle⟩ := hcov I hS hIt hIb
        have hn : I ∉ Cop (primesOf S) := by
          intro h
          simp only [Cop, Set.mem_setOf_eq] at h
          exact h P hP hle
        rw [Set.indicator_of_notMem hn, norm_zero]
    · rw [Set.indicator_of_mem (show I ∈ {I | I ∉ S} from hS)]
      exact (norm_indicator_le_norm_self _ _).trans (hgf I)
  rw [← tsum_ite_eq (⊤ : Ideal (𝓞 F)) (fun _ => (1 : ℂ)), ← (hg.indicator _).tsum_sub hite]
  have hsn : Summable (fun I => ‖(Cop (primesOf S)).indicator g I -
      (if I = ⊤ then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hf.indicator _)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine (hsn.tsum_le_tsum hpt (hf.indicator _)).trans_eq ?_
  exact (tsum_subtype {I | I ∉ S} f).symm

/-- A finite set outside of which the tail of `f` is small. -/
theorem exists_tail_lt (f : Ideal (𝓞 F) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Ideal (𝓞 F)), ∑' I : {I // I ∉ S}, f I < ε :=
  ((tendsto_tsum_compl_atTop_zero f).eventually (gt_mem_nhds hε)).exists

end T12B

end ArtinPrimitiveRoots
end

section
/-! # C3P_Zeta: the incomplete Dedekind zeta function `ζ^S`

`ζ^S(s) = ∏_{P ⊇ 𝔪}(1 − N P^{-s}) ζ_F(s) = R(s)/(s − 1)` with `R` entire, `R(1) = R_S`
(`sZetaResidue`), and `‖R(s)‖ ≤ C (2 + |Im s|)^k` on `9/10 ≤ Re s ≤ 12`. From 8087d96f
(`(s − 1) ζ_K` entire), 4f76b464 (convexity bound for `(s − 1) ζ_{K,T}`, here with `T = ∅`), the
Euler product 4d2ff9db, and Mathlib's class number formula; a field in an arbitrary universe is
replaced by a `Type` model. -/

set_option maxHeartbeats 1000000

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P


/-- `ζ^S`: the Dedekind zeta function with the Euler factors at the primes containing `𝔪`
removed. -/
noncomputable def zetaS {F : Type*} [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}, (1 - (Ideal.absNorm P : ℂ) ^ (-s))) *
    dedekindZeta F s

theorem exists_small_model (F : Type u) [Field F] [NumberField F] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀), Nonempty (F₀ ≃+* F) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  haveI : Fact (Irreducible (minpoly ℚ α)) := ⟨minpoly.irreducible hint⟩
  let e : AdjoinRoot (minpoly ℚ α) ≃ₐ[ℚ] F :=
    (IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly ℚ α)) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (AdjoinRoot (minpoly ℚ α)) := { }
  exact ⟨_, inferInstance, inferInstance, ⟨e.toRingEquiv⟩⟩

theorem card_absNorm_eq_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K₁) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 K₂) // Ideal.absNorm I = n} := by
  set f : 𝓞 K₁ ≃+* 𝓞 K₂ := RingOfIntegers.mapRingEquiv e
  have hnorm : ∀ I : Ideal (𝓞 K₁), Ideal.absNorm (I.map f) = Ideal.absNorm I := by
    intro I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm
  have h1 : ∀ I : Ideal (𝓞 K₁), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 K₂), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.map f, by rw [hnorm]; exact I.2⟩
      invFun := fun J => ⟨J.1.map f.symm, by rw [← hnorm, h2]; exact J.2⟩
      left_inv := fun I => Subtype.ext (h1 I.1)
      right_inv := fun J => Subtype.ext (h2 J.1) }

theorem dedekindZeta_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) : dedekindZeta K₁ = dedekindZeta K₂ := by
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  rw [card_absNorm_eq_congr e n]

/-- `(s − 1) ζ_F` continued: entire, with value the residue at 1 and polynomial growth on
`−1/2 ≤ Re s ≤ 5/2`. -/
theorem exists_R0 (F : Type u) [Field F] [NumberField F] :
    ∃ R0 : ℂ → ℂ, Differentiable ℂ R0 ∧ (∀ s : ℂ, 1 < s.re → R0 s = (s - 1) * dedekindZeta F s) ∧
      R0 1 = (dedekindZeta_residue F : ℂ) ∧
      ∃ C A : ℝ, 0 < A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖R0 s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨F₀, _, _, ⟨e⟩⟩ := exists_small_model F
  have hζ : dedekindZeta F₀ = dedekindZeta F := dedekindZeta_congr e
  obtain ⟨R0, hR0, -, hR0eq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
      F₀
  refine ⟨R0, hR0, fun s hs => by rw [hR0eq s hs, hζ], ?_, ?_⟩
  · -- the residue, by uniqueness of limits along real `s → 1⁺`
    have h1 : Tendsto (fun s : ℝ => R0 s) (𝓝[>] 1) (𝓝 (R0 1)) := by
      have := ((hR0 1).continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1)))
      convert this using 2
      simp
    have h2 := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hR0eq s (by simpa using hs), hζ]
  · obtain ⟨C, A, -, hA, hb⟩ :=
      NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
        F₀ ∅
    refine ⟨C, A, hA, hb R0 hR0 fun s hs => ?_⟩
    rw [hR0eq s hs]
    congr 1
    have hp := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F₀ s hs
    rw [← hp.tprod_eq]
    exact ((Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)).tprod_eq
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F₀) =>
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).symm

/-- `‖ζ_F(s)‖` is bounded on `Re s ≥ 5/2`. -/
theorem exists_dedekindZeta_bound (F : Type*) [Field F] [NumberField F] :
    ∃ B : ℝ, ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := by
  set f : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)
  have hs0 : LSeriesSummable f ((5 / 2 : ℝ) : ℂ) := T12B.lseriesSummable_card (by norm_num)
  refine ⟨∑' n, ‖LSeries.term f ((5 / 2 : ℝ) : ℂ) n‖, fun s hs => ?_⟩
  have hre : ((5 / 2 : ℝ) : ℂ).re ≤ s.re := by simpa using hs
  have hss : LSeriesSummable f s := hs0.of_re_le_re hre
  unfold dedekindZeta
  refine (norm_tsum_le_tsum_norm hss.norm).trans ?_
  exact hss.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f hre n) hs0.norm

lemma finite_primes_ge {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm 𝔪)).subset ?_
  intro P ⟨_, _, hle'⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
    (Ideal.absNorm_dvd_absNorm_of_le hle')

/-- The package for `ζ^S`. -/
theorem zetaS_package {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ (∀ s : ℂ, 1 < s.re → zetaS 𝔪 s = R s / (s - 1)) ∧
      R 1 = (sZetaResidue 𝔪 : ℂ) ∧
      ∃ C k : ℝ, 0 ≤ k ∧ ∀ s : ℂ, 9 / 10 ≤ s.re → s.re ≤ 12 → ‖R s‖ ≤ C * (2 + |s.im|) ^ k := by
  classical
  obtain ⟨R0, hR0, hR0eq, hR01, C, A, hA, hC⟩ := exists_R0 F
  obtain ⟨B₀, hB₀⟩ := exists_dedekindZeta_bound F
  set B := max B₀ 0
  have hB : ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := fun s hs =>
    (hB₀ s hs).trans (le_max_left _ _)
  have hfin := finite_primes_ge h𝔪
  set T := hfin.toFinset with hT
  have hTmem : ∀ P, P ∈ T ↔ P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P := fun P => by simp [hT]
  have hN0 : ∀ P ∈ T, (Ideal.absNorm P : ℂ) ≠ 0 := fun P hP => by
    have := ((hTmem P).1 hP).2.1
    exact_mod_cast (by rwa [Ne, Ideal.absNorm_eq_zero_iff] : Ideal.absNorm P ≠ 0)
  have hN1 : ∀ P ∈ T, (1 : ℝ) ≤ Ideal.absNorm P := fun P hP => by
    have := ((hTmem P).1 hP).2.1
    have : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  set E : ℂ → ℂ := fun s => ∏ P ∈ T, (1 - (Ideal.absNorm P : ℂ) ^ (-s))
  have hE : ∀ s, (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
      (1 - (Ideal.absNorm P : ℂ) ^ (-s))) = E s := fun s =>
    finprod_mem_eq_finite_toFinset_prod _ hfin
  have hEd : Differentiable ℂ E := by
    intro s
    refine DifferentiableAt.fun_finsetProd fun P hP => ?_
    exact (differentiableAt_const _).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl (hN0 P hP)))
  have hEb : ∀ s : ℂ, 0 ≤ s.re → ‖E s‖ ≤ 2 ^ T.card := by
    intro s hs
    refine (Finset.norm_prod_le _ _).trans ?_
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
    refine (norm_sub_le _ _).trans ?_
    have hP1 := hN1 P hP
    have : ‖(Ideal.absNorm P : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [show ((Ideal.absNorm P : ℕ) : ℂ) = ((Ideal.absNorm P : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp; linarith)
    rw [norm_one]; linarith
  refine ⟨fun s => E s * R0 s, hEd.mul hR0, ?_, ?_, ?_⟩
  · intro s hs
    have hs1 : s - 1 ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    rw [zetaS, hE]
    show E s * dedekindZeta F s = E s * R0 s / (s - 1)
    rw [hR0eq s hs]
    field_simp
  · simp only
    rw [hR01, sZetaResidue, finprod_mem_eq_finite_toFinset_prod _ hfin]
    push_cast
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [Complex.cpow_neg_one]
  · refine ⟨2 ^ T.card * max (max C 0) (11 * B), max A 1, by positivity, fun s h1 h2 => ?_⟩
    have hb1 : (1 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    rw [norm_mul]
    have hEs := hEb s (by linarith)
    have hRs : ‖R0 s‖ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 := by
      rcases le_total s.re (5 / 2) with h3 | h3
      · refine (hC s (by linarith) h3).trans ?_
        have : (2 + |s.im|) ^ A ≤ (2 + |s.im|) ^ max A 1 :=
          Real.rpow_le_rpow_of_exponent_le hb1 (le_max_left _ _)
        calc C * (2 + |s.im|) ^ A ≤ max C 0 * (2 + |s.im|) ^ A := by
              gcongr; exact le_max_left _ _
          _ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 :=
              mul_le_mul (le_max_left _ _) this (by positivity)
                (le_trans (by positivity) (le_max_left _ _))
      · have hs1 : 1 < s.re := by linarith
        rw [hR0eq s hs1, norm_mul]
        have hz := hB s h3
        have hB0 : 0 ≤ B := (norm_nonneg _).trans hz
        have hsn : ‖s - 1‖ ≤ 11 * (2 + |s.im|) := by
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          simp only [sub_re, one_re, sub_im, one_im, sub_zero]
          rw [abs_of_nonneg (by linarith)]
          linarith [abs_nonneg s.im]
        have hp : (2 + |s.im|) ≤ (2 + |s.im|) ^ max A 1 := by
          conv_lhs => rw [← Real.rpow_one (2 + |s.im|)]
          exact Real.rpow_le_rpow_of_exponent_le hb1 (le_max_right _ _)
        calc ‖s - 1‖ * ‖dedekindZeta F s‖ ≤ (11 * (2 + |s.im|)) * B := by gcongr
          _ = (11 * B) * (2 + |s.im|) := by ring
          _ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 := by
              gcongr
              · exact le_max_right _ _
    calc ‖E s‖ * ‖R0 s‖ ≤ 2 ^ T.card * (max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1) := by
          gcongr
      _ = _ := by ring

end C3P

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-- (b) and (c) for any character of nonzero modulus. -/
theorem ne_zero_and_bound {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) :
    (∀ s : ℂ, 1 < s.re → χ.LSeries s ≠ 0) ∧
    (∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(χ.LSeries s)⁻¹‖ ≤ B) := by
  have hχ := norm_le_one h𝔪 χ
  constructor
  · intro s hs
    obtain ⟨S, hS⟩ := exists_tail_lt (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s.re))
      (by norm_num : (0 : ℝ) < 1 / 2)
    have hb := sieve_bound (gs χ s) (gs_mul χ s) (gs_bot χ s) (gs_top χ s) _
      (summable_absNorm_rpow hs) (norm_gs_le χ hχ le_rfl) S
    rw [← lseries_eq_tsum χ hχ hs] at hb
    intro h0
    rw [h0, zero_mul, zero_sub, norm_neg, norm_one] at hb
    linarith
  · obtain ⟨S, hS⟩ := exists_tail_lt (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-2 : ℝ))
      (by norm_num : (0 : ℝ) < 1 / 2)
    set f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-2 : ℝ)
    have hf0 : ∀ I, 0 ≤ f I := fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
    set C := ∏ P ∈ primesOf S, (1 + f P) with hC
    have hCpos : 0 < C := Finset.prod_pos fun P _ => by linarith [hf0 P]
    refine ⟨2 * C, fun s hs => ?_⟩
    have hs1 : 1 < s.re := by linarith
    have hb := sieve_bound (gs χ s) (gs_mul χ s) (gs_bot χ s) (gs_top χ s) f
      (summable_absNorm_rpow (by norm_num : (1 : ℝ) < 2)) (norm_gs_le χ hχ hs) S
    rw [← lseries_eq_tsum χ hχ hs1] at hb
    have hprod : ‖∏ P ∈ primesOf S, (1 - gs χ s P)‖ ≤ C := by
      refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        fun P _ => ?_)
      exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_gs_le χ hχ hs P])
    have hlow : 1 / 2 ≤ ‖χ.LSeries s‖ * C := by
      have h1 : (1 : ℝ) ≤ ‖χ.LSeries s * ∏ P ∈ primesOf S, (1 - gs χ s P)‖ + 1 / 2 := by
        have := norm_sub_norm_le (1 : ℂ) (χ.LSeries s * ∏ P ∈ primesOf S, (1 - gs χ s P))
        rw [norm_one, norm_sub_rev] at this
        linarith
      rw [norm_mul] at h1
      nlinarith [norm_nonneg (χ.LSeries s)]
    have hL : 0 < ‖χ.LSeries s‖ := by
      by_contra h
      have : ‖χ.LSeries s‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
      rw [this, zero_mul] at hlow
      linarith
    rw [norm_inv, inv_le_comm₀ hL (by positivity)]
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    nlinarith

end T12B

end ArtinPrimitiveRoots
end

section
/-! # C3P_L: `L(s, χ)` on `Re s > 1`

Holomorphy (Mathlib's `LSeries_differentiableOn`, abscissa ≤ 1), non-vanishing (T12B), and
`‖L(s,χ)⁻¹‖ ≤ B` on `Re s ≥ σ₀` for any `σ₀ > 1` (T12B's finite sieve with 2 replaced by σ₀). -/

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

open T12B

variable {F : Type*} [Field F] [NumberField F]

lemma norm_coeff_le {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) (n : ℕ) :
    ‖χ.coeff n‖ ≤ ‖(Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)‖ := by
  classical
  have hχ := norm_le_one h𝔪 χ
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
  unfold HeckeChar.coeff
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.norm_natCast]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun I _ => hχ I).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have : Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} = hfin.toFinset.card := by
    exact Nat.card_eq_card_finite_toFinset hfin
  rw [this]

lemma differentiableOn_LSeries {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) :
    DifferentiableOn ℂ χ.LSeries {s | 1 < s.re} := by
  refine (LSeries_differentiableOn χ.coeff).mono fun s (hs : 1 < s.re) => ?_
  have hab : LSeries.abscissaOfAbsConv χ.coeff ≤ (1 : ℝ) := by
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
    have h := lseriesSummable_card (F := F) hy
    refine Summable.of_norm_bounded h.norm fun n => ?_
    exact LSeries.norm_term_le _ (norm_coeff_le h𝔪 χ n)
  show LSeries.abscissaOfAbsConv χ.coeff < (s.re : EReal)
  exact lt_of_le_of_lt hab (by exact_mod_cast hs)

/-- `‖L(s,χ)⁻¹‖ ≤ B` on `Re s ≥ σ₀`, for `σ₀ > 1`. -/
theorem inv_bound {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    ∃ B : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → ‖(χ.LSeries s)⁻¹‖ ≤ B := by
  have hχ := norm_le_one h𝔪 χ
  obtain ⟨S, hS⟩ := exists_tail_lt (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ₀))
    (by norm_num : (0 : ℝ) < 1 / 2)
  set f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ₀)
  have hf0 : ∀ I, 0 ≤ f I := fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set C := ∏ P ∈ primesOf S, (1 + f P) with hC
  have hCpos : 0 < C := Finset.prod_pos fun P _ => by linarith [hf0 P]
  refine ⟨2 * C, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hb := sieve_bound (gs χ s) (gs_mul χ s) (gs_bot χ s) (gs_top χ s) f
    (summable_absNorm_rpow hσ) (norm_gs_le χ hχ hs) S
  rw [← lseries_eq_tsum χ hχ hs1] at hb
  have hprod : ‖∏ P ∈ primesOf S, (1 - gs χ s P)‖ ≤ C := by
    refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      fun P _ => ?_)
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_gs_le χ hχ hs P])
  have hlow : 1 / 2 ≤ ‖χ.LSeries s‖ * C := by
    have h1 : (1 : ℝ) ≤ ‖χ.LSeries s * ∏ P ∈ primesOf S, (1 - gs χ s P)‖ + 1 / 2 := by
      have := norm_sub_norm_le (1 : ℂ) (χ.LSeries s * ∏ P ∈ primesOf S, (1 - gs χ s P))
      rw [norm_one, norm_sub_rev] at this
      linarith
    rw [norm_mul] at h1
    nlinarith [norm_nonneg (χ.LSeries s)]
  have hL : 0 < ‖χ.LSeries s‖ := by
    by_contra h
    have : ‖χ.LSeries s‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [this, zero_mul] at hlow
    linarith
  rw [norm_inv, inv_le_comm₀ hL (by positivity)]
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  nlinarith

end C3P

end ArtinPrimitiveRoots
end

section
/-! # L92M_Basic: Mellin transforms of smooth functions supported in `[a, b] ⊂ (0, ∞)`

For `g : ℝ → ℝ` continuous with `tsupport g ⊆ Icc a b`, `0 < a`, the Mellin transform of
`(g · : ℂ)` is entire and bounded on vertical strips; for smooth `g`, integration by parts
(`D g t = t g'(t)`, `mellin (D g) s = -s mellin g s`) gives decay faster than any power of `|Im s|`.
-/

namespace ArtinPrimitiveRoots.L92M

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval ContDiff

section General

variable {g : ℝ → ℝ} {a b : ℝ}

lemma vanish_of_tsupport (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (t : ℝ)
    (ht : t ∉ Ioo (a / 2) (max a b + 1)) : g t = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ht ?_
  have := hs h
  exact ⟨by linarith [this.1], by linarith [this.2, le_max_right a b]⟩

lemma lt_bounds (ha : 0 < a) : 0 < a / 2 ∧ a / 2 < max a b + 1 :=
  ⟨by linarith, by linarith [le_max_left a b]⟩

lemma cpow_continuousOn (s : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ s) (Ioi 0) :=
  fun _ ht => (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))).continuousWithinAt

lemma hasCompactSupport_of_tsupport (hs : tsupport g ⊆ Icc a b) : HasCompactSupport g :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hs

lemma mellin_eq_intervalIntegral (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (s : ℂ) :
    mellin (fun t => (g t : ℂ)) s =
      ∫ t in (a / 2)..(max a b + 1), (t : ℂ) ^ (s - 1) * (g t : ℂ) := by
  rw [mellin, intervalIntegral.integral_of_le (lt_bounds (b := b) ha).2.le]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
  · intro t ht
    exact lt_trans (lt_bounds (b := b) ha).1 ht.1
  · intro t ht
    have : t ∉ Ioo (a / 2) (max a b + 1) := fun h' => ht.2 ⟨h'.1, h'.2.le⟩
    simp [vanish_of_tsupport ha hs t this]

lemma mellin_differentiable_of_tsupport (hc : Continuous g) (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) : Differentiable ℂ (mellin (fun t => (g t : ℂ))) := by
  intro s
  have hF : LocallyIntegrableOn (fun t => (g t : ℂ)) (Ioi 0) :=
    (continuous_ofReal.comp hc).locallyIntegrable.locallyIntegrableOn _
  have htop : (fun t => (g t : ℂ)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (max a b + 1)] with t ht
    simp [vanish_of_tsupport ha hs t fun h => absurd h.2 (not_lt.mpr ht.le)]
  have hbot : (fun t => (g t : ℂ)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a / 2 by linarith)] with t ht
    simp [vanish_of_tsupport ha hs t fun h => absurd h.1 (not_lt.mpr ht.2.le)]
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hF
    ((isBigO_zero _ _).congr' htop.symm EventuallyEq.rfl) (by linarith)
    ((isBigO_zero _ _).congr' hbot.symm EventuallyEq.rfl) (by linarith)

/-- Boundedness of the Mellin transform on vertical strips. -/
lemma mellin_bounded_strip (hc : Continuous g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (σ₁ σ₂ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C := by
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support (hasCompactSupport_of_tsupport hs)
  have hcomp : IsCompact (Icc σ₁ σ₂ ×ˢ Icc α β) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ (p.1 - 1)) (Icc σ₁ σ₂ ×ˢ Icc α β) := by
    intro p hp
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.rpow continuousAt_snd (continuousAt_fst.sub continuousAt_const) ?_
    left
    have := hp.2.1
    exact ne_of_gt (lt_of_lt_of_le hαβ.1 this)
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max (B * max M 0 * (β - α)) 0, le_max_right _ _, fun s h1 h2 => ?_⟩
  rw [mellin_eq_intervalIntegral ha hs]
  refine le_trans ?_ (le_max_left _ _)
  have : ∀ t ∈ Ι α β, ‖(t : ℂ) ^ (s - 1) * (g t : ℂ)‖ ≤ B * max M 0 := by
    intro t ht
    have ht2 : t ∈ Ioc α β := by rwa [uIoc_of_le hαβ.2.le] at ht
    have ht' : t ∈ Icc α β := ⟨ht2.1.le, ht2.2⟩
    have htpos : 0 < t := lt_of_lt_of_le hαβ.1 ht'.1
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos, norm_real]
    have hb := hB (s.re, t) ⟨⟨h1, h2⟩, ht'⟩
    simp only [Real.norm_eq_abs] at hb
    rw [abs_of_nonneg (Real.rpow_nonneg htpos.le _)] at hb
    have hgt : ‖g t‖ ≤ max M 0 := le_trans (hM t) (le_max_left _ _)
    exact mul_le_mul hb hgt (norm_nonneg _) (le_trans (Real.rpow_nonneg htpos.le _) hb)
  have := intervalIntegral.norm_integral_le_of_norm_le_const this
  rwa [abs_of_pos (sub_pos.mpr hαβ.2)] at this

end General

section IBP

variable {g : ℝ → ℝ} {a b : ℝ}

/-- `D g t = t g'(t)`. -/
noncomputable def Dop (g : ℝ → ℝ) : ℝ → ℝ := fun t => t * deriv g t

lemma tsupport_Dop_subset (g : ℝ → ℝ) : tsupport (Dop g) ⊆ tsupport g :=
  (tsupport_mul_subset_right (f := fun t => t)).trans tsupport_deriv_subset

lemma contDiff_Dop (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (Dop g) :=
  contDiff_id.mul (contDiff_infty_iff_deriv.mp hg).2

lemma hasDerivAt_ofReal_cpow (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t := by
  have h1 : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  have := ((hasDerivAt_id (t : ℂ)).cpow_const (c := s) h1).comp_ofReal
  simpa using this

/-- Integration by parts: `mellin (t g'(t)) s = -s mellin g s`. -/
lemma mellin_Dop (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (s : ℂ) :
    mellin (fun t => (Dop g t : ℂ)) s = -s * mellin (fun t => (g t : ℂ)) s := by
  have hs' : tsupport (Dop g) ⊆ Icc a b := (tsupport_Dop_subset g).trans hs
  rw [mellin_eq_intervalIntegral ha hs', mellin_eq_intervalIntegral ha hs]
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcd : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hpos : ∀ t ∈ uIcc α β, 0 < t := by
    intro t ht
    rw [uIcc_of_le hαβ.2.le] at ht
    exact lt_of_lt_of_le hαβ.1 ht.1
  have h1 : ∫ t in α..β, (t : ℂ) ^ (s - 1) * ((Dop g t : ℝ) : ℂ) =
      ∫ t in α..β, (t : ℂ) ^ s * ((deriv g t : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos t ht).ne'
    simp only [Dop, ofReal_mul]
    rw [← mul_assoc]
    congr 1
    conv_rhs => rw [show s = (s - 1) + 1 by ring, cpow_add _ _ htc, cpow_one]
  rw [h1]
  have hu : ∀ t ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t :=
    fun t ht => hasDerivAt_ofReal_cpow s (hpos t ht)
  have hv : ∀ t ∈ uIcc α β, HasDerivAt (fun y : ℝ => (g y : ℂ)) ((deriv g t : ℝ) : ℂ) t :=
    fun t _ => (hdiff t).hasDerivAt.ofReal_comp
  have hu' : IntervalIntegrable (fun t : ℝ => s * (t : ℂ) ^ (s - 1)) volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul ((cpow_continuousOn (s - 1)).mono fun t ht => hpos t ht)
  have hv' : IntervalIntegrable (fun t : ℝ => ((deriv g t : ℝ) : ℂ)) volume α β :=
    (continuous_ofReal.comp hcd).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  have hgα : g α = 0 := vanish_of_tsupport ha hs α (fun h => lt_irrefl _ h.1)
  have hgβ : g β = 0 := vanish_of_tsupport ha hs β (fun h => lt_irrefl _ h.2)
  rw [hgα, hgβ]
  simp only [ofReal_zero, mul_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

lemma mellin_Dop_iterate (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (N : ℕ) : ContDiff ℝ ∞ (Dop^[N] g) ∧ tsupport (Dop^[N] g) ⊆ Icc a b ∧
      ∀ s : ℂ, mellin (fun t => (Dop^[N] g t : ℂ)) s = (-s) ^ N * mellin (fun t => (g t : ℂ)) s := by
  induction N with
  | zero => exact ⟨hg, hs, fun s => by simp⟩
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨contDiff_Dop h1, (tsupport_Dop_subset _).trans h2, fun s => ?_⟩
    rw [mellin_Dop h1 ha h2, h3, pow_succ]
    ring

lemma one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) : (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + u ^ N) := le_mul_of_one_le_right (by positivity)
          (by linarith [pow_nonneg hu N])
  · calc (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * u ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + u ^ N) := by gcongr; linarith

/-- Rapid decay on vertical strips, with a nonnegative constant. -/
lemma mellin_decay_aux (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (N : ℕ) (σ₁ σ₂ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C / (1 + |s.im|) ^ N := by
  obtain ⟨h1, h2, h3⟩ := mellin_Dop_iterate hg ha hs N
  obtain ⟨C₀, hC₀, hb₀⟩ := mellin_bounded_strip hg.continuous ha hs σ₁ σ₂
  obtain ⟨C₁, hC₁, hb₁⟩ := mellin_bounded_strip h1.continuous ha h2 σ₁ σ₂
  refine ⟨2 ^ N * (C₀ + C₁), by positivity, fun s hs1 hs2 => ?_⟩
  have hpos : 0 < (1 + |s.im|) ^ N := by positivity
  rw [le_div_iff₀ hpos]
  have e1 : ‖s‖ ^ N * ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C₁ := by
    have := hb₁ s hs1 hs2
    rw [h3 s, norm_mul, norm_pow, norm_neg] at this
    exact this
  have e0 := hb₀ s hs1 hs2
  have him : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  calc ‖mellin (fun t => (g t : ℂ)) s‖ * (1 + |s.im|) ^ N
      ≤ ‖mellin (fun t => (g t : ℂ)) s‖ * (2 ^ N * (1 + |s.im| ^ N)) := by
        gcongr; exact one_add_pow_le _ (abs_nonneg _) N
    _ ≤ ‖mellin (fun t => (g t : ℂ)) s‖ * (2 ^ N * (1 + ‖s‖ ^ N)) := by
        gcongr
    _ = 2 ^ N * (‖mellin (fun t => (g t : ℂ)) s‖ + ‖s‖ ^ N * ‖mellin (fun t => (g t : ℂ)) s‖) := by
        ring
    _ ≤ 2 ^ N * (C₀ + C₁) := by gcongr

end IBP

section Main

variable (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
  (hab : tsupport f ⊆ Set.Icc a b)

include hf ha hab

omit hf ha hab in
/-- M0 -/
theorem exists_tsupport_subset_Icc (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Set.Ioi 0) : ∃ a b : ℝ, 0 < a ∧ tsupport f ⊆ Set.Icc a b := by
  rcases (tsupport f).eq_empty_or_nonempty with he | hne
  · exact ⟨1, 1, one_pos, by simp [he]⟩
  · obtain ⟨m, hm, hmin⟩ := hfc.isCompact.exists_isMinOn hne continuousOn_id
    obtain ⟨M, hM⟩ := hfc.isCompact.bddAbove
    exact ⟨m, M, hfs hm, fun t ht => ⟨hmin ht, hM ht⟩⟩

/-- M3a -/
theorem mellin_differentiable : Differentiable ℂ (mellin (fun u : ℝ => (f u : ℂ))) :=
  mellin_differentiable_of_tsupport hf.continuous ha hab

/-- M3b' -/
theorem mellin_decay_rpow (A σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun u : ℝ => (f u : ℂ)) s‖ ≤ C * (1 + |s.im|) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := mellin_decay_aux hf ha hab ⌈A⌉₊ σ₁ σ₂
  refine ⟨C, fun s h1 h2 => le_trans (hC s h1 h2) ?_⟩
  have hb : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hb (by linarith [Nat.le_ceil A])) hC0

end Main

end ArtinPrimitiveRoots.L92M
end

section
/-! # C3P_Main: C3 from the principal-row factorization (Prop 7.3 at u = 1)

`PrincipalRowFactorization F ι` is Prop 7.3 of the paper for the frequency `u = 1`: on the
initial lines the row series `ℱ₁(ξ, w, z)` is `ζ^S(6z) ζ^S(w) ℋ(ξ, w, z) / L^S(ξ, η)`, with `ℋ`
continuous, separately holomorphic and bounded on the box `Om`
(`1 < Re ξ < 5`, `9/10 < Re w < 5`, `3/20 < Re z < 3`) and `ℋ(ξ, 1, 1/6) = H_η(ξ)`
(`principalCorrection`). From it, `C3_of_principalRowFactorization` proves the statement of C3. -/

open NumberField Complex MeasureTheory Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

/-- Proposition 7.3 at `u = 1`, (7.12)–(7.13): the Euler factorization of the principal row
`ℱ₁ = ζ^S(6z) ζ^S(w) ℋ₁ / L^S(ξ, η)` on the initial lines, with the correction `ℋ₁` continuous,
separately holomorphic and bounded on the box `Om` around the contours of §8.2, and equal to
`H_η = principalCorrection` at `(w, z) = (1, 1/6)`. -/
def PrincipalRowFactorization (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ H : ℂ → ℂ → ℂ → ℂ,
      ContinuousOn (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) Om ∧
      (∀ p ∈ Om, DifferentiableAt ℂ (fun x => H x p.2.1 p.2.2) p.1 ∧
        DifferentiableAt ℂ (fun x => H p.1 x p.2.2) p.2.1 ∧
        DifferentiableAt ℂ (fun x => H p.1 p.2.1 x) p.2.2) ∧
      (∃ B : ℝ, ∀ p ∈ Om, ‖H p.1 p.2.1 p.2.2‖ ≤ B) ∧
      (∀ ξ w z : ℂ, 3 < ξ.re → 3 < w.re → 1 < z.re →
        χ.freqSeries g (freqElt g (principalFreq 𝔪)) ξ w z =
          zetaS 𝔪 (6 * z) * zetaS 𝔪 w * H ξ w z / χ.LSeries ξ) ∧
      (∀ ξ : ℂ, 1 < ξ.re → ξ.re < 5 → H ξ 1 (1 / 6) = χ.principalCorrection ι ξ)

theorem C3_of_principalRowFactorization (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hP : PrincipalRowFactorization F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ) (M : ℂ → ℂ),
        IsProbeWeight W₁ → IsMellinWeight M →
          ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
            ‖χ.rowIntegral g W₁ M (principalFreq 𝔪) (Z ^ ((9 : ℝ) / 10))
                (Z ^ ((133 : ℝ) / 1000)) Z - principalConstant 𝔪 W₁ M * χ.principalMellin ι Z‖ ≤
              C * Z ^ ((7 : ℝ) / 15 - 1 / 2000) := by
  obtain ⟨N₀, hN₀⟩ := hP
  refine ⟨N₀, fun 𝔪 h𝔪 hsm χ g W₁ M hW hM => ?_⟩
  obtain ⟨H, hHc, hHd, ⟨BH, hBH⟩, hfac, hspec⟩ := hN₀ 𝔪 h𝔪 hsm χ g
  obtain ⟨R, hRd, hRz, hR1, hRg⟩ := zetaS_package h𝔪
  obtain ⟨a, b, ha, hab⟩ := L92M.exists_tsupport_subset_Icc W₁ hW.2.1 hW.2.2
  set Wh := mellin (fun t : ℝ => (W₁ t : ℂ))
  set L := χ.LSeries
  have hLd := differentiableOn_LSeries h𝔪 χ
  have hL0 := (T12B.ne_zero_and_bound h𝔪 χ).1
  obtain ⟨BL, hBL⟩ := inv_bound h𝔪 χ (σ₀ := sig1) sig1_gt
  set G : ℂ → ℂ → ℂ → ℂ := fun ξ w z => H ξ w z / L ξ
  have hOm1 : ∀ p ∈ Om, 1 < p.1.re := fun p hp => hp.1
  have hLat : ∀ ξ : ℂ, 1 < ξ.re → DifferentiableAt ℂ L ξ := fun ξ hξ =>
    hLd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hξ)
  have hyp : Hyp M Wh R G := by
    refine ⟨hM.1, fun A => hM.2 (4 / 25) 2 A (by norm_num), ?_, fun A => ?_, hRd, hRg, ?_,
      fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩
    · exact L92M.mellin_differentiable W₁ hW.1 a b ha hab
    · exact L92M.mellin_decay_rpow W₁ hW.1 a b ha hab A (19 / 20) 4
    · refine hHc.div ?_ fun p hp => hL0 _ (hOm1 p hp)
      refine ContinuousOn.comp (g := L) (f := fun p : ℂ × ℂ × ℂ => p.1) hLd.continuousOn
        continuous_fst.continuousOn fun p hp => hOm1 p hp
    · exact (hHd p hp).1.div (hLat _ (hOm1 p hp)) (hL0 _ (hOm1 p hp))
    · exact (hHd p hp).2.1.div_const _
    · exact (hHd p hp).2.2.div_const _
    · refine ⟨BH * BL, fun ξ w z h1 h2 h3 h4 h5 h6 => ?_⟩
      have hp : (ξ, w, z) ∈ Om := mem_Om (by linarith [sig1_gt]) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
      simp only [G, div_eq_mul_inv, norm_mul]
      exact mul_le_mul (hBH _ hp) (hBL ξ h1) (norm_nonneg _)
        ((norm_nonneg _).trans (hBH _ hp))
  obtain ⟨C, hC⟩ := core_main hyp
  refine ⟨C, 1, fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  -- the row integral is the abstract one
  have hrow : χ.rowIntegral g W₁ M (principalFreq 𝔪) (Z ^ ((9 : ℝ) / 10))
      (Z ^ ((133 : ℝ) / 1000)) Z = ((2 * Real.pi) ^ 3 : ℂ)⁻¹ * (∫ t1 : ℝ, ∫ t2 : ℝ, ∫ t3 : ℝ,
        L3 (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z M Wh R G 4 4 2 t1 t2 t3) := by
    unfold HeckeChar.rowIntegral
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t1 => ?_)
    refine integral_congr_ae (Eventually.of_forall fun t2 => ?_)
    refine integral_congr_ae (Eventually.of_forall fun t3 => ?_)
    simp only [L3, Phi, Ef]
    have hnorm : (Ideal.absNorm (principalFreq 𝔪).1.1 : ℂ) = 1 := by
      simp [principalFreq]
    rw [hnorm, Complex.one_cpow, hfac _ _ _ (by norm_num) (by norm_num) (by norm_num),
      hRz _ (by simp; norm_num), hRz _ (by norm_num)]
    simp only [G, Complex.ofReal_ofNat]
    ring
  have hmain : principalConstant 𝔪 W₁ M * χ.principalMellin ι Z =
      R 1 ^ 2 / 6 * M (1 / 6) * Wh 1 * ((1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ,
        (Z : ℂ) ^ ((2 : ℂ) + τ * I - 8 / 15) * cexp (((2 : ℂ) + τ * I - 5 / 6) ^ 2) *
          G (2 + τ * I) 1 (1 / 6)) := by
    unfold principalConstant HeckeChar.principalMellin principalMellinOf
    rw [hR1]
    have hint : ∀ τ : ℝ, (Z : ℂ) ^ ((2 : ℂ) + τ * I - 8 / 15) *
        cexp (((2 : ℂ) + τ * I - 5 / 6) ^ 2) * χ.principalCorrection ι (2 + τ * I) /
          χ.LSeries (2 + τ * I) =
        (Z : ℂ) ^ ((2 : ℂ) + τ * I - 8 / 15) * cexp (((2 : ℂ) + τ * I - 5 / 6) ^ 2) *
          G (2 + τ * I) 1 (1 / 6) := fun τ => by
      simp only [G]
      rw [hspec _ (by simp) (by simp; norm_num)]
      ring
    simp_rw [hint]
    push_cast
    ring
  rw [hrow, hmain]
  exact hC Z hZ

end C3P

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField Filter Asymptotics Finset

/-- The partial sums of the ideal-counting function are `O(n)`. -/
theorem T12C_sum_card_isBigO (F : Type*) [Field F] [NumberField F] :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  have hT := (Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop
  have h1 := hT.isBigO_one ℝ
  have h2 := h1.mul (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  simp only [one_mul] at h2
  refine (h2.congr' ?_ ?_)
  · filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Function.comp_apply]
    rw [div_mul_cancel₀ _ (by exact_mod_cast hn)]
    norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le)]
    classical
    rw [← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  · exact Eventually.of_forall fun n => by simp

/-- `∑_I N(I)^{-α}` converges for `α > 1` (all ideals; the zero ideal contributes `0`). -/
theorem T12C_summable_ideal (F : Type*) [Field F] [NumberField F] {α : ℝ} (hα : 1 < α) :
    Summable fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-α) := by
  set c : ℕ → ℝ := fun k => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ) with hc
  have hL : LSeriesSummable (fun n => (c n : ℂ)) (α : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg (T12C_sum_card_isBigO F)
      (fun n => by positivity) zero_le_one (by simpa using hα)
  have hR : Summable fun n : ℕ => c n * (n : ℝ) ^ (-α) := by
    refine (hL.norm).congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : -α ≠ 0)]
    · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        Complex.ofReal_re, Real.rpow_neg (by positivity), div_eq_mul_inv]
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr ⟨fun n => ?_, ?_⟩
  · have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    exact Summable.of_finite
  · refine hR.congr fun n => ?_
    have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    haveI := Fintype.ofFinite {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
    rw [tsum_fintype]
    simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
    rw [Finset.sum_congr rfl (fun y _ => by rw [y.2]), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    simp only [hc, Nat.card_eq_fintype_card]

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

theorem T12C_map_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (k : ℕ) :
    χ.toFun (I ^ k) = χ.toFun I ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rwa [Ideal.span_singleton_one, ← Ideal.one_eq_top] at this
  | succ k ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- A finite-order Hecke character has absolute value `1` on nonzero ideals coprime to `𝔪`. -/
theorem T12C_norm_eq_one {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) : ‖χ.toFun I‖ = 1 := by
  classical
  by_cases h𝔪 : 𝔪 = ⊥
  · subst h𝔪
    rw [sup_bot_eq] at hcop
    subst hcop
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rw [Ideal.span_singleton_one] at this
    rw [this, norm_one]
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hmk : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have hI0h : I ^ h ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hI)
  have hprin : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff hI0h).mp hmk
  obtain ⟨β, hβ⟩ := hprin.principal
  change I ^ h = Ideal.span {β} at hβ
  -- `hβ : I ^ h = span {β}`
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hβ
    exact pow_ne_zero h hI hβ
  have hcop' : Ideal.span {β} ⊔ 𝔪 = ⊤ := by rw [← hβ]; exact Ideal.pow_sup_eq_top hcop
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at hcop'
    obtain ⟨y, hy, z, hz, hyz⟩ := hcop'
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 r) ?_
    rw [← map_mul, mul_comm, ← map_one (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq]
    have : r * β - 1 = -z := by linear_combination hyz
    rw [this]
    exact 𝔪.neg_mem hz
  have hfin : Finite (𝓞 F ⧸ 𝔪) := Ring.HasFiniteQuotients.finiteQuotient h𝔪
  obtain ⟨m, hm, hum⟩ := (isOfFinOrder_of_finite hunit.unit).exists_pow_eq_one
  have hβm : Ideal.Quotient.mk 𝔪 (β ^ m) = 1 := by
    rw [map_pow]
    have := congrArg Units.val hum
    simpa using this
  have hχ : χ.toFun (Ideal.span {β ^ m}) = 1 := by
    refine χ.map_principal' _ (pow_ne_zero _ hβ0) ?_
    rw [← Ideal.Quotient.eq, map_one, hβm]
  rw [← Ideal.span_singleton_pow, ← hβ, ← pow_mul, T12C_map_pow] at hχ
  have hn := congrArg norm hχ
  rw [norm_pow, norm_one] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.mul_ne_zero hpos.ne' hm.ne')).mp hn

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

theorem T12C_pow_mod3 {M : Type*} [Monoid M] (z : M) (hz : z ^ 3 = 1) (m : ℕ) :
    z ^ m = z ^ (m % 3) := by
  conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hz, one_pow, one_mul]

/-- A prime of norm divisible by `3` has norm at most `3^[F:ℚ]`. -/
theorem T12C_absNorm_le_of_three_dvd {F : Type*} [Field F] [NumberField F] (P : Ideal (𝓞 F))
    (hP0 : P ≠ ⊥) [P.IsMaximal] (h3 : 3 ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  obtain ⟨f, hp, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at h3
  have h3p : 3 = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
  have h30 : ((3 : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [h3p]; exact ringChar.Nat.cast_ringChar
  have hmem : (3 : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using h30
  have hle : Ideal.span {(3 : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (3 : 𝓞 F) = 3 ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (3 : 𝓞 F) = algebraMap ℤ (𝓞 F) 3 by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow] at hdvd
  exact Nat.le_of_dvd (by positivity) hdvd

/-- `|J(ρ_P, ρ_P)|^6 / N P^3 = 1` for a prime `P` of norm `> 3^[F:ℚ]` of the cyclotomic field
`F = ℚ(μ_n)`, `3 ∣ n`. -/
theorem T12C_norm_jacobiPhaseSix (n : ℕ) (hn0 : 0 < n) (hn : 3 ∣ n) (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (P : Ideal (𝓞 F))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) :
    ‖jacobiPhaseSix ι P‖ = 1 := by
  classical
  haveI : P.IsMaximal := hP.isMaximal hP0
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P with hQdef
  have hcard : Fintype.card (𝓞 F ⧸ P) = Q := by
    rw [hQdef, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hQ4 : 4 ≤ Q := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      have : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h3Q : ¬ 3 ∣ Q := fun h => by
    have := T12C_absNorm_le_of_three_dvd P hP0 h
    omega
  have hcop : Q.Coprime 3 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Q))
  -- the cube root of unity
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 3)) 3 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  set ω₀ : 𝓞 F := hζ3.toInteger with hω₀
  have hω : IsPrimitiveRoot ω₀ 3 := hζ3.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P ω₀) 3 :=
    hω.idealQuotient_mk (by omega) hcop
  set ψ : ℂ := ι (ω₀ : F) with hψdef
  have hψ : IsPrimitiveRoot ψ 3 :=
    (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective
  set e := (Q - 1) / 3 with hedef
  have h3e : 3 * e = Q - 1 := by
    have h1 : Ideal.Quotient.mk P ω₀ ^ (Q - 1) = 1 := by
      rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
    have := (hωb.pow_eq_one_iff_dvd _).mp h1
    omega
  -- key lemma
  have KL : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∀ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i →
      cubicResidueChar ι P x = ψ ^ i := by
    intro x hx i hi
    have hex : ∃ ω : 𝓞 F, ω ^ 3 = 1 ∧ Ideal.Quotient.mk P ω = x ^ ((Ideal.absNorm P - 1) / 3) :=
      ⟨ω₀ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
        rw [map_pow, ← hi]⟩
    simp only [cubicResidueChar, if_neg hx, dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    obtain ⟨j, hj, hjω⟩ := hω.eq_pow_of_pow_eq_one h1
    have hmk : Ideal.Quotient.mk P ω₀ ^ j = Ideal.Quotient.mk P ω₀ ^ (i % 3) := by
      rw [← map_pow, hjω, h2, ← T12C_pow_mod3 _ hωb.pow_eq_one]
      exact hi
    have hji : j = i % 3 := hωb.pow_inj hj (Nat.mod_lt _ (by norm_num)) hmk
    rw [← hjω, show ((ω₀ ^ j : 𝓞 F) : F) = (ω₀ : F) ^ j by norm_cast, map_pow, hji, ← T12C_pow_mod3 _ hψ.pow_eq_one]
  have EX : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∃ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i := by
    intro x hx
    have : (x ^ e) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, h3e, ← hcard]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    obtain ⟨i, -, hi⟩ := hωb.eq_pow_of_pow_eq_one this
    exact ⟨i, hi.symm⟩
  have Z : cubicResidueChar ι P 0 = 0 := by simp [cubicResidueChar]
  let ρ : MulChar (𝓞 F ⧸ P) ℂ :=
    { toFun := cubicResidueChar ι P
      map_one' := by
        rw [KL 1 one_ne_zero 0 (by simp)]
        simp
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · simp [hx, Z]
        by_cases hy : y = 0
        · simp [hy, Z]
        obtain ⟨i, hi⟩ := EX x hx
        obtain ⟨j, hj⟩ := EX y hy
        rw [KL x hx i hi, KL y hy j hj, KL (x * y) (mul_ne_zero hx hy) (i + j)
          (by rw [mul_pow, hi, hj, pow_add]), pow_add]
      map_nonunit' := by
        intro a ha
        have : a = 0 := by
          by_contra h
          exact ha (Ne.isUnit h)
        simp [this, Z] }
  have hρ : ∀ x, ρ x = cubicResidueChar ι P x := fun x => rfl
  -- a non-cube
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 F ⧸ P)ˣ)
  have hog : orderOf g = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card,
      hcard]
  obtain ⟨i, hi⟩ := EX (g : 𝓞 F ⧸ P) g.ne_zero
  have hi3 : ¬ 3 ∣ i := by
    intro h
    have h1 : (g : 𝓞 F ⧸ P) ^ e = 1 := by rw [hi, hωb.pow_eq_one_iff_dvd]; exact h
    have h2 : g ^ e = 1 := Units.ext (by simpa using h1)
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hog] at this
    have hepos : 0 < e := by omega
    have := Nat.le_of_dvd hepos this
    omega
  have hρg : ρ g = ψ ^ i := KL _ g.ne_zero i hi
  have hρ1 : ρ ≠ 1 := by
    intro h
    have : ρ g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [hρg, hψ.pow_eq_one_iff_dvd] at this
    exact hi3 this
  have hρ2 : ρ * ρ ≠ 1 := by
    intro h
    have : (ρ * ρ) g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [MulChar.mul_apply, hρg, ← pow_add, hψ.pow_eq_one_iff_dvd] at this
    have : 3 ∣ 2 * i := by rwa [two_mul]
    exact hi3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this))
  have hch : ringChar ℂ ≠ ringChar (𝓞 F ⧸ P) := by
    simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite (𝓞 F ⧸ P)).symm
  have hJ := jacobiSum_mul_jacobiSum_inv hch hρ1 hρ1 hρ2
  rw [← MulChar.star_eq_inv] at hJ
  have hstar : jacobiSum (star ρ) (star ρ) = starRingEnd ℂ (jacobiSum ρ ρ) :=
    jacobiSum_ringHomComp ρ ρ (starRingEnd ℂ)
  rw [hstar, Complex.mul_conj', hcard] at hJ
  have hJn : ‖jacobiSum ρ ρ‖ ^ 2 = Q := by exact_mod_cast hJ
  have hcj : cubicJacobiSum ι P = jacobiSum ρ ρ := by
    rw [cubicJacobiSum, finsum_eq_sum_of_fintype]
    rfl
  rw [jacobiPhaseSix, hcj, norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_natCast,
    show ‖jacobiSum ρ ρ‖ ^ 6 = (‖jacobiSum ρ ρ‖ ^ 2) ^ 3 by ring, hJn]
  have : (0 : ℝ) < (Q : ℝ) ^ 3 := by have : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
                                     positivity
  rw [← hQdef]
  field_simp

end ArtinPrimitiveRoots
end

section
/-! # C3P_Row: the principal-row correction `ℋ₁(ξ, w, z)` of Proposition 7.3

`rowLocalFactor Q e θ ξ w z` is `ℋ_{1,𝔭} = (1 − V)(1 − W)(1 − D₁)⁻¹ ℱ_{1,𝔭}` with `ℱ_{1,𝔭}` the
closed form (7.19) at `u = 1`: `Q = N𝔭`, `V = Q^{-6z}`, `W = Q^{-w}`, `D = e Q^{-ξ}` (`e = η(𝔭)`),
`E = θ Q^{4−6ξ} V` (`θ` in the place of `ϑ(𝔭)⁶`), multiplied out:
`[(1 − W) + W(1 − V) + (E((1 − Q⁻¹)(1 − W) + W(1 − V)(1 − W)) − D((1 − V)(1 − W) +
(Q − 1)WV(1 − W)))/(1 − E)] / (1 − D)`.
`rowCorrection` is the product over the exterior primes; on the box `Om` it is continuous,
separately holomorphic and bounded (`‖ℋ_𝔭 − 1‖ ≤ 50 Q^{-9/5}`), and at `(w, z) = (1, 1/6)` it is
`principalCorrection`. -/

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

/-- The local factor `ℋ_{1,𝔭}(ξ, w, z)` of Proposition 7.3 at `u = 1` ((7.19), multiplied out). -/
noncomputable def rowLocalFactor (Q : ℕ) (e θ ξ w z : ℂ) : ℂ :=
  let V := (Q : ℂ) ^ (-(6 * z))
  let W := (Q : ℂ) ^ (-w)
  let D := e * (Q : ℂ) ^ (-ξ)
  let E := θ * (Q : ℂ) ^ (4 - 6 * ξ) * V
  ((1 - W) + W * (1 - V) + (E * ((1 - (Q : ℂ)⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
    D * ((1 - V) * (1 - W) + ((Q : ℂ) - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D)

/-- The principal-row correction `ℋ₁(ξ, w, z) = ∏_{𝔭 ∉ S} ℋ_{1,𝔭}`, with
`θ = conj(jacobiPhaseSix) · η⁶` in the place of `ϑ(𝔭)⁶`, as in `principalCorrection`. -/
noncomputable def rowCorrection {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
    (ι : F →+* ℂ) (χ : HeckeChar F 𝔪) (ξ w z : ℂ) : ℂ :=
  ∏' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤},
    rowLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
      (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) ξ w z

lemma rowLocal_alg (Q V W D E : ℂ) (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    ((1 - W) + W * (1 - V) + (E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
      D * ((1 - V) * (1 - W) + (Q - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D) - 1 =
    (-(W * V) + (D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E +
      E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))) / (1 - E)) / (1 - D) := by
  field_simp
  ring

lemma rowLocal_spec (Q : ℕ) (hQ : Q ≠ 0) (e θ ξ : ℂ) :
    rowLocalFactor Q e θ ξ 1 (1 / 6) = principalLocalFactor Q e θ ξ := by
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have h1 : (Q : ℂ) ^ (-(6 * (1 / 6 : ℂ))) = (Q : ℂ)⁻¹ := by
    rw [show -(6 * (1 / 6 : ℂ)) = -1 by norm_num, Complex.cpow_neg_one]
  have h2 : (Q : ℂ) ^ (-(1 : ℂ)) = (Q : ℂ)⁻¹ := Complex.cpow_neg_one _
  have h3 : (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ)⁻¹ = (Q : ℂ) ^ (3 - 6 * ξ) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hQ']
    congr 1; ring
  simp only [rowLocalFactor, principalLocalFactor, h1, h2]
  rw [mul_assoc θ, h3]
  set D := e * (Q : ℂ) ^ (-ξ)
  set E := θ * (Q : ℂ) ^ (3 - 6 * ξ)
  by_cases hD : 1 - D = 0
  · rw [hD, div_zero, div_zero]
  by_cases hE : 1 - E = 0
  · rw [hE, div_zero, div_zero]
    congr 1
    field_simp
    ring
  congr 1
  field_simp
  ring

/-- The local factor as a rational function of `Q, V, W, D, E`. -/
noncomputable def rlAlg (Q V W D E : ℂ) : ℂ :=
  ((1 - W) + W * (1 - V) + (E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
    D * ((1 - V) * (1 - W) + (Q - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D)

lemma rowLocalFactor_eq (Q : ℕ) (e θ ξ w z : ℂ) :
    rowLocalFactor Q e θ ξ w z = rlAlg (Q : ℂ) ((Q : ℂ) ^ (-(6 * z))) ((Q : ℂ) ^ (-w))
      (e * (Q : ℂ) ^ (-ξ)) (θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z))) := rfl

lemma rlAlg_bound (Q V W D E : ℂ) {q x : ℝ} (hq : 1 ≤ q) (hQn : ‖Q - 1‖ ≤ q)
    (hqi : ‖1 - Q⁻¹‖ ≤ 1) (hx0 : 0 ≤ x) (hxh : x ≤ 1 / 2) (hV : ‖V‖ ≤ x) (hW : ‖W‖ ≤ x)
    (hD : ‖D‖ ≤ q⁻¹) (hinv : q⁻¹ ≤ x) (hE : ‖E‖ ≤ x * x) :
    ‖rlAlg Q V W D E - 1‖ ≤ 50 * (x * x) ∧ 1 - D ≠ 0 ∧ 1 - E ≠ 0 := by
  have hq0 : 0 < q := by linarith
  have hDx : ‖D‖ ≤ x := hD.trans hinv
  have hx1 : x ≤ 1 := by linarith
  have hxx : x * x ≤ 1 / 2 := by nlinarith
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D; rw [norm_one] at this; linarith
  have h1E : 1 / 2 ≤ ‖1 - E‖ := by
    have := norm_sub_norm_le (1 : ℂ) E; rw [norm_one] at this; linarith
  have hD0 : 1 - D ≠ 0 := fun h => by rw [h, norm_zero] at h1D; linarith
  have hE0 : 1 - E ≠ 0 := fun h => by rw [h, norm_zero] at h1E; linarith
  refine ⟨?_, hD0, hE0⟩
  have hV1 : ‖V‖ ≤ 1 := hV.trans hx1
  have hW1 : ‖W‖ ≤ 1 := hW.trans hx1
  have h1W : ‖1 - W‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have h1V : ‖1 - V‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hQD : ‖(Q - 1) * D‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖Q - 1‖ * ‖D‖ ≤ q * q⁻¹ := mul_le_mul hQn hD (norm_nonneg _) hq0.le
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  have hA1 : ‖(1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)‖ ≤ 6 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖1 - Q⁻¹‖ * ‖1 - W‖ ≤ 1 * 2 := by gcongr
    have h2 : ‖W‖ * ‖1 - V‖ * ‖1 - W‖ ≤ 1 * 2 * 2 := by gcongr
    linarith
  have hN2 : ‖D * (V + W - V * W)‖ ≤ 3 * (x * x) := by
    rw [norm_mul]
    have h3 : ‖V + W - V * W‖ ≤ 3 * x := by
      have h4 : ‖V * W‖ ≤ x * 1 := by rw [norm_mul]; gcongr
      have := norm_sub_le (V + W) (V * W)
      have := norm_add_le V W
      linarith
    calc ‖D‖ * ‖V + W - V * W‖ ≤ x * (3 * x) := by gcongr
      _ = 3 * (x * x) := by ring
  have hN3 : ‖(Q - 1) * D * (W * V * (1 - W))‖ ≤ 2 * (x * x) := by
    rw [show ‖(Q - 1) * D * (W * V * (1 - W))‖ = ‖Q - 1‖ * ‖D‖ * (‖W‖ * ‖V‖ * ‖1 - W‖) by
      simp only [norm_mul]]
    rw [norm_mul] at hQD
    calc ‖Q - 1‖ * ‖D‖ * (‖W‖ * ‖V‖ * ‖1 - W‖) ≤ 1 * (x * x * 2) := by gcongr
      _ = 2 * (x * x) := by ring
  have hN4 : ‖D * E‖ ≤ x * x := by
    rw [norm_mul]
    calc ‖D‖ * ‖E‖ ≤ 1 * (x * x) := by gcongr; linarith
      _ = x * x := one_mul _
  have hN5 : ‖E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))‖ ≤ 6 * (x * x) := by
    rw [norm_mul]
    calc ‖E‖ * ‖(1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)‖ ≤ (x * x) * 6 := by gcongr
      _ = 6 * (x * x) := by ring
  have hnum : ‖D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E +
      E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))‖ ≤ 12 * (x * x) := by
    have a1 := norm_sub_le (D * (V + W - V * W)) ((Q - 1) * D * (W * V * (1 - W)))
    have a2 := norm_sub_le (D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W))) (D * E)
    have a3 := norm_add_le (D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E)
      (E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)))
    linarith
  have hquo : ‖(D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E +
      E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))) / (1 - E)‖ ≤ 24 * (x * x) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1E (by positivity : (0 : ℝ) ≤ 24 * (x * x))]
  have hWV : ‖-(W * V)‖ ≤ x * x := by rw [norm_neg, norm_mul]; gcongr
  have h25 := (norm_add_le _ _).trans (add_le_add hWV hquo)
  unfold rlAlg
  rw [rowLocal_alg Q V W D E hD0 hE0, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h1D (by positivity : (0 : ℝ) ≤ 50 * (x * x))]

/-- The local bound on the box. -/
theorem rowLocal_bound (Q : ℕ) (hQ : 30 ≤ Q) (e θ ξ w z : ℂ) (he : ‖e‖ ≤ 1) (hθ : ‖θ‖ ≤ 1)
    (hξ : 1 < ξ.re) (hw : 9 / 10 < w.re) (hz : 3 / 20 < z.re) :
    ‖rowLocalFactor Q e θ ξ w z - 1‖ ≤ 50 * (Q : ℝ) ^ (-(9 / 5 : ℝ)) ∧
      1 - e * (Q : ℂ) ^ (-ξ) ≠ 0 ∧ 1 - θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z)) ≠ 0 := by
  have hq30 : (30 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hq0 : 0 < (Q : ℝ) := by linarith
  have hq1 : 1 ≤ (Q : ℝ) := by linarith
  have hnc : ∀ s : ℂ, ‖(Q : ℂ) ^ s‖ = (Q : ℝ) ^ s.re := fun s => by
    rw [show ((Q : ℕ) : ℂ) = (((Q : ℝ) : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hx0 : 0 ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := Real.rpow_nonneg hq0.le _
  have hx2 : (Q : ℝ) ^ (-(9 / 10 : ℝ)) * (Q : ℝ) ^ (-(9 / 10 : ℝ)) =
      (Q : ℝ) ^ (-(9 / 5 : ℝ)) := by
    rw [← Real.rpow_add hq0]; norm_num
  have hxh : (Q : ℝ) ^ (-(9 / 10 : ℝ)) ≤ 1 / 2 := by
    have h1 : (Q : ℝ) ^ (-(9 / 10 : ℝ)) ≤ (Q : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have h2 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hq0.le, ← Real.sqrt_eq_rpow]
      have hs := Real.sq_sqrt hq0.le
      have hs0 := Real.sqrt_nonneg (Q : ℝ)
      have h2s : 2 ≤ Real.sqrt (Q : ℝ) := by nlinarith
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hinv : (Q : ℝ)⁻¹ ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hV : ‖(Q : ℂ) ^ (-(6 * z))‖ ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [hnc]; apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
  have hW : ‖(Q : ℂ) ^ (-w)‖ ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [hnc]; apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
  have hD : ‖e * (Q : ℂ) ^ (-ξ)‖ ≤ (Q : ℝ)⁻¹ := by
    rw [norm_mul, hnc]
    have : (Q : ℝ) ^ (-ξ).re ≤ (Q : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]; apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
    calc ‖e‖ * (Q : ℝ) ^ (-ξ).re ≤ 1 * (Q : ℝ)⁻¹ := mul_le_mul he this (by positivity) zero_le_one
      _ = (Q : ℝ)⁻¹ := one_mul _
  have hE : ‖θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z))‖ ≤
      (Q : ℝ) ^ (-(9 / 10 : ℝ)) * (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [norm_mul, norm_mul, hnc (4 - 6 * ξ)]
    have h1 : (Q : ℝ) ^ (4 - 6 * ξ).re ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
    calc ‖θ‖ * (Q : ℝ) ^ (4 - 6 * ξ).re * ‖(Q : ℂ) ^ (-(6 * z))‖ ≤
        1 * (Q : ℝ) ^ (-(9 / 10 : ℝ)) * (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by gcongr
      _ = _ := by ring
  have hQn : ‖(Q : ℂ) - 1‖ ≤ (Q : ℝ) := by
    have : (Q : ℂ) - 1 = (((Q : ℝ) - 1 : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have hqi : ‖(1 : ℂ) - (Q : ℂ)⁻¹‖ ≤ 1 := by
    have : (1 : ℂ) - (Q : ℂ)⁻¹ = ((1 - (Q : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : (Q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
    have : 0 ≤ (Q : ℝ)⁻¹ := by positivity
    constructor <;> linarith
  obtain ⟨h1, h2, h3⟩ := rlAlg_bound (Q : ℂ) _ _ _ _ hq1 hQn hqi hx0 hxh hV hW hD hinv hE
  refine ⟨?_, h2, h3⟩
  rw [rowLocalFactor_eq, ← hx2]
  exact h1

/-- Joint holomorphy of a local factor at points of the box. -/
theorem rowLocal_differentiableAt (Q : ℕ) (hQ : 30 ≤ Q) (e θ : ℂ) (he : ‖e‖ ≤ 1)
    (hθ : ‖θ‖ ≤ 1) (p : ℂ × ℂ × ℂ) (hp : p ∈ Om) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => rowLocalFactor Q e θ p.1 p.2.1 p.2.2) p := by
  obtain ⟨-, hD, hE⟩ := rowLocal_bound Q hQ e θ p.1 p.2.1 p.2.2 he hθ hp.1 hp.2.2.1 hp.2.2.2.2.1
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have d1 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) p := differentiableAt_fst
  have d2 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) p :=
    differentiableAt_fst.comp p differentiableAt_snd
  have d3 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) p :=
    differentiableAt_snd.comp p differentiableAt_snd
  have hV : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => (Q : ℂ) ^ (-(6 * p.2.2))) p :=
    ((d3.const_mul 6).neg).const_cpow (Or.inl hQ')
  have hW : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => (Q : ℂ) ^ (-p.2.1)) p :=
    d2.neg.const_cpow (Or.inl hQ')
  have hD' : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => e * (Q : ℂ) ^ (-p.1)) p :=
    (d1.neg.const_cpow (Or.inl hQ')).const_mul e
  have hE' : DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => θ * (Q : ℂ) ^ (4 - 6 * p.1) * (Q : ℂ) ^ (-(6 * p.2.2))) p :=
    ((((d1.const_mul 6).const_sub 4).const_cpow (Or.inl hQ')).const_mul θ).mul hV
  rw [show (fun p : ℂ × ℂ × ℂ => rowLocalFactor Q e θ p.1 p.2.1 p.2.2) =
    fun p => rlAlg (Q : ℂ) ((Q : ℂ) ^ (-(6 * p.2.2))) ((Q : ℂ) ^ (-p.2.1))
      (e * (Q : ℂ) ^ (-p.1)) (θ * (Q : ℂ) ^ (4 - 6 * p.1) * (Q : ℂ) ^ (-(6 * p.2.2))) from rfl]
  unfold rlAlg
  simp only [div_eq_mul_inv]
  have c1 : DifferentiableAt ℂ (fun _ : ℂ × ℂ × ℂ => (1 : ℂ)) p := differentiableAt_const _
  refine DifferentiableAt.fun_mul ?_ ((c1.fun_sub hD').fun_inv hD)
  refine ((c1.fun_sub hW).fun_add (hW.fun_mul (c1.fun_sub hV))).fun_add ?_
  refine DifferentiableAt.fun_mul ?_ ((c1.fun_sub hE').fun_inv hE)
  refine (hE'.fun_mul ?_).fun_sub (hD'.fun_mul ?_)
  · exact ((differentiableAt_const _).fun_mul (c1.fun_sub hW)).fun_add
      ((hW.fun_mul (c1.fun_sub hV)).fun_mul (c1.fun_sub hW))
  · exact ((c1.fun_sub hV).fun_mul (c1.fun_sub hW)).fun_add
      ((((differentiableAt_const _).fun_mul hW).fun_mul hV).fun_mul (c1.fun_sub hW))

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_RowReg: `ℋ₁` is continuous, separately holomorphic and bounded on the box -/

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

lemma isOpen_Om : IsOpen Om := by
  unfold Om
  have c1 : Continuous fun p : ℂ × ℂ × ℂ => p.1.re := Complex.continuous_re.comp continuous_fst
  have c2 : Continuous fun p : ℂ × ℂ × ℂ => p.2.1.re :=
    Complex.continuous_re.comp (continuous_fst.comp continuous_snd)
  have c3 : Continuous fun p : ℂ × ℂ × ℂ => p.2.2.re :=
    Complex.continuous_re.comp (continuous_snd.comp continuous_snd)
  exact (isOpen_lt continuous_const c1).inter ((isOpen_lt c1 continuous_const).inter
    ((isOpen_lt continuous_const c2).inter ((isOpen_lt c2 continuous_const).inter
      ((isOpen_lt continuous_const c3).inter (isOpen_lt c3 continuous_const)))))

theorem rowCorrection_regular (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), SmallPrimesDvd N₀ 𝔪 → ∀ χ : HeckeChar F 𝔪,
      ContinuousOn (fun p : ℂ × ℂ × ℂ => rowCorrection ι χ p.1 p.2.1 p.2.2) Om ∧
      (∀ p ∈ Om, DifferentiableAt ℂ (fun x => rowCorrection ι χ x p.2.1 p.2.2) p.1 ∧
        DifferentiableAt ℂ (fun x => rowCorrection ι χ p.1 x p.2.2) p.2.1 ∧
        DifferentiableAt ℂ (fun x => rowCorrection ι χ p.1 p.2.1 x) p.2.2) ∧
      (∃ B : ℝ, ∀ p ∈ Om, ‖rowCorrection ι χ p.1 p.2.1 p.2.2‖ ≤ B) ∧
      (∀ ξ : ℂ, rowCorrection ι χ ξ 1 (1 / 6) = χ.principalCorrection ι ξ) := by
  have hn3 : 3 ∣ n := (by norm_num : 3 ∣ 12).trans hn
  set d := Module.finrank ℤ (𝓞 F) with hd
  refine ⟨3 ^ (d + 4), fun 𝔪 hS χ => ?_⟩
  let J := {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤}
  have hbig : ∀ P : J, 3 ^ (d + 4) < Ideal.absNorm P.1 := by
    intro P
    by_contra h
    have hle := hS P.1 P.2.1 P.2.2.1 (not_lt.mp h)
    have h2 := P.2.2.2
    rw [sup_eq_left.mpr hle] at h2
    exact P.2.1.ne_top h2
  have h80 : ∀ P : J, 80 ≤ Ideal.absNorm P.1 := by
    intro P
    have := hbig P
    have : 81 ≤ 3 ^ (d + 4) := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ (d + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h30 : ∀ P : J, 30 ≤ Ideal.absNorm P.1 := fun P => by have := h80 P; omega
  have hd3 : ∀ P : J, 3 ^ d < Ideal.absNorm P.1 := by
    intro P
    have := hbig P
    have : 3 ^ d ≤ 3 ^ (d + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have he : ∀ P : J, ‖χ.toFun P.1‖ ≤ 1 := fun P =>
    (T12C_norm_eq_one χ P.1 P.2.2.1 P.2.2.2).le
  have hθ : ∀ P : J,
      ‖starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6‖ ≤ 1 := by
    intro P
    rw [norm_mul, Complex.norm_conj, T12C_norm_jacobiPhaseSix n hn0 hn3 F ι P.1 P.2.1 P.2.2.1
      (hd3 P), norm_pow, T12C_norm_eq_one χ P.1 P.2.2.1 P.2.2.2]
    norm_num
  -- the factors
  set f : J → ℂ × ℂ × ℂ → ℂ := fun P p => rowLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
    (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) p.1 p.2.1 p.2.2 - 1 with hf
  set u : J → ℝ := fun P => 50 * ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-(9 / 5 : ℝ)) with hu
  have hfu : ∀ P : J, ∀ p ∈ Om, ‖f P p‖ ≤ u P := fun P p hp =>
    (rowLocal_bound _ (h30 P) _ _ _ _ _ (he P) (hθ P) hp.1 hp.2.2.1 hp.2.2.2.2.1).1
  have hu1 : ∀ P : J, u P < 1 := by
    intro P
    have hQ : (80 : ℝ) ≤ ((Ideal.absNorm P.1 : ℕ) : ℝ) := by exact_mod_cast h80 P
    have hQ1 : (1 : ℝ) ≤ ((Ideal.absNorm P.1 : ℕ) : ℝ) := by linarith
    have : ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-(9 / 5 : ℝ)) ≤ ((Ideal.absNorm P.1 : ℕ) : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have h2 : ((Ideal.absNorm P.1 : ℕ) : ℝ)⁻¹ ≤ 1 / 80 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hQ
    simp only [hu]; linarith
  have hus : Summable u := by
    have h1 := T12C_summable_ideal F (α := 9 / 5) (by norm_num)
    exact (h1.comp_injective Subtype.coe_injective).mul_left 50
  have hfd : ∀ P : J, ∀ p ∈ Om, DifferentiableAt ℂ (f P) p := fun P p hp =>
    (rowLocal_differentiableAt _ (h30 P) _ _ (he P) (hθ P) p hp).sub_const 1
  have hfc : ∀ P : J, ContinuousOn (f P) Om := fun P p hp =>
    (hfd P p hp).continuousAt.continuousWithinAt
  have hprod : ∀ p : ℂ × ℂ × ℂ, rowCorrection ι χ p.1 p.2.1 p.2.2 = ∏' P : J, (1 + f P p) := by
    intro p
    simp only [rowCorrection, hf, add_sub_cancel]
    rfl
  have hne : ∀ p ∈ Om, ∀ P : J, 1 + f P p ≠ 0 := by
    intro p hp P h
    have h1 : f P p = -1 := by linear_combination h
    have := (hfu P p hp).trans_lt (hu1 P)
    rw [h1, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  have hnf : ∀ p ∈ Om, Summable fun P : J => ‖f P p‖ := fun p hp =>
    hus.of_nonneg_of_le (fun _ => norm_nonneg _) (fun P => hfu P p hp)
  -- holomorphy along an affine line through the box
  have hslice : ∀ ℓ : ℂ → ℂ × ℂ × ℂ, Differentiable ℂ ℓ → ∀ x0 : ℂ, ℓ x0 ∈ Om →
      DifferentiableAt ℂ (fun x => rowCorrection ι χ (ℓ x).1 (ℓ x).2.1 (ℓ x).2.2) x0 := by
    intro ℓ hℓ x0 hx0
    set K := ℓ ⁻¹' Om
    have hKo : IsOpen K := isOpen_Om.preimage hℓ.continuous
    have H := Summable.hasProdLocallyUniformlyOn_one_add (f := fun P x => f P (ℓ x)) hKo hus
      (Eventually.of_forall fun P x hx => hfu P (ℓ x) hx)
      (fun P => (hfc P).comp hℓ.continuous.continuousOn fun x hx => hx)
    rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at H
    have hD := H.differentiableOn (Eventually.of_forall fun t =>
      DifferentiableOn.fun_finsetProd fun P _ => (differentiableOn_const 1).add
        (fun x hx => ((hfd P (ℓ x) hx).comp x (hℓ x)).differentiableWithinAt)) hKo
    have hD' : DifferentiableOn ℂ (fun x => rowCorrection ι χ (ℓ x).1 (ℓ x).2.1 (ℓ x).2.2) K :=
      hD.congr fun x _ => hprod (ℓ x)
    exact hD'.differentiableAt (hKo.mem_nhds hx0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H := Summable.hasProdLocallyUniformlyOn_one_add isOpen_Om hus
      (Eventually.of_forall fun P p hp => hfu P p hp) hfc
    rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at H
    have hC := H.continuousOn (Filter.Frequently.of_forall fun t => by
      apply continuousOn_finset_prod
      intro P _
      exact continuousOn_const.add (hfc P))
    exact hC.congr fun p _ => hprod p
  · intro p hp
    refine ⟨?_, ?_, ?_⟩
    · exact hslice (fun x => (x, p.2.1, p.2.2)) (by fun_prop) p.1 hp
    · exact hslice (fun x => (p.1, x, p.2.2)) (by fun_prop) p.2.1 hp
    · exact hslice (fun x => (p.1, p.2.1, x)) (by fun_prop) p.2.2 hp
  · refine ⟨Real.exp (∑' P, u P), fun p hp => ?_⟩
    rw [hprod, (multipliable_one_add_of_summable (hnf p hp)).norm_tprod,
      ← Real.rexp_tsum_eq_tprod (fun P => norm_pos_iff.mpr (hne p hp P))
        (hnf p hp).summable_log_norm_one_add]
    refine Real.exp_le_exp.mpr (Summable.tsum_le_tsum (fun P => ?_)
      (hnf p hp).summable_log_norm_one_add hus)
    have hpos := norm_pos_iff.mpr (hne p hp P)
    calc Real.log ‖1 + f P p‖ ≤ ‖1 + f P p‖ - 1 := Real.log_le_sub_one_of_pos hpos
      _ ≤ ‖f P p‖ := by
        have := norm_add_le (1 : ℂ) (f P p)
        rw [norm_one] at this
        linarith
      _ ≤ u P := hfu P p hp
  · intro ξ
    unfold rowCorrection HeckeChar.principalCorrection
    refine tprod_congr fun P => ?_
    exact rowLocal_spec _ (by have := h30 P; omega) _ _ _

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Final: C3 from the Euler-product identity of the principal row

`PrincipalRowEuler F ι` is the identity (7.12) of Proposition 7.3 at `u = 1`, with the correction
written out as the explicit Euler product `rowCorrection` of the local factors (7.19):
`ℱ₁(ξ, w, z) = ζ^S(6z) ζ^S(w) ℋ₁(ξ, w, z) / L^S(ξ, η)` for `Re ξ > 3`, `Re w > 3`, `Re z > 1`.
The analytic half of Proposition 7.3 (regularity and boundedness of `ℋ₁` on the box, and
`ℋ₁(ξ, 1, 1/6) = H_η`) is proved in `C3P_RowReg`. -/

open NumberField

namespace ArtinPrimitiveRoots

namespace C3P

/-- (7.12) at `u = 1`: the Euler factorization of the principal row on the initial lines. -/
def PrincipalRowEuler (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ξ w z : ℂ), 3 < ξ.re → 3 < w.re → 1 < z.re →
      χ.freqSeries g (freqElt g (principalFreq 𝔪)) ξ w z =
        zetaS 𝔪 (6 * z) * zetaS 𝔪 w * rowCorrection ι χ ξ w z / χ.LSeries ξ

lemma smallPrimesDvd_mono {F : Type*} [Field F] [NumberField F] {N N' : ℕ} (h : N ≤ N')
    {𝔪 : Ideal (𝓞 F)} (h𝔪 : SmallPrimesDvd N' 𝔪) : SmallPrimesDvd N 𝔪 :=
  fun P hP hP0 hPN => h𝔪 P hP hP0 (hPN.trans h)

theorem principalRowFactorization_of_euler (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hE : PrincipalRowEuler F ι) : PrincipalRowFactorization F ι := by
  obtain ⟨N₁, h1⟩ := hE
  obtain ⟨N₂, h2⟩ := rowCorrection_regular n hn0 hn F ι
  refine ⟨max N₁ N₂, fun 𝔪 h𝔪 hS χ g => ?_⟩
  obtain ⟨hc, hd, hb, hs⟩ := h2 𝔪 (smallPrimesDvd_mono (le_max_right _ _) hS) χ
  exact ⟨rowCorrection ι χ, hc, hd, hb,
    fun ξ w z hξ hw hz => h1 𝔪 h𝔪 (smallPrimesDvd_mono (le_max_left _ _) hS) χ g ξ w z hξ hw hz,
    fun ξ _ _ => hs ξ⟩

/-- C3, from the Euler-product identity of the principal row. -/
theorem chk_exists_cutoff_norm_rowIntegral_principalFreq_sub_le_of_principalRowEuler
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hE : PrincipalRowEuler F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ) (M : ℂ → ℂ),
        IsProbeWeight W₁ → IsMellinWeight M →
          ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
            ‖χ.rowIntegral g W₁ M (principalFreq 𝔪) (Z ^ ((9 : ℝ) / 10))
                (Z ^ ((133 : ℝ) / 1000)) Z - principalConstant 𝔪 W₁ M * χ.principalMellin ι Z‖ ≤
              C * Z ^ ((7 : ℝ) / 15 - 1 / 2000) :=
  C3_of_principalRowFactorization n hn0 hn F ι (principalRowFactorization_of_euler n hn0 hn F ι hE)

end C3P

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ) (M : ℂ → ℂ),
        IsProbeWeight W₁ → IsMellinWeight M →
          ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
            ‖χ.rowIntegral g W₁ M (principalFreq 𝔪) (Z ^ ((9 : ℝ) / 10))
                (Z ^ ((133 : ℝ) / 1000)) Z - principalConstant 𝔪 W₁ M * χ.principalMellin ι Z‖ ≤
              C * Z ^ ((7 : ℝ) / 15 - 1 / 2000) :=
  C3P.chk_exists_cutoff_norm_rowIntegral_principalFreq_sub_le_of_principalRowEuler n hn0 hn F ι
    (exists_cutoff_freqSeries_principalFreq_eq n hn0 hn F ι)
end
