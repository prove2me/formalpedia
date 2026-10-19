-- Prove2me | solution 1 for ArtinPrimitiveRoots.tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T11:00:47.02958+00:00
-- url     : https://prove2.me/submissions/bd256226-9417-40c7-9d19-e484cf34946c

import Definitions.Def_ArtinGLWeight
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Mathlib

section
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

lemma mellinConvergent_of_tsupport (hc : Continuous g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (s : ℂ) : MellinConvergent (fun t => (g t : ℂ)) s := by
  unfold MellinConvergent
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (g t : ℂ)) (Icc (a / 2) (max a b + 1)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ((cpow_continuousOn (s - 1)).mono ?_).smul (continuous_ofReal.comp hc).continuousOn
    intro t ht
    exact lt_of_lt_of_le (lt_bounds (b := b) ha).1 ht.1
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro t ht
  have : t ∉ Ioo (a / 2) (max a b + 1) := fun h' => ht.2 (Ioo_subset_Icc_self h')
  simp [vanish_of_tsupport ha hs t this]

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
end

section
section
/-!
# L3Q_W: the weight `W` of GL Prop 5.2 and its Mellin transform

`W` is a smooth bump with `W = 1` on `[1, 2]`, `0 ≤ W ≤ 1`, support in `[1/2, 5/2]`. Its Mellin
transform `Wm` is entire, decays faster than any power on vertical strips, and inverts back to `W`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open MeasureTheory Complex
open scoped Real

theorem contDiff_W : ContDiff ℝ (⊤ : ℕ∞) W := WB.contDiff

theorem continuous_W : Continuous W := WB.continuous

theorem tsupport_W : tsupport W ⊆ Set.Icc (1 / 2) (5 / 2) := by
  have : tsupport W = Metric.closedBall (3 / 2 : ℝ) 1 := WB.tsupport_eq
  rw [this, Real.closedBall_eq_Icc]
  norm_num

theorem W_eq_zero {t : ℝ} (ht : t < 1 / 2 ∨ 5 / 2 < t) : W t = 0 := by
  by_contra h
  have := tsupport_W (subset_tsupport _ h)
  rw [Set.mem_Icc] at this
  rcases ht with ht | ht <;> linarith [this.1, this.2]

theorem differentiable_Wm : Differentiable ℂ Wm :=
  L92M.mellin_differentiable W contDiff_W (1 / 2) (5 / 2) (by norm_num) tsupport_W

theorem Wm_decay (A σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Wm s‖ ≤ C * (1 + |s.im|) ^ (-A) :=
  L92M.mellin_decay_rpow W contDiff_W (1 / 2) (5 / 2) (by norm_num) tsupport_W A σ₁ σ₂

theorem mellinConvergent_W (s : ℂ) : MellinConvergent (fun t : ℝ => (W t : ℂ)) s :=
  L92M.mellinConvergent_of_tsupport continuous_W (by norm_num) tsupport_W s

theorem integrable_Wm_line (σ : ℝ) : Integrable fun y : ℝ => Wm (σ + y * I) := by
  obtain ⟨C, hC⟩ := Wm_decay 2 σ σ
  have hcont : Continuous fun y : ℝ => Wm (σ + y * I) :=
    differentiable_Wm.continuous.comp (continuous_const.add (continuous_ofReal.mul continuous_const))
  refine Integrable.mono' ((integrable_one_add_norm (E := ℝ) (r := 2) (by norm_num)).const_mul C)
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h := hC (σ + y * I) (by simp) (by simp)
  have him : ((σ : ℂ) + y * I).im = y := by simp
  rw [him] at h
  simpa [Real.norm_eq_abs] using h

theorem verticalIntegrable_Wm (σ : ℝ) : VerticalIntegrable Wm σ := integrable_Wm_line σ

/-- Mellin inversion for `W` on every line. -/
theorem mellinInv_Wm (σ : ℝ) {x : ℝ} (hx : 0 < x) : mellinInv σ Wm x = W x :=
  mellinInv_mellin_eq σ (fun t : ℝ => (W t : ℂ)) hx (mellinConvergent_W σ)
    (verticalIntegrable_Wm σ) (continuous_ofReal.comp continuous_W).continuousAt

/-- Mellin inversion, explicitly: `W x = (2π)⁻¹ ∫ x^{-(σ+it)} Wm(σ+it) dt`. -/
theorem W_eq_integral (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    (W x : ℂ) = (1 / (2 * π) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) * Wm (σ + t * I) := by
  rw [← mellinInv_Wm σ hx, mellinInv]
  simp [smul_eq_mul]

end ArtinPrimitiveRoots.L3Q

end
end

section
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
end

section
section
/-!
# L3Q_Mel: Mellin inversion of `W` against Dirichlet series, and contour shifts

* `tsum_W_eq`: `∑ b_i W(x_i) = (2π)⁻¹ ∫ Wm(σ+it) ∑ b_i x_i^{-(σ+it)} dt` (absolute convergence).
* `shift_hol`, `shift_pole`: shifting `∫ Wm(σ+it) h(σ+it) dt` across a strip where `h` is
  holomorphic (resp. `A/(w − p)` with `A` holomorphic) and polynomially bounded.
* `norm_integral_Wm_le`: `‖∫ Wm(σ+it) Φ(t) dt‖ ≤ B · IW σ A` when `‖Φ t‖ ≤ B (1+|t|)^A`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open MeasureTheory Complex Filter Topology
open scoped Real

/-! ### The polynomial majorant -/

lemma integrable_one_add_abs_rpow_neg_two :
    Integrable fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  simpa [Real.norm_eq_abs] using this

lemma tendsto_one_add_abs_rpow_neg_two_atTop :
    Tendsto (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop)
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp h1

lemma tendsto_one_add_abs_rpow_neg_two_atBot :
    Tendsto (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) atBot (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => 1 + |t|) atBot atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_abs_atBot_atTop)
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp h1

/-- `Wm · h` is dominated by `C (1+|t|)^{-2}` on a strip where `‖h‖ ≤ C₀ (1+|t|)^A`. -/
lemma Wm_mul_maj (a b A C₀ : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ∀ z : ℂ, ‖z‖ ≤ C₀ * (1 + |w.im|) ^ A →
      ‖Wm w * z‖ ≤ C * (1 + |w.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨Cw, hCw⟩ := Wm_decay (A + 2) a b
  refine ⟨max Cw 0 * max C₀ 0, by positivity, fun w h1 h2 z hz => ?_⟩
  have h1t : 0 < 1 + |w.im| := by positivity
  rw [norm_mul]
  have hw := (hCw w h1 h2).trans (mul_le_mul_of_nonneg_right (le_max_left Cw 0) (by positivity))
  have hz' := hz.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  calc ‖Wm w‖ * ‖z‖ ≤ (max Cw 0 * (1 + |w.im|) ^ (-(A + 2))) * (max C₀ 0 * (1 + |w.im|) ^ A) :=
        mul_le_mul hw hz' (norm_nonneg _) (by positivity)
    _ = max Cw 0 * max C₀ 0 * ((1 + |w.im|) ^ (-(A + 2)) * (1 + |w.im|) ^ A) := by ring
    _ = max Cw 0 * max C₀ 0 * (1 + |w.im|) ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add h1t]; ring_nf

/-- Contour shift for `Wm · h`, `h` holomorphic and polynomially bounded on the strip. -/
theorem shift_hol {h : ℂ → ℂ} {a b C₀ A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (hh : DifferentiableOn ℂ h {s | a ≤ s.re ∧ s.re ≤ b})
    (hb : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖h w‖ ≤ C₀ * (1 + |w.im|) ^ A) :
    ∫ t : ℝ, Wm (a + t * I) * h (a + t * I) = ∫ t : ℝ, Wm (b + t * I) * h (b + t * I) := by
  obtain ⟨C, hC0, hC⟩ := Wm_mul_maj a b A C₀ hA
  refine C3P.C3P_shift (f := fun w => Wm w * h w) (g := fun t => C * (1 + |t|) ^ (-(2 : ℝ))) hab
    (differentiable_Wm.differentiableOn.mul hh)
    (integrable_one_add_abs_rpow_neg_two.const_mul C)
    (by simpa using tendsto_one_add_abs_rpow_neg_two_atTop.const_mul C)
    (by simpa using tendsto_one_add_abs_rpow_neg_two_atBot.const_mul C)
    (fun w h1 h2 => hC w h1 h2 (h w) (hb w h1 h2))

/-- Contour shift for `Wm · A / (w − p)` across the simple pole `p`. -/
theorem shift_pole {Af : ℂ → ℂ} {a b p C₀ A : ℝ} (hap : a < p) (hpb : p < b) (hA : 0 ≤ A)
    (hh : DifferentiableOn ℂ Af {s | a ≤ s.re ∧ s.re ≤ b})
    (hb : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖Af w‖ ≤ C₀ * (1 + |w.im|) ^ A) :
    ∫ t : ℝ, Wm (b + t * I) * (Af (b + t * I) / ((b + t * I) - p)) =
      (∫ t : ℝ, Wm (a + t * I) * (Af (a + t * I) / ((a + t * I) - p))) +
        2 * (π : ℂ) * (Wm p * Af p) := by
  have hab := hap.le.trans hpb.le
  set d : ℝ := min (p - a) (b - p) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  obtain ⟨C, hC0, hC⟩ := Wm_mul_maj a b A C₀ hA
  have key := C3P.C3P_shift_pole (f := fun w => Wm w * (Af w / (w - p)))
    (A := fun w => Wm w * Af w) (g := fun t => (C * max 1 d⁻¹) * (1 + |t|) ^ (-(2 : ℝ)))
    hap hpb (differentiable_Wm.differentiableOn.mul hh) (fun s => by ring)
    (integrable_one_add_abs_rpow_neg_two.const_mul _)
    (by simpa using tendsto_one_add_abs_rpow_neg_two_atTop.const_mul (C * max 1 d⁻¹))
    (by simpa using tendsto_one_add_abs_rpow_neg_two_atBot.const_mul (C * max 1 d⁻¹)) ?_
  · simpa using key
  intro w h1 h2 hcase
  have hm := hC w h1 h2 (Af w) (hb w h1 h2)
  have hden : 1 ≤ ‖w - p‖ * max 1 d⁻¹ := by
    rcases hcase with h | h | h
    · have : d ≤ ‖w - p‖ := by
        refine le_trans ?_ (Complex.abs_re_le_norm _)
        simp only [sub_re, ofReal_re, h]
        rw [abs_of_neg (by linarith)]; linarith [min_le_left (p - a) (b - p)]
      calc (1 : ℝ) = d * d⁻¹ := (mul_inv_cancel₀ hd0.ne').symm
        _ ≤ ‖w - p‖ * max 1 d⁻¹ := mul_le_mul this (le_max_right _ _) (by positivity)
            (norm_nonneg _)
    · have : d ≤ ‖w - p‖ := by
        refine le_trans ?_ (Complex.abs_re_le_norm _)
        simp only [sub_re, ofReal_re, h]
        rw [abs_of_pos (by linarith)]; linarith [min_le_right (p - a) (b - p)]
      calc (1 : ℝ) = d * d⁻¹ := (mul_inv_cancel₀ hd0.ne').symm
        _ ≤ ‖w - p‖ * max 1 d⁻¹ := mul_le_mul this (le_max_right _ _) (by positivity)
            (norm_nonneg _)
    · have : 1 ≤ ‖w - p‖ := by
        refine le_trans ?_ (Complex.abs_im_le_norm _)
        simpa using h
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ‖w - p‖ * max 1 d⁻¹ := mul_le_mul this (le_max_left _ _) zero_le_one (norm_nonneg _)
  have hwp : 0 < ‖w - p‖ := by
    rcases (norm_nonneg (w - p)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hden; linarith
  have hinv : ‖w - p‖⁻¹ ≤ max 1 d⁻¹ := by
    calc ‖w - p‖⁻¹ = ‖w - p‖⁻¹ * 1 := by ring
      _ ≤ ‖w - p‖⁻¹ * (‖w - p‖ * max 1 d⁻¹) := by gcongr
      _ = max 1 d⁻¹ := by field_simp
  rw [show Wm w * (Af w / (w - p)) = (Wm w * Af w) * (w - p)⁻¹ by ring, norm_mul, norm_inv]
  calc ‖Wm w * Af w‖ * ‖w - p‖⁻¹ ≤ C * (1 + |w.im|) ^ (-(2 : ℝ)) * max 1 d⁻¹ :=
        mul_le_mul hm hinv (by positivity) (by positivity)
    _ = _ := by ring

/-! ### Mellin inversion against a Dirichlet series -/

theorem tsum_W_eq {ι : Type*} [Countable ι] (b : ι → ℂ) (x : ι → ℝ) (hx : ∀ i, 0 < x i) (σ : ℝ)
    (hs : Summable fun i => ‖b i‖ * x i ^ (-σ)) :
    ∑' i, b i * (W (x i) : ℂ) =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (σ + t * I) * ∑' i, b i * (x i : ℂ) ^ (-((σ : ℂ) + t * I)) := by
  set G : ι → ℝ → ℂ := fun i t => Wm (σ + t * I) * (b i * (x i : ℂ) ^ (-((σ : ℂ) + t * I)))
  have hnorm : ∀ i t, ‖G i t‖ = ‖b i‖ * x i ^ (-σ) * ‖Wm (σ + t * I)‖ := by
    intro i t
    simp only [G, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hx i)]
    have : (-((σ : ℂ) + t * I)).re = -σ := by simp
    rw [this]; ring
  have hcont : ∀ i, Continuous (G i) := by
    intro i
    refine (differentiable_Wm.continuous.comp (by fun_prop)).mul (continuous_const.mul ?_)
    refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
    exact_mod_cast (hx i).ne'
  have hint : ∀ i, Integrable (G i) := by
    intro i
    refine Integrable.mono' ((integrable_Wm_line σ).norm.const_mul (‖b i‖ * x i ^ (-σ)))
      (hcont i).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [hnorm]
  have hsum : Summable fun i => ∫ t, ‖G i t‖ := by
    simp_rw [hnorm, integral_const_mul]
    exact hs.mul_right _
  have hterm : ∀ i, b i * (W (x i) : ℂ) = (1 / (2 * π) : ℂ) * ∫ t, G i t := by
    intro i
    rw [W_eq_integral σ (hx i), ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul]
    congr 1; funext t; simp only [G]; ring
  simp_rw [hterm]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  congr 1; funext t
  simp only [G]
  rw [tsum_mul_left]

/-! ### Bounding a line integral -/

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Sq: `a = s r²` with `s` squarefree, and coprimality bookkeeping

* `sqdec_exists`, `sqdec_unique`: every nonzero ideal is uniquely `s r²` with `s` squarefree.
* `tsum_sqdec`: `∑'_a f a = ∑'_{(s, r)} f (s r²)` when `f ⊥ = 0`.
* `sfree_gt_iff`: `(∀ 𝔟, 𝔟² ∣ s r² → L N𝔟² < N(s r²)) ↔ L < N s` (GL's `s(a) > L`).
* `cop`: coprimality to a finite set of primes; `sup_eq_top_iff_cop`; transfer to `s r²`.
-/

open NumberField UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L3Q

open GLW

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma bot_ne_of_mul {s r : Ideal (𝓞 F)} (hs : s ≠ ⊥) (hr : r ≠ ⊥) : s * r ^ 2 ≠ ⊥ := by
  rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  exact ⟨by rwa [Ideal.zero_eq_bot], pow_ne_zero 2 (by rwa [Ideal.zero_eq_bot])⟩

lemma count_le_one_of_sq {s : Ideal (𝓞 F)} (hs0 : s ≠ ⊥) (hs : Squarefree s) (P : Ideal (𝓞 F)) :
    (normalizedFactors s).count P ≤ 1 :=
  Multiset.nodup_iff_count_le_one.1 ((squarefree_iff_nodup_normalizedFactors hs0).1 hs) P

lemma count_mul_sq {s r : Ideal (𝓞 F)} (hs : s ≠ ⊥) (hr : r ≠ ⊥) (P : Ideal (𝓞 F)) :
    (normalizedFactors (s * r ^ 2)).count P =
      (normalizedFactors s).count P + 2 * (normalizedFactors r).count P := by
  rw [normalizedFactors_mul (by rwa [← Ideal.zero_eq_bot] at hs)
    (pow_ne_zero 2 (by rwa [← Ideal.zero_eq_bot] at hr)), normalizedFactors_pow,
    Multiset.count_add, Multiset.count_nsmul]

lemma eq_of_nf_eq {a b : Ideal (𝓞 F)} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (h : normalizedFactors a = normalizedFactors b) : a = b := by
  rw [← Ideal.prod_normalizedFactors_eq_self ha, ← Ideal.prod_normalizedFactors_eq_self hb, h]

theorem sqdec_unique {s r s' r' : Ideal (𝓞 F)} (hs : s ≠ ⊥) (hr : r ≠ ⊥) (hs' : s' ≠ ⊥)
    (hr' : r' ≠ ⊥) (hsq : Squarefree s) (hsq' : Squarefree s') (h : s * r ^ 2 = s' * r' ^ 2) :
    s = s' ∧ r = r' := by
  have hc : ∀ P, (normalizedFactors s).count P = (normalizedFactors s').count P ∧
      (normalizedFactors r).count P = (normalizedFactors r').count P := by
    intro P
    have h1 := count_mul_sq hs hr P
    have h2 := count_mul_sq hs' hr' P
    rw [h] at h1
    have h3 := count_le_one_of_sq hs hsq P
    have h4 := count_le_one_of_sq hs' hsq' P
    omega
  exact ⟨eq_of_nf_eq hs hs' (Multiset.ext.2 fun P => (hc P).1),
    eq_of_nf_eq hr hr' (Multiset.ext.2 fun P => (hc P).2)⟩

theorem sqdec_exists (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :
    ∃ s r : Ideal (𝓞 F), s ≠ ⊥ ∧ r ≠ ⊥ ∧ Squarefree s ∧ a = s * r ^ 2 := by
  rw [← Ideal.zero_eq_bot] at ha
  revert ha
  refine UniqueFactorizationMonoid.induction_on_prime a (fun h => absurd rfl h) ?_ ?_
  · intro u hu _
    refine ⟨⊤, ⊤, by simp, by simp, by rw [← Ideal.one_eq_top]; exact squarefree_one, ?_⟩
    rw [Ideal.isUnit_iff.1 hu, pow_two, Ideal.top_mul, Ideal.top_mul]
  · intro x p hx hp ih _
    obtain ⟨s, r, hs, hr, hsq, rfl⟩ := ih hx
    by_cases hps : p ∣ s
    · obtain ⟨s', rfl⟩ := hps
      have hs' : s' ≠ ⊥ := by rintro rfl; simp at hs
      refine ⟨s', p * r, hs', ?_, hsq.of_mul_right, by ring⟩
      rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
      exact ⟨hp.ne_zero, by rwa [Ideal.zero_eq_bot]⟩
    · refine ⟨p * s, r, ?_, hr, ?_, by ring⟩
      · rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
        exact ⟨hp.ne_zero, by rwa [Ideal.zero_eq_bot]⟩
      · refine squarefree_mul_iff.2 ⟨?_, hp.irreducible.squarefree, hsq⟩
        exact (hp.irreducible.isRelPrime_iff_not_dvd).2 hps

/-- The reindexing `(s, r) ↦ s r²`. -/
def sqMap (p : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} × {r : Ideal (𝓞 F) // r ≠ ⊥}) :
    Ideal (𝓞 F) := p.1.1 * p.2.1 ^ 2

theorem sqMap_injective : Function.Injective (sqMap (F := F)) := by
  rintro ⟨⟨s, hs, hsq⟩, ⟨r, hr⟩⟩ ⟨⟨s', hs', hsq'⟩, ⟨r', hr'⟩⟩ h
  obtain ⟨h1, h2⟩ := sqdec_unique hs hr hs' hr' hsq hsq' h
  subst h1; subst h2; rfl

theorem tsum_sqdec {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : Ideal (𝓞 F) → E)
    (hf : f ⊥ = 0) :
    ∑' p : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} × {r : Ideal (𝓞 F) // r ≠ ⊥},
      f (p.1.1 * p.2.1 ^ 2) = ∑' a, f a := by
  refine sqMap_injective.tsum_eq (f := f) ?_
  intro a ha
  have ha0 : a ≠ ⊥ := fun h => ha (by rw [h, hf])
  obtain ⟨s, r, hs, hr, hsq, rfl⟩ := sqdec_exists a ha0
  exact ⟨⟨⟨s, hs, hsq⟩, ⟨r, hr⟩⟩, rfl⟩

lemma absNorm_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (0 : ℝ) < Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  exact_mod_cast Nat.pos_of_ne_zero this

lemma dvd_of_sq_dvd {s r b : Ideal (𝓞 F)} (hs : s ≠ ⊥) (hr : r ≠ ⊥) (hsq : Squarefree s)
    (hb : b ^ 2 ∣ s * r ^ 2) : b ∣ r := by
  have hb0' : b ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_dvd_iff] at hb
    exact bot_ne_of_mul hs hr (by rwa [← Ideal.zero_eq_bot])
  have hr0' : r ≠ 0 := by rwa [Ideal.zero_eq_bot]
  rw [dvd_iff_normalizedFactors_le_normalizedFactors hb0' hr0']
  have hsr : s * r ^ 2 ≠ 0 := by rw [Ideal.zero_eq_bot]; exact bot_ne_of_mul hs hr
  have h := (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hb0') hsr).1 hb
  rw [Multiset.le_iff_count] at h ⊢
  intro P
  have h1 := h P
  rw [normalizedFactors_pow, Multiset.count_nsmul, count_mul_sq hs hr] at h1
  have h2 := count_le_one_of_sq hs hsq P
  omega

/-- GL's `s(a) > L`, for `a = s r²`. -/
theorem sfree_gt_iff {s r : Ideal (𝓞 F)} (hs : s ≠ ⊥) (hr : r ≠ ⊥) (hsq : Squarefree s) (L : ℝ) :
    (∀ b : Ideal (𝓞 F), b ^ 2 ∣ s * r ^ 2 →
        L * (Ideal.absNorm b : ℝ) ^ 2 < Ideal.absNorm (s * r ^ 2)) ↔
      L < Ideal.absNorm s := by
  have hN : (Ideal.absNorm (s * r ^ 2) : ℝ) = Ideal.absNorm s * (Ideal.absNorm r : ℝ) ^ 2 := by
    simp [map_mul, map_pow]
  have hr0 := absNorm_pos hr
  have hs0 := absNorm_pos hs
  rw [hN]
  constructor
  · intro h
    have := h r (dvd_mul_left _ _)
    by_contra hc; push Not at hc
    have : Ideal.absNorm s * (Ideal.absNorm r : ℝ) ^ 2 ≤ L * (Ideal.absNorm r : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  · intro hL b hb
    have hbr := dvd_of_sq_dvd hs hr hsq hb
    have hbn : (Ideal.absNorm b : ℝ) ≤ Ideal.absNorm r := by
      have : Ideal.absNorm b ∣ Ideal.absNorm r := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hbr)
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hr)) this
    rcases le_or_gt L 0 with h0 | h0
    · have : L * (Ideal.absNorm b : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)
      have : 0 < Ideal.absNorm s * (Ideal.absNorm r : ℝ) ^ 2 := by positivity
      linarith
    · calc L * (Ideal.absNorm b : ℝ) ^ 2 ≤ L * (Ideal.absNorm r : ℝ) ^ 2 := by
            gcongr
        _ < Ideal.absNorm s * (Ideal.absNorm r : ℝ) ^ 2 := by gcongr

/-! ### Coprimality -/

lemma sup_mul_eq_top_iff {I J K : Ideal (𝓞 F)} : I * J ⊔ K = ⊤ ↔ I ⊔ K = ⊤ ∧ J ⊔ K = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq]
  exact IsCoprime.mul_left_iff

lemma sup_sq_eq_top_iff {I K : Ideal (𝓞 F)} : I ^ 2 ⊔ K = ⊤ ↔ I ⊔ K = ⊤ := by
  rw [pow_two, sup_mul_eq_top_iff, and_self]

lemma sup_mul_sq_eq_top_iff {s r K : Ideal (𝓞 F)} :
    s * r ^ 2 ⊔ K = ⊤ ↔ s ⊔ K = ⊤ ∧ r ⊔ K = ⊤ := by
  rw [sup_mul_eq_top_iff, sup_sq_eq_top_iff]

lemma mem_sqfRows {𝔪 : Ideal (𝓞 F)} {Y : ℝ} {a : Ideal (𝓞 F)} :
    a ∈ sqfRows 𝔪 Y ↔ IsExterior 𝔪 a ∧ Squarefree a ∧ (Ideal.absNorm a : ℝ) ≤ Y := by
  unfold sqfRows; rw [Set.Finite.mem_toFinset]; rfl

lemma mem_primesOf {𝔤 P : Ideal (𝓞 F)} : P ∈ primesOf 𝔤 ↔ P ∈ normalizedFactors 𝔤 := by
  unfold primesOf; rw [Multiset.mem_toFinset]

lemma primesOf_prime {𝔤 P : Ideal (𝓞 F)} (h : P ∈ primesOf 𝔤) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp := prime_of_normalized_factor P (mem_primesOf.1 h)
  exact ⟨Ideal.isPrime_of_prime hp, by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero⟩

lemma le_of_mem_primesOf {𝔤 P : Ideal (𝓞 F)} (h : P ∈ primesOf 𝔤) : 𝔤 ≤ P :=
  Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (mem_primesOf.1 h))

/-- `a ⊔ 𝔤 = ⊤` iff `a` lies in no prime factor of `𝔤`. -/
theorem sup_eq_top_iff_forall {a 𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) :
    a ⊔ 𝔤 = ⊤ ↔ ∀ P ∈ primesOf 𝔤, ¬ a ≤ P := by
  constructor
  · intro h P hP haP
    have hP' := primesOf_prime hP
    exact hP'.1.ne_top (top_le_iff.1 (h ▸ sup_le haP (le_of_mem_primesOf hP)))
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgM : 𝔤 ≤ M := le_trans le_sup_right hle
    have hM0 : M ≠ ⊥ := by
      rintro rfl; exact h𝔤 (le_bot_iff.1 hgM)
    have hMp : Prime M := Ideal.prime_of_isPrime hM0 hM.isPrime
    obtain ⟨Q, hQ, hQM⟩ := exists_mem_normalizedFactors_of_dvd
      (by rwa [Ne, ← Ideal.zero_eq_bot] at h𝔤) hMp.irreducible (Ideal.dvd_iff_le.2 hgM)
    have hQeq : Q = M := by
      rw [associated_iff_eq] at hQM; exact hQM.symm
    exact h Q (mem_primesOf.2 hQ) (hQeq ▸ le_trans le_sup_left hle)

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Zeta: `(s − 1) ζ_F(s)` and the coprime partial zeta functions

From the seam `exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq`.
* `R0 F`: entire, `= (s − 1) ζ_F(s)` on `Re s > 1`, polynomially bounded on `−1/2 ≤ Re s ≤ X`.
* `zeta_tsum`, `zeta_cop`: `ζ_F(s) = ∑' N I^{-s}`; `∑'_{I ⊔ q = ⊤} N I^{-s} = ζ_F(s) ∏_{P ∣ q}(1 − N P^{-s})`.
* `summable_norm_cpow`, `summable_absNorm_rpow`, `sieve`: the Dirichlet series and its Euler factors.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex

variable (F : Type*) [Field F] [NumberField F]

instance fiber_finite_L3Q (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

theorem R0_spec : Differentiable ℂ (R0 F) ∧
    (∀ s : ℂ, 1 < s.re → R0 F s = (s - 1) * dedekindZeta F s) ∧
    R0 F 1 = (dedekindZeta_residue F : ℂ) ∧
    ∀ X : ℝ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X →
      ‖R0 F s‖ ≤ C * (1 + |s.im|) ^ A := by
  obtain ⟨R, h1, h2, h3, h4, -⟩ :=
    exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq F
  exact Classical.epsilon_spec (p := fun R : ℂ → ℂ => Differentiable ℂ R ∧
    (∀ s : ℂ, 1 < s.re → R s = (s - 1) * dedekindZeta F s) ∧
    R 1 = (dedekindZeta_residue F : ℂ) ∧
    ∀ X : ℝ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X →
      ‖R s‖ ≤ C * (1 + |s.im|) ^ A) ⟨R, h1, h2, h3, h4⟩

theorem R0_diff : Differentiable ℂ (R0 F) := (R0_spec F).1

variable {F}

theorem R0_eq {s : ℂ} (hs : 1 < s.re) : R0 F s = (s - 1) * dedekindZeta F s :=
  (R0_spec F).2.1 s hs

variable (F) in
theorem R0_bound (X : ℝ) : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
    ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X → ‖R0 F s‖ ≤ C * (1 + |s.im|) ^ A :=
  (R0_spec F).2.2.2 X

theorem zeta_tsum {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta F s = ∑' I : Ideal (𝓞 F), (Ideal.absNorm I : ℂ) ^ (-s) :=
  (exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq F).choose_spec.2.2.2.2.1 s hs

theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) :=
  (exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq F).choose_spec.2.2.2.2.2.1 σ hσ

theorem sieve (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J) (hg : Summable g)
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    (∑' I, g I) * ∏ P ∈ T, (1 - g P) =
      ∑' I, ({I | ∀ P ∈ T, ¬ I ≤ P} : Set (Ideal (𝓞 F))).indicator g I :=
  (exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq F).choose_spec.2.2.2.2.2.2 g hmul hg T hT

theorem summable_norm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) => ‖(Ideal.absNorm I : ℂ) ^ (-s)‖) := by
  refine (summable_absNorm_rpow hs).congr fun I => ?_
  rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
  simp

lemma cpow_absNorm_mul (s : ℂ) (I J : Ideal (𝓞 F)) :
    (Ideal.absNorm (I * J) : ℂ) ^ (-s) =
      (Ideal.absNorm I : ℂ) ^ (-s) * (Ideal.absNorm J : ℂ) ^ (-s) := by
  rw [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem summable_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℂ) ^ (-s) :=
  (summable_norm_cpow hs).of_norm

/-- Ideals coprime to `q`: `∑'_{I ⊔ q = ⊤} N I^{-s} = ζ_F(s) ∏_{P ∣ q} (1 − N P^{-s})`. -/
theorem zeta_cop {q : Ideal (𝓞 F)} (hq : q ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    ∑' I : Ideal (𝓞 F), (if I ⊔ q = ⊤ then (Ideal.absNorm I : ℂ) ^ (-s) else 0) =
      dedekindZeta F s * ∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-s)) := by
  classical
  have h := sieve (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℂ) ^ (-s))
    (cpow_absNorm_mul s) (summable_cpow hs) (primesOf q) (fun P hP => primesOf_prime hP)
  rw [zeta_tsum hs, h]
  congr 1; funext I
  by_cases hI : I ⊔ q = ⊤
  · rw [if_pos hI, Set.indicator_of_mem]
    exact (sup_eq_top_iff_forall hq).1 hI
  · rw [if_neg hI, Set.indicator_of_notMem]
    exact fun h' => hI ((sup_eq_top_iff_forall hq).2 h')

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3H_Core: finite bilinear-form bounds and the row-multiplication step (GL Lemma 4.4)

`SBf χ R Cs v`: for every coefficient vector `z`, `∑_{a ∈ R} |∑_{c ∈ Cs} z c χ a c|² ≤ v ∑ |z c|²`.

* `SBf.mono_rows`, `SBf.union`, `SBf.biUnion`: row-set bookkeeping.
* `SBf.of_inj`: rows that map injectively into `R'` with `χ a c = w c χ (f a) c`, `‖w c‖ ≤ 1`.
* `SBf.lift`: Heath-Brown's Lemma 9 (GL Lemma 4.4) in abstract form: if rows can be multiplied by
  any of a family `P` of "primes", each row or column being divisible by at most `ω` of them and
  `8 ω ≤ #P`, then a bound `W` for the multiplied rows gives the bound `8 W`.
-/

namespace L3H

open Finset

variable {I : Type*}

variable {χ : I → I → ℂ}

end L3H

end
end

section
section
/-! # L3H_NT: the quadratic family `χ_𝔠(𝔡) = residueSymbol 𝔡 (gen 𝔠)³` as a finite kernel

* `rowsF 𝔪 lo hi`: exterior squarefree ideals with `lo < N 𝔡 ≤ hi`, as a `Finset`.
* `chiK ι 𝔪 g 𝔡 𝔠 = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 3`.
* `chiK_mul_row`: `χ(a) = w · χ(a p)` with `‖w‖ = 1` for an exterior good prime `p ∤ 𝔠`.
* `sb_iff_dyadic`, `sb_of_SBf`: the `tsum`-over-subtypes statements against `SBf`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

/-! ### Residue symbols -/

/-! ### Multiplicativity of the symbol (without `C3I.chi`) -/

/-! ### The kernel -/

/-! ### Ideal facts -/

/-! ### Row and column sets -/

lemma fin_set (𝔪 : Ideal (𝓞 F)) (lo hi : ℝ) :
    {𝔡 : Ideal (𝓞 F) | IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ lo < (Ideal.absNorm 𝔡 : ℝ) ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ hi}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊hi⌋₊).subset
    (fun 𝔡 h => Nat.le_floor h.2.2.2)

/-- Exterior squarefree ideals with `lo < N 𝔡 ≤ hi`. -/
noncomputable def rowsF (𝔪 : Ideal (𝓞 F)) (lo hi : ℝ) : Finset (Ideal (𝓞 F)) :=
  (fin_set 𝔪 lo hi).toFinset

lemma mem_rowsF {𝔪 : Ideal (𝓞 F)} {lo hi : ℝ} {𝔡 : Ideal (𝓞 F)} :
    𝔡 ∈ rowsF 𝔪 lo hi ↔ IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ lo < (Ideal.absNorm 𝔡 : ℝ) ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ hi := by
  unfold rowsF; rw [Set.Finite.mem_toFinset]; rfl

lemma one_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

lemma mem_rowsF_zero {𝔪 : Ideal (𝓞 F)} {hi : ℝ} {𝔡 : Ideal (𝓞 F)} :
    𝔡 ∈ rowsF 𝔪 0 hi ↔ IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ hi := by
  rw [mem_rowsF]
  constructor
  · rintro ⟨h1, h2, -, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨h1, h2, lt_of_lt_of_le zero_lt_one (one_le_absNorm h1.1), h4⟩

/-! ### `tsum` over subtypes -/

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)

end L3H

end
end

section
section
/-!
# L3Q_Orig: the part `s(a) ≤ L` of the original sum (GL's `T′` plus the error `RP`)

For a pair character `ψ` (`PsiHyp`) and `q = 𝔤 𝔪 c`:
`∑_{a ⊔ 𝔤 = ⊤, s(a) ≤ L} W(Na/M) ψ(a) = ∑_{s ∈ Srow} ψ(s) [κ (Ns/M)^{-1/2} Wm(1/2) ∏_{P∣q}(1 − 1/NP)
  + (2π)⁻¹ ∫ Wm(ε+it) (Ns/M)^{-(ε+it)} ∏_{P∣q}(1 − NP^{-2(ε+it)}) R0(2(ε+it))/(2(ε+it) − 1) dt]`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

instance countable_ideal_L3Q : Countable (Ideal (𝓞 F)) :=
  (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).symm.injective.countable

lemma mem_Srow {𝔪 𝔤 : Ideal (𝓞 F)} {L : ℝ} {s : Ideal (𝓞 F)} :
    s ∈ Srow 𝔪 𝔤 L ↔ IsExterior 𝔪 s ∧ Squarefree s ∧ (Ideal.absNorm s : ℝ) ≤ L ∧ s ⊔ 𝔤 = ⊤ := by
  classical
  unfold Srow
  rw [Finset.mem_filter, mem_sqfRows]
  tauto

lemma sqfRows_eq (𝔪 : Ideal (𝓞 F)) (Y : ℝ) : sqfRows 𝔪 Y = L3H.rowsF 𝔪 0 Y := by
  ext a; rw [mem_sqfRows, L3H.mem_rowsF_zero]

lemma tsum_subtype_of_zero' {β E : Type*} [AddCommMonoid E] [TopologicalSpace E] (p : β → Prop)
    (S : Finset β) (hS : ∀ x ∈ S, p x) (f : β → E) (hf : ∀ x, p x → x ∉ S → f x = 0) :
    ∑' x : {x // p x}, f x.1 = ∑ x ∈ S, f x := by
  classical
  change ∑' x : ({x | p x} : Set β), f x = _
  rw [tsum_subtype, tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hS x hx)]
  · intro x hx
    by_cases h : p x
    · rw [Set.indicator_of_mem (show x ∈ {x | p x} from h)]; exact hf x h hx
    · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from h)]

lemma W_div_eq_zero {M x : ℝ} (hM : 0 < M) (hx : 3 * M ≤ x) : W (x / M) = 0 :=
  W_eq_zero (Or.inr (by rw [lt_div_iff₀ hM]; linarith))

lemma finite_absNorm_le (X : ℝ) : {a : Ideal (𝓞 F) | (Ideal.absNorm a : ℝ) ≤ X}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).subset fun a h => Nat.le_floor h

lemma cpow_natCast_sq (n : ℕ) (z : ℂ) : ((n : ℂ) ^ 2) ^ z = (n : ℂ) ^ (2 * z) := by
  rw [← natCast_cpow_natCast_mul]; norm_num

lemma norm_cpow_neg_le {X : ℝ} (hX : 0 < X) {a b : ℝ} {w : ℂ} (ha : a ≤ w.re) (hb : w.re ≤ b) :
    ‖(X : ℂ) ^ (-w)‖ ≤ X ^ (-a) + X ^ (-b) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, neg_re]
  rcases le_or_gt 1 X with h1 | h1
  · have : X ^ (-w.re) ≤ X ^ (-a) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith [Real.rpow_nonneg hX.le (-b)]
  · have : X ^ (-w.re) ≤ X ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_ge hX h1.le (by linarith)
    linarith [Real.rpow_nonneg hX.le (-a)]

lemma norm_natCast_cpow_neg_le_one {n : ℕ} (hn : 1 ≤ n) {u : ℂ} (hu : 0 ≤ u.re) :
    ‖(n : ℂ) ^ (-u)‖ ≤ 1 := by
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp; linarith)

lemma one_le_absNorm_of_mem_primesOf {q P : Ideal (𝓞 F)} (hP : P ∈ primesOf q) :
    1 ≤ Ideal.absNorm P := by
  have := (primesOf_prime hP).2
  exact Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact this)

lemma norm_prod_one_sub_le (q : Ideal (𝓞 F)) {u : ℂ} (hu : 0 ≤ u.re) :
    ‖∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-u))‖ ≤ 2 ^ (primesOf q).card := by
  refine (Finset.norm_prod_le _ _).trans ?_
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
  refine (norm_sub_le _ _).trans ?_
  have := norm_natCast_cpow_neg_le_one (one_le_absNorm_of_mem_primesOf hP) hu
  rw [norm_one]; linarith

lemma differentiable_prod_one_sub (q : Ideal (𝓞 F)) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun w => ∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-f w)) := by
  intro w
  refine DifferentiableAt.fun_finsetProd fun P hP => ?_
  have hN : (Ideal.absNorm P : ℂ) ≠ 0 := by
    have := one_le_absNorm_of_mem_primesOf hP
    exact_mod_cast (by omega : Ideal.absNorm P ≠ 0)
  exact (differentiableAt_const _).sub ((hf w).neg.const_cpow (Or.inl hN))

/-- The `r`-sum: `∑'_{r ⊔ q = ⊤} W(X N r²)`, by Mellin inversion and a shift past `w = 1/2`. -/
theorem rsum_eq {q : Ideal (𝓞 F)} (hq : q ≠ ⊥) (hqt : q ≠ ⊤) {X : ℝ} (hX : 0 < X) {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∑' r : Ideal (𝓞 F), (if r ⊔ q = ⊤ then (W (X * (Ideal.absNorm r : ℝ) ^ 2) : ℂ) else 0) =
      R0 F 1 / 2 * (X : ℂ) ^ (-(1 / 2 : ℂ)) * Wm (1 / 2) *
          (∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) +
        (1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (ε + t * I) *
          ((X : ℂ) ^ (-((ε : ℂ) + t * I)) *
            (∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((ε : ℂ) + t * I))))) *
            R0 F (2 * ((ε : ℂ) + t * I)) / (2 * ((ε : ℂ) + t * I) - 1)) := by
  classical
  -- index set: ideals coprime to `q`
  have hne : ∀ r : Ideal (𝓞 F), r ⊔ q = ⊤ → r ≠ ⊥ := by
    intro r hr h; rw [h, bot_sup_eq] at hr; exact hqt hr
  set ι := {r : Ideal (𝓞 F) // r ⊔ q = ⊤}
  have hx : ∀ r : ι, 0 < X * (Ideal.absNorm r.1 : ℝ) ^ 2 := fun r =>
    mul_pos hX (pow_pos (absNorm_pos (hne r.1 r.2)) 2)
  have hsub : ∀ (f : Ideal (𝓞 F) → ℂ), ∑' r : Ideal (𝓞 F), (if r ⊔ q = ⊤ then f r else 0) =
      ∑' r : ι, f r.1 := by
    intro f
    have h := tsum_subtype ({r | r ⊔ q = ⊤} : Set (Ideal (𝓞 F))) f
    rw [show (∑' r : ι, f r.1) = ∑' x : ({r | r ⊔ q = ⊤} : Set (Ideal (𝓞 F))), f x from rfl, h]
    exact tsum_congr fun r => rfl
  have hsum2 : Summable fun r : Ideal (𝓞 F) => ((Ideal.absNorm r : ℕ) : ℝ) ^ (-(2 : ℝ)) :=
    summable_absNorm_rpow (by norm_num)
  have hS : Summable fun r : ι => ‖(1 : ℂ)‖ * (X * (Ideal.absNorm r.1 : ℝ) ^ 2) ^ (-(1 : ℝ)) := by
    refine ((hsum2.subtype _).mul_left X⁻¹).congr fun r => ?_
    have hN := absNorm_pos (hne r.1 r.2)
    rw [norm_one, one_mul, Real.mul_rpow hX.le (by positivity), Real.rpow_neg_one,
      ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  rw [hsub (fun r => (W (X * (Ideal.absNorm r : ℝ) ^ 2) : ℂ))]
  have hmel := tsum_W_eq (fun _ : ι => (1 : ℂ)) (fun r => X * (Ideal.absNorm r.1 : ℝ) ^ 2) hx 1 hS
  simp only [one_mul] at hmel
  rw [hmel]
  -- the Dirichlet series on `Re w = 1`
  have hline : ∀ t : ℝ, ∑' r : ι, ((X * (Ideal.absNorm r.1 : ℝ) ^ 2 : ℝ) : ℂ) ^
      (-(((1 : ℝ) : ℂ) + t * I)) =
      (X : ℂ) ^ (-((1 : ℂ) + t * I)) * (dedekindZeta F (2 * ((1 : ℂ) + t * I)) *
        ∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((1 : ℂ) + t * I))))) := by
    intro t
    have hre : 1 < (2 * ((1 : ℂ) + t * I)).re := by norm_num
    rw [← zeta_cop hq hre, hsub, ← tsum_mul_left]
    congr 1; funext r
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hX.le (by positivity)]
    congr 1
    push_cast
    rw [cpow_natCast_sq]; ring_nf
  simp_rw [hline]
  -- rewrite `ζ(2w) = R0(2w)/(2w − 1)` and shift
  obtain ⟨Af, hAf⟩ : ∃ Af : ℂ → ℂ, Af = fun w => (X : ℂ) ^ (-w) *
    (∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * w)))) * R0 F (2 * w) / 2 := ⟨_, rfl⟩
  have hzeta : ∀ w : ℂ, 1 / 2 < w.re → (X : ℂ) ^ (-w) * (dedekindZeta F (2 * w) *
      ∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * w)))) = Af w / (w - 1 / 2) := by
    intro w hw
    have hre : 1 < (2 * w).re := by simp; linarith
    have hne' : w - 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [hAf]; dsimp only
    rw [R0_eq hre, eq_div_iff hne']
    ring
  obtain ⟨CR, AR, hCR, hAR, hRb⟩ := R0_bound F 2
  have hAfd : DifferentiableOn ℂ Af {s | ε ≤ s.re ∧ s.re ≤ 1} := by
    rw [hAf]
    refine Differentiable.differentiableOn ?_
    refine ((((differentiable_id.neg).const_cpow (Or.inl ?_)).mul
      (differentiable_prod_one_sub q (differentiable_id.const_mul 2))).mul
      ((R0_diff F).comp (differentiable_id.const_mul 2))).div_const 2
    exact_mod_cast hX.ne'
  have hAfb : ∀ w : ℂ, ε ≤ w.re → w.re ≤ 1 → ‖Af w‖ ≤
      ((X ^ (-ε) + X ^ (-(1 : ℝ))) * 2 ^ (primesOf q).card * (CR * 2 ^ AR) / 2) *
        (1 + |w.im|) ^ AR := by
    intro w h1 h2
    rw [hAf]; dsimp only
    rw [norm_div, norm_mul, norm_mul, Complex.norm_two]
    have e1 := norm_cpow_neg_le hX h1 h2
    have e2 := norm_prod_one_sub_le q (u := 2 * w) (by simp; linarith)
    have e3 := hRb (2 * w) (by simp; linarith) (by simp; linarith)
    have him : |(2 * w).im| = 2 * |w.im| := by simp [abs_mul]
    rw [him] at e3
    have e4 : (1 + 2 * |w.im|) ^ AR ≤ 2 ^ AR * (1 + |w.im|) ^ AR := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg w.im]) hAR
    have e3' : ‖R0 F (2 * w)‖ ≤ CR * 2 ^ AR * (1 + |w.im|) ^ AR := by
      calc ‖R0 F (2 * w)‖ ≤ CR * (1 + 2 * |w.im|) ^ AR := e3
        _ ≤ CR * (2 ^ AR * (1 + |w.im|) ^ AR) := by gcongr
        _ = _ := by ring
    have hx0 : 0 ≤ X ^ (-ε) + X ^ (-(1 : ℝ)) := by positivity
    calc ‖(X : ℂ) ^ (-w)‖ * ‖∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * w)))‖ *
          ‖R0 F (2 * w)‖ / 2
        ≤ (X ^ (-ε) + X ^ (-(1 : ℝ))) * 2 ^ (primesOf q).card *
          (CR * 2 ^ AR * (1 + |w.im|) ^ AR) / 2 := by gcongr
      _ = _ := by ring
  have hshift := shift_pole (Af := Af) (a := ε) (b := 1) (p := 1 / 2) (by linarith) (by norm_num)
    hAR hAfd hAfb
  -- assemble
  have hcongr : ∫ t : ℝ, Wm (((1 : ℝ) : ℂ) + t * I) * ((X : ℂ) ^ (-((1 : ℂ) + t * I)) *
      (dedekindZeta F (2 * ((1 : ℂ) + t * I)) *
        ∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((1 : ℂ) + t * I)))))) =
      ∫ t : ℝ, Wm (((1 : ℝ) : ℂ) + t * I) *
        (Af (((1 : ℝ) : ℂ) + t * I) / ((((1 : ℝ) : ℂ) + t * I) - ((1 / 2 : ℝ) : ℂ))) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [hzeta _ (by simp; norm_num)]
    push_cast; ring_nf
  rw [hcongr, hshift]
  have hres : Af ((1 / 2 : ℝ) : ℂ) = (X : ℂ) ^ (-(1 / 2 : ℂ)) *
      (∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) * R0 F 1 / 2 := by
    rw [hAf]; dsimp only; push_cast; ring_nf
  have alg : ∀ a b c d w : ℂ, 2 * w - 1 ≠ 0 →
      d * (a * b * c / 2 / (w - 1 / 2)) = d * (a * b * c / (2 * w - 1)) := by
    intro a b c d w hw
    have hw' : w - 1 / 2 ≠ 0 := by
      intro h; apply hw; linear_combination 2 * h
    field_simp
  have hline2 : ∀ t : ℝ, Wm ((ε : ℂ) + t * I) * (Af ((ε : ℂ) + t * I) / (((ε : ℂ) + t * I) -
      ((1 / 2 : ℝ) : ℂ))) = Wm ((ε : ℂ) + t * I) * ((X : ℂ) ^ (-((ε : ℂ) + t * I)) *
        (∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((ε : ℂ) + t * I))))) *
        R0 F (2 * ((ε : ℂ) + t * I)) / (2 * ((ε : ℂ) + t * I) - 1)) := by
    intro t
    have hne2 : 2 * ((ε : ℂ) + t * I) - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [hAf, show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by push_cast; ring]
    exact alg _ _ _ _ _ hne2
  rw [integral_congr_ae (Eventually.of_forall hline2), hres,
    show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by push_cast; ring]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ t : ℝ, Wm ((ε : ℂ) + t * I) * ((X : ℂ) ^ (-((ε : ℂ) + t * I)) *
        (∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((ε : ℂ) + t * I))))) *
        R0 F (2 * ((ε : ℂ) + t * I)) / (2 * ((ε : ℂ) + t * I) - 1))) = J
  generalize (∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) = Pq
  field_simp
  ring

lemma W_zero : W 0 = 0 := W_eq_zero (Or.inl (by norm_num))

lemma psi_sq_eq {𝔪 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ) {r : Ideal (𝓞 F)}
    (hr : r ≠ ⊥) : ψ r ^ 2 = if r ⊔ 𝔪 = ⊤ ∧ r ⊔ c = ⊤ then 1 else 0 := by
  by_cases h1 : r ⊔ 𝔪 = ⊤
  · rw [hψ.sq r hr h1]; simp [h1]
  · rw [hψ.nonext r hr h1]; simp [h1]

lemma sup_q_iff {r 𝔤 𝔪 c : Ideal (𝓞 F)} :
    r ⊔ 𝔤 * 𝔪 * c = ⊤ ↔ r ⊔ 𝔤 = ⊤ ∧ r ⊔ 𝔪 = ⊤ ∧ r ⊔ c = ⊤ := by
  rw [sup_comm, sup_mul_eq_top_iff, sup_mul_eq_top_iff, sup_comm 𝔤, sup_comm 𝔪, sup_comm c]
  tauto

open Classical in
/-- The part `s(a) ≤ L` of the original sum. -/
theorem Ale_eq {𝔪 𝔤 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ)
    (hq : 𝔤 * 𝔪 * c ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤) {M : ℝ} (hM : 0 < M) (L : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) :
    ∑' a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ ∧ ¬ sgt L a then
        (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0) =
      ∑ s ∈ Srow 𝔪 𝔤 L, ψ s *
        (R0 F 1 / 2 * (((Ideal.absNorm s : ℝ) / M : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * Wm (1 / 2) *
            (∏ P ∈ primesOf (𝔤 * 𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) +
          (1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (ε + t * I) *
            ((((Ideal.absNorm s : ℝ) / M : ℝ) : ℂ) ^ (-((ε : ℂ) + t * I)) *
              (∏ P ∈ primesOf (𝔤 * 𝔪 * c),
                (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((ε : ℂ) + t * I))))) *
              R0 F (2 * ((ε : ℂ) + t * I)) / (2 * ((ε : ℂ) + t * I) - 1))) := by
  classical
  set q := 𝔤 * 𝔪 * c with hqdef
  have hqt : q ≠ ⊤ := by
    intro h; apply h𝔪t
    have : q ≤ 𝔪 := Ideal.le_of_dvd (dvd_mul_of_dvd_left (dvd_mul_left 𝔪 𝔤) c)
    exact top_le_iff.1 (h ▸ this)
  set f : Ideal (𝓞 F) → ℂ := fun a => if a ⊔ 𝔤 = ⊤ ∧ ¬ sgt L a then
    (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0 with hf
  have hf0 : f ⊥ = 0 := by
    simp only [hf]; split_ifs <;> simp [W_zero]
  rw [← tsum_sqdec f hf0]
  -- the summand on `(s, r)`
  set g : Ideal (𝓞 F) → ℂ := fun s => if s ⊔ 𝔤 = ⊤ ∧ (Ideal.absNorm s : ℝ) ≤ L then ψ s else 0
  set h : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun s r =>
    if r ⊔ q = ⊤ then (W ((Ideal.absNorm s : ℝ) / M * (Ideal.absNorm r : ℝ) ^ 2) : ℂ) else 0
  have hfg : ∀ p : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} × {r : Ideal (𝓞 F) // r ≠ ⊥},
      f (p.1.1 * p.2.1 ^ 2) = g p.1.1 * h p.1.1 p.2.1 := by
    rintro ⟨⟨s, hs, hsq⟩, ⟨r, hr⟩⟩
    simp only [hf, g, h]
    have e1 : s * r ^ 2 ⊔ 𝔤 = ⊤ ↔ s ⊔ 𝔤 = ⊤ ∧ r ⊔ 𝔤 = ⊤ := sup_mul_sq_eq_top_iff
    have hsgt : sgt L (s * r ^ 2) ↔ L < Ideal.absNorm s := sfree_gt_iff hs hr hsq L
    have hψsr : ψ (s * r ^ 2) = ψ s * (if r ⊔ 𝔪 = ⊤ ∧ r ⊔ c = ⊤ then 1 else 0) := by
      rw [hψ.mul s (r ^ 2) hs (pow_ne_zero 2 hr), pow_two r, hψ.mul r r hr hr, ← pow_two,
        psi_sq_eq hψ hr]
    have e2 : r ⊔ q = ⊤ ↔ r ⊔ 𝔤 = ⊤ ∧ r ⊔ 𝔪 = ⊤ ∧ r ⊔ c = ⊤ := sup_q_iff
    have hW : (Ideal.absNorm (s * r ^ 2) : ℝ) / M =
        (Ideal.absNorm s : ℝ) / M * (Ideal.absNorm r : ℝ) ^ 2 := by
      simp [map_mul, map_pow]; ring
    rw [hW, hψsr]
    by_cases h1 : s ⊔ 𝔤 = ⊤ <;> by_cases h2 : (Ideal.absNorm s : ℝ) ≤ L <;>
      by_cases h3 : r ⊔ 𝔤 = ⊤ <;> by_cases h4 : r ⊔ 𝔪 = ⊤ ∧ r ⊔ c = ⊤ <;>
      simp [e1, e2, hsgt, h1, h2, h3, h4, mul_comm]
  simp_rw [hfg]
  have hsupp : (Function.support fun p : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} ×
      {r : Ideal (𝓞 F) // r ≠ ⊥} => g p.1.1 * h p.1.1 p.2.1) ⊆
      sqMap ⁻¹' {a | (Ideal.absNorm a : ℝ) ≤ 3 * M} := by
    intro p hp
    simp only [Function.mem_support] at hp
    show (Ideal.absNorm (p.1.1 * p.2.1 ^ 2) : ℝ) ≤ 3 * M
    by_contra hc; push Not at hc
    apply hp
    have hW : W ((Ideal.absNorm p.1.1 : ℝ) / M * (Ideal.absNorm p.2.1 : ℝ) ^ 2) = 0 := by
      have : (Ideal.absNorm p.1.1 : ℝ) / M * (Ideal.absNorm p.2.1 : ℝ) ^ 2 =
          (Ideal.absNorm (p.1.1 * p.2.1 ^ 2) : ℝ) / M := by
        simp [map_mul, map_pow]; ring
      rw [this]; exact W_div_eq_zero hM hc.le
    simp only [h, hW, Complex.ofReal_zero, ite_self, mul_zero]
  have hfin := ((finite_absNorm_le (F := F) (3 * M)).preimage sqMap_injective.injOn).subset hsupp
  rw [(summable_of_finite_support hfin).tsum_prod' (fun s => summable_of_finite_support
    (hfin.preimage (Prod.mk_right_injective s).injOn))]
  simp_rw [tsum_mul_left]
  have hr : ∀ s : Ideal (𝓞 F), ∑' r : {r : Ideal (𝓞 F) // r ≠ ⊥}, h s r.1 = ∑' r, h s r := by
    intro s
    have hsupp' : Function.support (h s) ⊆ {r | r ≠ ⊥} := by
      refine Function.support_subset_iff.2 fun r hr0 => ?_
      rintro rfl
      apply hr0
      simp only [h, bot_sup_eq, if_neg hqt]
    exact tsum_subtype_eq_of_support_subset hsupp'
  simp_rw [hr]
  refine (tsum_subtype_of_zero' (fun s => s ≠ ⊥ ∧ Squarefree s) (Srow 𝔪 𝔤 L)
    (fun s hs => ⟨(mem_Srow.1 hs).1.1, (mem_Srow.1 hs).2.1⟩)
    (fun s => g s * ∑' r, h s r) ?_).trans ?_
  · intro s hs hsS
    simp only [g]
    split_ifs with hc
    · have hext : ¬ s ⊔ 𝔪 = ⊤ := by
        intro he
        exact hsS (mem_Srow.2 ⟨⟨hs.1, he⟩, hs.2, hc.2, hc.1⟩)
      rw [hψ.nonext s hs.1 hext, zero_mul]
    · rw [zero_mul]
  · refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hse, hsq, hsL, hsg⟩ := mem_Srow.1 hs
    simp only [g, hsg, hsL, and_self, if_true]
    congr 1
    simp only [h]
    exact rsum_eq hq hqt (div_pos (absNorm_pos hse.1) hM) hε hε2

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3K_Gamma: the Gamma-factor ratio on the left edge of the convexity strip

* `norm_Gamma_mono`: `σ ↦ ‖Γ(σ + it)‖ / Γ(σ)` is nondecreasing on `σ > 0` (Gauss's product).
* `norm_Gamma_one_add_sq`: `‖Γ(1 + it)‖² = π |t| / |sinh(π t)|`.
* `exists_norm_Gammaℂ_ratio_le`: for `0 < δ < 1`,
  `‖Γ_ℂ(1 + δ − it) / Γ_ℂ(−δ + it)‖ ≤ C (1 + |t|)^3`. -/

open Complex Filter Topology

set_option autoImplicit false

namespace ArtinPrimitiveRoots

namespace L3K

lemma norm_GammaSeq (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq s n‖ =
      (n : ℝ) ^ s.re * (Nat.factorial n : ℝ) / ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  rw [GammaSeq, norm_div, norm_mul, norm_prod,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma prod_pos_norm {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    0 < ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  refine Finset.prod_pos fun j _ => norm_pos_iff.2 fun h => ?_
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma term_ineq {x y t : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(y : ℂ) + t * I‖ * ‖(x : ℂ)‖ ≤ ‖(x : ℂ) + t * I‖ * ‖(y : ℂ)‖ := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hy]
  have e1 : √(y ^ 2 + t ^ 2) * x = √((y ^ 2 + t ^ 2) * x ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hx.le]
  have e2 : √(x ^ 2 + t ^ 2) * y = √((x ^ 2 + t ^ 2) * y ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
  rw [e1, e2]
  apply Real.sqrt_le_sqrt
  have h1 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.le hxy 2
  nlinarith [sq_nonneg t]

/-- `‖Γ(a + it)‖ Γ(b) ≤ ‖Γ(b + it)‖ Γ(a)` for `0 < a ≤ b`. -/
theorem norm_Gamma_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    ‖Gamma ((a : ℂ) + t * I)‖ * ‖Gamma (b : ℂ)‖ ≤ ‖Gamma ((b : ℂ) + t * I)‖ * ‖Gamma (a : ℂ)‖ := by
  have hb : 0 < b := ha.trans_le hab
  have key : ∀ n : ℕ, n ≠ 0 →
      ‖GammaSeq ((a : ℂ) + t * I) n‖ * ‖GammaSeq (b : ℂ) n‖ ≤
        ‖GammaSeq ((b : ℂ) + t * I) n‖ * ‖GammaSeq (a : ℂ) n‖ := by
    intro n hn
    have hre : ∀ x : ℝ, ((x : ℂ) + t * I).re = x := fun x => by simp
    rw [norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn,
      hre, hre, Complex.ofReal_re, Complex.ofReal_re]
    have hPa := prod_pos_norm (s := (a : ℂ) + t * I) (by rw [hre]; exact ha) n
    have hPb := prod_pos_norm (s := (b : ℂ) + t * I) (by rw [hre]; exact hb) n
    have hQa := prod_pos_norm (s := (a : ℂ)) (by simpa using ha) n
    have hQb := prod_pos_norm (s := (b : ℂ)) (by simpa using hb) n
    rw [div_mul_div_comm, div_mul_div_comm]
    have hnum : (n : ℝ) ^ a * (Nat.factorial n : ℝ) * ((n : ℝ) ^ b * (Nat.factorial n : ℝ)) =
        (n : ℝ) ^ b * (Nat.factorial n : ℝ) * ((n : ℝ) ^ a * (Nat.factorial n : ℝ)) := by ring
    rw [hnum]
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hPb hQa)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun j _ => by positivity)
    intro j _
    have e1 : ∀ x : ℝ, (x : ℂ) + t * I + j = ((x + j : ℝ) : ℂ) + t * I := fun x => by
      push_cast; ring
    have e2 : ∀ x : ℝ, (x : ℂ) + j = ((x + j : ℝ) : ℂ) := fun x => by push_cast; ring
    rw [e1, e1, e2, e2]
    exact term_ineq (by positivity) (by linarith)
  have hlim : ∀ s : ℂ, Tendsto (fun n => ‖GammaSeq s n‖) atTop (𝓝 ‖Gamma s‖) :=
    fun s => (GammaSeq_tendsto_Gamma s).norm
  exact le_of_tendsto_of_tendsto ((hlim _).mul (hlim _)) ((hlim _).mul (hlim _))
    (by filter_upwards [eventually_ne_atTop 0] with n hn using key n hn)

lemma norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h3 : ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ ≤ Real.exp z.im + Real.exp (-z.im) := by
    rw [← h1, ← h2]; exact norm_sub_le _ _
  have h4 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h5 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-- `‖Γ(1 + it)‖² ‖sin(π(1 + it))‖ = π |t|`. -/
lemma norm_Gamma_one_add_sq_mul (t : ℝ) :
    ‖Gamma (1 + t * I)‖ ^ 2 * ‖Complex.sin ((Real.pi : ℂ) * (1 + t * I))‖ = Real.pi * |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hz : (-(t : ℂ) * I) ≠ 0 := by
    simp [ht]
  have hrefl := Gamma_mul_Gamma_one_sub (1 + t * I)
  have hsub : (1 : ℂ) - (1 + t * I) = -(t : ℂ) * I := by ring
  rw [hsub] at hrefl
  have hconj : Gamma (1 - t * I) = (starRingEnd ℂ) (Gamma (1 + t * I)) := by
    rw [← Gamma_conj]; congr 1; simp [Complex.conj_ofReal]; ring
  have hadd : Gamma (1 - t * I) = (-(t : ℂ) * I) * Gamma (-(t : ℂ) * I) := by
    have := Gamma_add_one (-(t : ℂ) * I) hz
    rw [show -(t : ℂ) * I + 1 = 1 - t * I by ring] at this
    exact this
  have hsq : (‖Gamma (1 + t * I)‖ ^ 2 : ℂ) = Gamma (1 + t * I) * Gamma (1 - t * I) := by
    rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 + t * I)) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrefl
    rcases mul_eq_zero.1 hrefl with h | h
    · exact Gamma_ne_zero_of_re_pos (by simp) h
    · exact Gamma_ne_zero (fun m hm => by
        have := congrArg Complex.re hm; simp at this
        have := congrArg Complex.im hm; simp at this; exact ht this) h
  have key : (‖Gamma (1 + t * I)‖ ^ 2 : ℂ) * Complex.sin ((Real.pi : ℂ) * (1 + t * I)) =
      (-(t : ℂ) * I) * Real.pi := by
    rw [hsq, hadd, show Gamma (1 + t * I) * (-(t : ℂ) * I * Gamma (-(t : ℂ) * I)) =
      (-(t : ℂ) * I) * (Gamma (1 + t * I) * Gamma (-(t : ℂ) * I)) by ring, hrefl]
    field_simp
  have := congrArg (‖·‖) key
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_neg,
    Complex.norm_I, mul_one, abs_norm] at this
  rw [this, abs_of_pos Real.pi_pos]; ring

lemma norm_sin_pi_one_add (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * (1 + t * I))‖ = |Real.sinh (Real.pi * t)| := by
  rw [show (Real.pi : ℂ) * (1 + t * I) = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi by push_cast; ring,
    Complex.sin_add_pi, norm_neg, Complex.sin_mul_I, norm_mul, Complex.norm_I, mul_one,
    ← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]

/-- `‖Γ(1 + it)‖² ≤ 4π e^π (1 + |t|) e^{−π|t|}`. -/
lemma norm_Gamma_one_add_sq_le (t : ℝ) :
    ‖Gamma (1 + t * I)‖ ^ 2 ≤ 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|)) := by
  have hk := norm_Gamma_one_add_sq_mul t
  rw [norm_sin_pi_one_add] at hk
  have hsh : |Real.sinh (Real.pi * t)| = Real.sinh (Real.pi * |t|) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
  rw [hsh] at hk
  set G := ‖Gamma (1 + t * I)‖ ^ 2 with hG
  set x := Real.pi * |t| with hx
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hx0 : 0 ≤ x := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hE : 1 ≤ Real.exp Real.pi := Real.one_le_exp hpi.le
  have hRHS : 4 * Real.pi * (1 + |t|) * Real.exp (-x) ≤
      4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-x) := by
    have : 0 ≤ 4 * Real.pi * (1 + |t|) * Real.exp (-x) := by positivity
    nlinarith
  rcases eq_or_lt_of_le hx0 with h0 | hpos
  · have ht : t = 0 := by
      have : |t| = 0 := by
        rcases mul_eq_zero.1 h0.symm with h | h
        · exact absurd h hpi.ne'
        · exact h
      exact abs_eq_zero.1 this
    subst ht
    have : G = 1 := by rw [hG]; simp
    rw [this, ← h0, abs_zero, add_zero, neg_zero, Real.exp_zero, mul_one, mul_one]
    nlinarith
  have hsx : 0 < Real.sinh x := Real.sinh_pos_iff.2 hpos
  have hGeq : G = x / Real.sinh x := by field_simp; linarith
  rcases le_or_gt Real.pi x with hbig | hsmall
  · -- `sinh x ≥ e^x / 4`
    have hex : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have hemx : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hsh4 : Real.exp x / 4 ≤ Real.sinh x := by
      rw [Real.sinh_eq]; linarith
    have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hG4 : G ≤ 4 * x * Real.exp (-x) := by
      rw [hGeq, div_le_iff₀ hsx]
      have h1 : 4 * x * Real.exp (-x) * (Real.exp x / 4) = x := by
        field_simp
        rw [mul_comm]; exact hprod
      have : 0 ≤ 4 * x * Real.exp (-x) := by positivity
      nlinarith
    refine hG4.trans (le_trans ?_ hRHS)
    have : x ≤ Real.pi * (1 + |t|) := by rw [hx]; nlinarith [abs_nonneg t]
    have he := Real.exp_pos (-x)
    nlinarith
  · have hG1 : G ≤ 1 := by
      rw [hGeq, div_le_one hsx]; exact Real.self_le_sinh_iff.2 hx0
    refine hG1.trans ?_
    have hex : Real.exp (-Real.pi) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    have hep : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by rw [← Real.exp_add]; simp
    have : 1 ≤ 4 * Real.pi * (1 + |t|) * Real.exp (-x) * Real.exp Real.pi := by
      have h1 : 1 ≤ 4 * Real.pi * (1 + |t|) := by nlinarith [abs_nonneg t]
      have h2 : 1 ≤ Real.exp (-x) * Real.exp Real.pi := by nlinarith [Real.exp_pos (-Real.pi)]
      nlinarith [Real.exp_pos (-x)]
    have e : 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-x) =
        4 * Real.pi * (1 + |t|) * Real.exp (-x) * Real.exp Real.pi := by ring
    linarith

end L3K

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L3Q_Gam: the gamma ratio `G₀(w) = Γ_ℂ(1−w)/Γ_ℂ(w)`

`G₀ w = (2π)^{2w−1} Γ(1−w)² sin(πw) / π`: holomorphic on `Re w < 1`, equal to `Γ_ℂ(1−w)/Γ_ℂ(w)` off
the poles, `G₀(1/2) = 1`, and polynomially bounded on closed vertical strips inside `Re w < 1`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open Complex
open scoped Real

lemma two_pi_ne_zero : (2 * π : ℂ) ≠ 0 := by
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero two_ne_zero this

theorem G0_eq {w : ℂ} (hw : ∀ m : ℕ, w ≠ -m) (hw' : ∀ m : ℕ, 1 - w ≠ -m) :
    Gammaℂ (1 - w) / Gammaℂ w = G0 w := by
  have h1 : Gamma w ≠ 0 := Complex.Gamma_ne_zero hw
  have h2 : Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero hw'
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : Complex.sin (π * w) ≠ 0 := by
    intro h
    rw [h, div_zero] at hrefl
    exact mul_ne_zero h1 h2 hrefl
  have hc : (2 * π : ℂ) ^ (-(1 - w)) = (2 * π : ℂ) ^ (2 * w - 1) * (2 * π : ℂ) ^ (-w) := by
    rw [← cpow_add _ _ two_pi_ne_zero]; ring_nf
  have hpw : (2 * π : ℂ) ^ (-w) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_pi_ne_zero)
  have this : Gamma w * Gamma (1 - w) * Complex.sin (π * w) = π := by
    rw [hrefl]; field_simp
  have hq : Gamma (1 - w) / Gamma w = Gamma (1 - w) ^ 2 * Complex.sin (π * w) / π := by
    rw [div_eq_div_iff h1 hπ]
    linear_combination (-Gamma (1 - w)) * this
  calc Gammaℂ (1 - w) / Gammaℂ w = (2 * π : ℂ) ^ (2 * w - 1) * (Gamma (1 - w) / Gamma w) := by
        rw [Gammaℂ_def, Gammaℂ_def, hc]; field_simp
    _ = G0 w := by rw [hq, G0]; ring

theorem G0_differentiableAt {w : ℂ} (hw : w.re < 1) : DifferentiableAt ℂ G0 w := by
  have hg : DifferentiableAt ℂ (fun w : ℂ => Gamma (1 - w)) w := by
    refine (Complex.differentiableAt_Gamma (1 - w) fun m h => ?_).comp w
      ((differentiableAt_const _).sub differentiableAt_id)
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  unfold G0
  refine DifferentiableAt.div_const ?_ _
  refine ((DifferentiableAt.const_cpow ?_ (Or.inl two_pi_ne_zero)).mul (hg.pow 2)).mul ?_
  · exact ((differentiableAt_const _).mul differentiableAt_id).sub (differentiableAt_const _)
  · exact Complex.differentiable_sin.differentiableAt.comp w
      ((differentiableAt_const _).mul differentiableAt_id)

theorem G0_half : G0 (1 / 2) = 1 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg : Gamma (1 - 1 / 2 : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
    rw [show (1 - 1 / 2 : ℂ) = 1 / 2 by norm_num]; exact Complex.Gamma_one_half_eq
  have hsq : ((π : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = π := by
    rw [← cpow_natCast, ← cpow_mul]
    · norm_num
    · simp [Complex.log_im, Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
      linarith [Real.pi_pos]
    · simp [Complex.log_im, Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
      linarith [Real.pi_pos]
  unfold G0
  rw [hg, hsq, show (2 : ℂ) * (1 / 2) - 1 = 0 by norm_num, cpow_zero,
    show (π : ℂ) * (1 / 2) = (π / 2 : ℂ) by ring, Complex.sin_pi_div_two]
  field_simp

/-- `‖Γ(n + it)‖² ≤ 4πe^π (n(1+|t|))^{2(n−1)} (1+|t|) e^{−π|t|}` for `n ≥ 1`. -/
lemma norm_Gamma_nat_add_sq_le (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖Gamma ((n : ℂ) + t * I)‖ ^ 2 ≤ (n * (1 + |t|)) ^ (2 * (n - 1)) *
      (4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|))) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simpa using L3K.norm_Gamma_one_add_sq_le t
  | succ k hk ih =>
    have hk0 : ((k : ℂ) + t * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; omega
    have hrec : Gamma (((k + 1 : ℕ) : ℂ) + t * I) = ((k : ℂ) + t * I) * Gamma ((k : ℂ) + t * I) := by
      rw [show (((k + 1 : ℕ) : ℂ) + t * I) = ((k : ℂ) + t * I) + 1 by push_cast; ring]
      exact Complex.Gamma_add_one _ hk0
    have hnk : ‖(k : ℂ) + t * I‖ ≤ (k + 1 : ℕ) * (1 + |t|) := by
      refine (norm_add_le _ _).trans ?_
      simp only [Complex.norm_natCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]
      push_cast
      nlinarith [abs_nonneg t]
    have hpos : 0 ≤ 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|)) := by
      have := Real.pi_pos; positivity
    rw [hrec, norm_mul, mul_pow]
    have hmono : (k * (1 + |t|)) ^ (2 * (k - 1)) ≤ ((k + 1 : ℕ) * (1 + |t|)) ^ (2 * (k - 1)) := by
      gcongr; push_cast; linarith
    have hk2 : 2 * (k + 1 - 1) = 2 + 2 * (k - 1) := by omega
    rw [hk2, pow_add]
    calc ‖(k : ℂ) + t * I‖ ^ 2 * ‖Gamma ((k : ℂ) + t * I)‖ ^ 2
        ≤ (((k + 1 : ℕ) : ℝ) * (1 + |t|)) ^ 2 * (((k : ℝ) * (1 + |t|)) ^ (2 * (k - 1)) *
            (4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|)))) := by
          gcongr
      _ ≤ (((k + 1 : ℕ) : ℝ) * (1 + |t|)) ^ 2 * ((((k + 1 : ℕ) : ℝ) * (1 + |t|)) ^ (2 * (k - 1)) *
            (4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|)))) := by
          gcongr
      _ = _ := by ring

/-- `G₀` is polynomially bounded on `a ≤ Re w ≤ b` for `b < 1`. -/
theorem G0_bound (a b : ℝ) (hb : b < 1) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖G0 w‖ ≤ C * (1 + |w.im|) ^ A := by
  set δ : ℝ := 1 - b with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set n : ℕ := ⌈max (1 - a) 1⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by
    rw [hn]; exact (Nat.ceil_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))).ne')
  have hnX : max (1 - a) 1 ≤ n := Nat.le_ceil _
  -- a bound for `Γ(x)` on `[δ, n]`
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := δ) (b := (n : ℝ))).exists_bound_of_continuousOn
    (f := fun x : ℝ => ‖Gamma (x : ℂ)‖) (by
      refine ContinuousOn.norm ?_
      intro x hx
      refine ((Complex.differentiableAt_Gamma (x : ℂ) fun m h => ?_).continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith [hx.1])
  have hGn : 0 < ‖Gamma (n : ℂ)‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero fun m h => by
    have := congrArg Complex.re h; simp at this; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith)
  set K : ℝ := 4 * Real.pi * Real.exp Real.pi with hK
  have hK0 : 0 ≤ K := by have := Real.pi_pos; positivity
  set P : ℝ := (2 * π) ^ (2 * b - 1) with hP
  refine ⟨P * (max B 0 / ‖Gamma (n : ℂ)‖) ^ 2 * (n : ℝ) ^ (2 * (n - 1)) * K / π,
    (2 * (n - 1) + 1 : ℕ), by positivity, by positivity, fun w h1 h2 => ?_⟩
  set t := w.im
  set x := 1 - w.re with hx
  have hx0 : δ ≤ x := by rw [hx, hδ]; linarith
  have hxn : x ≤ n := by rw [hx]; linarith [le_max_left (1 - a) 1]
  have hxpos : 0 < x := lt_of_lt_of_le hδ0 hx0
  have h1w : (1 : ℂ) - w = (x : ℂ) + (-t) * I := by
    apply Complex.ext <;> simp [hx, t]
  -- `‖Γ(1-w)‖ ≤ ‖Γ(n - it)‖ B / Γ(n)`
  have hmono := L3K.norm_Gamma_mono hxpos hxn (-t)
  push_cast at hmono
  have hBx : ‖Gamma (x : ℂ)‖ ≤ max B 0 := by
    have := hB x ⟨hx0, hxn⟩
    rw [norm_norm] at this
    exact this.trans (le_max_left _ _)
  have hg1 : ‖Gamma (1 - w)‖ ≤ ‖Gamma ((n : ℂ) + (-t) * I)‖ * (max B 0 / ‖Gamma (n : ℂ)‖) := by
    rw [h1w, mul_div_assoc', le_div_iff₀ hGn]
    exact hmono.trans (mul_le_mul_of_nonneg_left hBx (norm_nonneg _))
  have hgn := norm_Gamma_nat_add_sq_le n hn1 (-t)
  rw [abs_neg] at hgn
  have hsin : ‖Complex.sin (π * w)‖ ≤ Real.exp (Real.pi * |t|) := by
    refine (L3K.norm_sin_le _).trans ?_
    apply le_of_eq; congr 1
    simp [t, abs_mul, abs_of_pos Real.pi_pos]
  have hcp : ‖(2 * π : ℂ) ^ (2 * w - 1)‖ ≤ P := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    rw [hP]
    apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_gt_three])
    have : (2 * w - 1).re = 2 * w.re - 1 := by simp
    rw [this]; linarith
  have h1t : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  unfold G0
  rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hg2 : ‖Gamma (1 - w)‖ ^ 2 ≤ (max B 0 / ‖Gamma (n : ℂ)‖) ^ 2 *
      ((n * (1 + |t|)) ^ (2 * (n - 1)) * (K * (1 + |t|) * Real.exp (-(Real.pi * |t|)))) := by
    calc ‖Gamma (1 - w)‖ ^ 2 ≤ (‖Gamma ((n : ℂ) + (-t) * I)‖ * (max B 0 / ‖Gamma (n : ℂ)‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hg1 2
      _ = (max B 0 / ‖Gamma (n : ℂ)‖) ^ 2 * ‖Gamma ((n : ℂ) + (-t) * I)‖ ^ 2 := by ring
      _ ≤ _ := by gcongr; simpa [hK, mul_assoc] using hgn
  have hexp : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
    rw [← Real.exp_add]; simp
  have hpow : (1 + |t|) ^ (((2 * (n - 1) + 1 : ℕ) : ℝ)) = (1 + |t|) ^ (2 * (n - 1)) * (1 + |t|) := by
    rw [Real.rpow_natCast, pow_succ]
  rw [hpow]
  have hP0 : 0 ≤ P := by positivity
  calc ‖(2 * π : ℂ) ^ (2 * w - 1)‖ * ‖Gamma (1 - w)‖ ^ 2 * ‖Complex.sin (π * w)‖ / π
      ≤ P * ((max B 0 / ‖Gamma (n : ℂ)‖) ^ 2 *
          ((n * (1 + |t|)) ^ (2 * (n - 1)) * (K * (1 + |t|) * Real.exp (-(Real.pi * |t|))))) *
          Real.exp (Real.pi * |t|) / π := by
        gcongr
    _ = P * (max B 0 / ‖Gamma (n : ℂ)‖) ^ 2 * (n : ℝ) ^ (2 * (n - 1)) * K / π *
          ((1 + |t|) ^ (2 * (n - 1)) * (1 + |t|)) *
          (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) := by
        rw [mul_pow]; ring
    _ = _ := by rw [hexp, mul_one]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_DualA: Dirichlet-series identities for the dual side

`LamHyp`: the entire continuation `Λ = ζ_𝔪 · L_ext(ψ)` with the functional equation and growth
(the content of the cut). Here:
* `tsum_cop_eq`: `∑'_{a ⊔ 𝔤 = ⊤} ψ(a) N a^{-w} = Λ(w) E(w)` on `Re w > 1`;
* `fe_line`: `Λ(w) = D^{1/2−w} G₀(w)^{r₂} Λ(1−w)` off the poles;
* `Lam_eq_split`: `Λ(u) = Zm(u) ζ(2u) ∏_{P ∣ 𝔪c}(1 − NP^{-2u}) (P_{L′}(u) + Q_{L′}(u))` on `Re u > 1`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma two_le_absNorm_of_mem_primesOf {q P : Ideal (𝓞 F)} (hP : P ∈ primesOf q) :
    2 ≤ Ideal.absNorm P := by
  have h1 := one_le_absNorm_of_mem_primesOf hP
  have hne : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact (primesOf_prime hP).1.ne_top
  omega

lemma norm_natCast_cpow_neg_lt_one {n : ℕ} (hn : 2 ≤ n) {u : ℂ} (hu : 0 < u.re) :
    ‖(n : ℂ) ^ (-u)‖ < 1 := by
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : 0 < n))]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by simp; linarith)

lemma prod_one_sub_ne_zero (q : Ideal (𝓞 F)) {u : ℂ} (hu : 0 < u.re) :
    ∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-u)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun P hP h => ?_
  have := norm_natCast_cpow_neg_lt_one (two_le_absNorm_of_mem_primesOf hP) hu
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at this
  exact lt_irrefl _ this

lemma psi_bot_term {ψ : Ideal (𝓞 F) → ℂ} {w : ℂ} (hw : w ≠ 0) :
    ψ ⊥ * (Ideal.absNorm (⊥ : Ideal (𝓞 F)) : ℂ) ^ (-w) = 0 := by
  rw [Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.2 hw), mul_zero]

lemma summable_psi {𝔪 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ) {w : ℂ}
    (hw : 1 < w.re) : Summable fun a : Ideal (𝓞 F) => ‖ψ a * (Ideal.absNorm a : ℂ) ^ (-w)‖ := by
  refine (summable_norm_cpow hw).of_nonneg_of_le (fun _ => norm_nonneg _) fun a => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hψ.norm_le a)

lemma psi_term_mul {𝔪 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ) {w : ℂ}
    (hw : w ≠ 0) (I J : Ideal (𝓞 F)) :
    ψ (I * J) * (Ideal.absNorm (I * J) : ℂ) ^ (-w) =
      (ψ I * (Ideal.absNorm I : ℂ) ^ (-w)) * (ψ J * (Ideal.absNorm J : ℂ) ^ (-w)) := by
  by_cases hI : I = ⊥
  · subst hI; rw [Ideal.bot_mul, psi_bot_term hw, zero_mul]
  by_cases hJ : J = ⊥
  · subst hJ; rw [Ideal.mul_bot, psi_bot_term hw, mul_zero]
  rw [hψ.mul I J hI hJ, cpow_absNorm_mul]; ring

/-- The coprime-to-`𝔤` Dirichlet series: `∑'_{a ⊔ 𝔤 = ⊤} ψ(a) N a^{-w} = Λ(w) E(w)`. -/
theorem tsum_cop_eq {𝔪 𝔤 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} {Λ : ℂ → ℂ}
    (hψ : PsiHyp 𝔪 c ψ) (hΛ : LamHyp 𝔪 c ψ Λ) (h𝔤 : 𝔤 ≠ ⊥) {w : ℂ} (hw : 1 < w.re) :
    ∑' a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ then ψ a * (Ideal.absNorm a : ℂ) ^ (-w) else 0) =
      Λ w * Em 𝔪 𝔤 ψ w := by
  classical
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  have hs := sieve (fun a : Ideal (𝓞 F) => ψ a * (Ideal.absNorm a : ℂ) ^ (-w))
    (psi_term_mul hψ hw0) (summable_psi hψ hw).of_norm (primesOf 𝔤)
    (fun P hP => primesOf_prime hP)
  have hP : ∀ P ∈ primesOf 𝔤, ψ P * (Ideal.absNorm P : ℂ) ^ (-w) = ψ P * (Ideal.absNorm P : ℂ) ^ (-w) :=
    fun _ _ => rfl
  have hlhs : ∑' a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ then ψ a * (Ideal.absNorm a : ℂ) ^ (-w) else 0) =
      ∑' a, ({I | ∀ P ∈ primesOf 𝔤, ¬ I ≤ P} : Set (Ideal (𝓞 F))).indicator
        (fun a : Ideal (𝓞 F) => ψ a * (Ideal.absNorm a : ℂ) ^ (-w)) a := by
    congr 1; funext a
    by_cases ha : a ⊔ 𝔤 = ⊤
    · rw [if_pos ha, Set.indicator_of_mem]
      exact (sup_eq_top_iff_forall h𝔤).1 ha
    · rw [if_neg ha, Set.indicator_of_notMem]
      exact fun h' => ha ((sup_eq_top_iff_forall h𝔤).2 h')
  rw [hlhs, ← hs, hΛ.dir w hw, Em]
  have hne := prod_one_sub_ne_zero 𝔪 (u := w) (by linarith)
  field_simp

/-- The functional equation in the form `Λ(w) = D^{1/2−w} G₀(w)^{r₂} Λ(1−w)`. -/
theorem fe_line {𝔪 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} {Λ : ℂ → ℂ}
    (hΛ : LamHyp 𝔪 c ψ Λ) (hD : Dc c ≠ 0) {w : ℂ} (hw : ∀ m : ℕ, w ≠ -(m : ℂ))
    (hw' : ∀ m : ℕ, 1 - w ≠ -(m : ℂ)) :
    Λ w = Dc c ^ (1 / 2 - w) * G0 w ^ InfinitePlace.nrComplexPlaces F * Λ (1 - w) := by
  have hfe := hΛ.fe w hw hw'
  have hg : Gammaℂ w ≠ 0 := by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero hw)
    exact cpow_ne_zero_iff.mpr (Or.inl two_pi_ne_zero)
  have hd : Dc c ^ (w / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hD)
  have hpow : Dc c ^ ((1 - w) / 2) = Dc c ^ (1 / 2 - w) * Dc c ^ (w / 2) := by
    rw [← cpow_add _ _ hD]; ring_nf
  rw [← G0_eq hw hw', div_pow]
  have hgr : Gammaℂ w ^ InfinitePlace.nrComplexPlaces F ≠ 0 := pow_ne_zero _ hg
  rw [hpow] at hfe
  generalize Dc c ^ (1 / 2 - w) = A at hfe ⊢
  generalize Dc c ^ (w / 2) = B at hfe hd ⊢
  generalize Gammaℂ w ^ InfinitePlace.nrComplexPlaces F = G at hfe hgr ⊢
  generalize Gammaℂ (1 - w) ^ InfinitePlace.nrComplexPlaces F = G1 at hfe ⊢
  rw [mul_div_assoc', div_mul_eq_mul_div, eq_div_iff hgr]
  apply mul_left_cancel₀ hd
  linear_combination hfe

/-- `∑'_a ψ(a) N a^{-u} = (∑'_{s sqfree} ψ(s) N s^{-u}) ζ(2u) ∏_{P ∣ 𝔪c}(1 − NP^{-2u})`. -/
theorem tsum_psi_sqdec {𝔪 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ)
    (h𝔪c : 𝔪 * c ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤) {u : ℂ} (hu : 1 < u.re) :
    ∑' a : Ideal (𝓞 F), ψ a * (Ideal.absNorm a : ℂ) ^ (-u) =
      (∑' s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s},
          ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u)) *
        (dedekindZeta F (2 * u) *
          ∏ P ∈ primesOf (𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * u)))) := by
  classical
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu; linarith
  have hu2 : 1 < (2 * u).re := by simp; linarith
  rw [← tsum_sqdec _ (psi_bot_term hu0)]
  have hterm : ∀ p : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} × {r : Ideal (𝓞 F) // r ≠ ⊥},
      ψ (p.1.1 * p.2.1 ^ 2) * (Ideal.absNorm (p.1.1 * p.2.1 ^ 2) : ℂ) ^ (-u) =
        (ψ p.1.1 * (Ideal.absNorm p.1.1 : ℂ) ^ (-u)) *
          (ψ p.2.1 ^ 2 * (Ideal.absNorm p.2.1 : ℂ) ^ (-(2 * u))) := by
    rintro ⟨⟨s, hs, -⟩, ⟨r, hr⟩⟩
    rw [psi_term_mul hψ hu0, pow_two r, psi_term_mul hψ hu0]
    simp only
    have hN : (Ideal.absNorm r : ℂ) ≠ 0 := by
      have := absNorm_pos hr; exact_mod_cast this.ne'
    rw [show (Ideal.absNorm r : ℂ) ^ (-(2 * u)) =
      (Ideal.absNorm r : ℂ) ^ (-u) * (Ideal.absNorm r : ℂ) ^ (-u) by
        rw [← cpow_add _ _ hN]; ring_nf]
    ring
  simp_rw [hterm]
  have hs1 : Summable fun s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} =>
      ‖ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u)‖ := (summable_psi hψ hu).subtype _
  have hs2 : Summable fun r : {r : Ideal (𝓞 F) // r ≠ ⊥} =>
      ‖ψ r.1 ^ 2 * (Ideal.absNorm r.1 : ℂ) ^ (-(2 * u))‖ := by
    refine ((summable_norm_cpow hu2).subtype _).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun r => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hψ.norm_le _))
  rw [← tsum_mul_tsum_of_summable_norm hs1 hs2]
  congr 1
  rw [← zeta_cop h𝔪c hu2]
  have hsupp : Function.support (fun r : Ideal (𝓞 F) =>
      if r ⊔ 𝔪 * c = ⊤ then (Ideal.absNorm r : ℂ) ^ (-(2 * u)) else 0) ⊆ {r | r ≠ ⊥} := by
    refine Function.support_subset_iff.2 fun r hr0 => ?_
    rintro rfl
    apply hr0
    have : ¬ (⊥ : Ideal (𝓞 F)) ⊔ 𝔪 * c = ⊤ := by
      rw [bot_sup_eq]; intro h; apply h𝔪t
      exact top_le_iff.1 (h ▸ Ideal.le_of_dvd (dvd_mul_right 𝔪 c))
    simp only [this, if_false]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun r => ?_
  have hr : r.1 ≠ ⊥ := r.2
  rw [psi_sq_eq hψ hr]
  have e : r.1 ⊔ 𝔪 * c = ⊤ ↔ r.1 ⊔ 𝔪 = ⊤ ∧ r.1 ⊔ c = ⊤ := by
    rw [sup_comm, sup_mul_eq_top_iff, sup_comm 𝔪, sup_comm c]
  by_cases h : r.1 ⊔ 𝔪 = ⊤ ∧ r.1 ⊔ c = ⊤
  · rw [if_pos h, if_pos (e.2 h), one_mul]
  · rw [if_neg h, if_neg (fun h' => h (e.1 h')), zero_mul]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_DualB: kernels and bounds for the dual side

`Kd(w) = M^w E(w) D^{1/2−w} G₀(w)^{r₂} ζ_𝔪(1−w) ∏_{P ∣ 𝔪c}(1 − NP^{-2(1−w)})`, the finite
Dirichlet polynomial `Pf` and the tail `Qf`; holomorphy and polynomial bounds on strips.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-! ### Polynomial bounds -/

/-- `f` is polynomially bounded on the strip `a ≤ Re w ≤ b`. -/
def PolyB (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖f w‖ ≤ C * (1 + |w.im|) ^ A

lemma PolyB.mul {f g : ℂ → ℂ} {a b : ℝ} (hf : PolyB f a b) (hg : PolyB g a b) :
    PolyB (fun w => f w * g w) a b := by
  obtain ⟨C₁, A₁, hC₁, hA₁, h₁⟩ := hf
  obtain ⟨C₂, A₂, hC₂, hA₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, A₁ + A₂, by positivity, by positivity, fun w h1 h2 => ?_⟩
  rw [norm_mul, Real.rpow_add (by positivity)]
  calc ‖f w‖ * ‖g w‖ ≤ (C₁ * (1 + |w.im|) ^ A₁) * (C₂ * (1 + |w.im|) ^ A₂) :=
        mul_le_mul (h₁ w h1 h2) (h₂ w h1 h2) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma PolyB.const_bound {f : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C)
    (h : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖f w‖ ≤ C) : PolyB f a b :=
  ⟨C, 0, hC, le_rfl, fun w h1 h2 => by simpa using h w h1 h2⟩

lemma PolyB.comp_affine {f : ℂ → ℂ} {a b : ℝ} (hf : PolyB f a b) (α β : ℝ) (hα : α ≠ 0)
    {a' b' : ℝ} (hs : ∀ w : ℂ, a' ≤ w.re → w.re ≤ b' → a ≤ (α * w + β).re ∧ (α * w + β).re ≤ b) :
    PolyB (fun w => f (α * w + β)) a' b' := by
  obtain ⟨C, A, hC, hA, h⟩ := hf
  refine ⟨C * (1 + |α|) ^ A, A, by positivity, hA, fun w h1 h2 => ?_⟩
  obtain ⟨e1, e2⟩ := hs w h1 h2
  have hb := h _ e1 e2
  have him : |(α * w + β : ℂ).im| = |α| * |w.im| := by simp [abs_mul]
  rw [him] at hb
  have : (1 + |α| * |w.im|) ^ A ≤ ((1 + |α|) * (1 + |w.im|)) ^ A :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg α, abs_nonneg w.im]) hA
  rw [Real.mul_rpow (by positivity) (by positivity)] at this
  calc ‖f (α * w + β)‖ ≤ C * (1 + |α| * |w.im|) ^ A := hb
    _ ≤ C * ((1 + |α|) ^ A * (1 + |w.im|) ^ A) := by gcongr
    _ = _ := by ring

lemma PolyB_cpow_const {X : ℝ} (hX : 0 < X) (a b : ℝ) (β : ℂ) (κ : ℝ) :
    PolyB (fun w => (X : ℂ) ^ (β + κ * w)) a b := by
  set K := |κ| * (|a| + |b|)
  refine PolyB.const_bound (C := X ^ (β.re + K) + X ^ (β.re - K))
    (by positivity) fun w h1 h2 => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  have hre : |(β + κ * w).re - β.re| ≤ K := by
    have : (β + κ * w).re - β.re = κ * w.re := by simp
    rw [this, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg κ)
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
  rw [abs_le] at hre
  rcases le_or_gt 1 X with hX1 | hX1
  · have : X ^ (β + κ * w).re ≤ X ^ (β.re + K) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    linarith [Real.rpow_nonneg hX.le (β.re - K)]
  · have : X ^ (β + κ * w).re ≤ X ^ (β.re - K) :=
      Real.rpow_le_rpow_of_exponent_ge hX hX1.le (by linarith)
    linarith [Real.rpow_nonneg hX.le (β.re + K)]

lemma PolyB.pow {f : ℂ → ℂ} {a b : ℝ} (hf : PolyB f a b) (n : ℕ) :
    PolyB (fun w => f w ^ n) a b := by
  induction n with
  | zero => exact PolyB.const_bound zero_le_one fun w _ _ => by simp
  | succ n ih => simpa [pow_succ] using ih.mul hf

lemma PolyB.add {f g : ℂ → ℂ} {a b : ℝ} (hf : PolyB f a b) (hg : PolyB g a b) :
    PolyB (fun w => f w + g w) a b := by
  obtain ⟨C₁, A₁, hC₁, hA₁, h₁⟩ := hf
  obtain ⟨C₂, A₂, hC₂, hA₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max A₁ A₂, by positivity, le_max_of_le_left hA₁, fun w h1 h2 => ?_⟩
  have ht : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
  have e1 : (1 + |w.im|) ^ A₁ ≤ (1 + |w.im|) ^ max A₁ A₂ :=
    Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _)
  have e2 : (1 + |w.im|) ^ A₂ ≤ (1 + |w.im|) ^ max A₁ A₂ :=
    Real.rpow_le_rpow_of_exponent_le ht (le_max_right _ _)
  calc ‖f w + g w‖ ≤ ‖f w‖ + ‖g w‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + |w.im|) ^ A₁ + C₂ * (1 + |w.im|) ^ A₂ := add_le_add (h₁ w h1 h2) (h₂ w h1 h2)
    _ ≤ C₁ * (1 + |w.im|) ^ max A₁ A₂ + C₂ * (1 + |w.im|) ^ max A₁ A₂ := by gcongr
    _ = _ := by ring

lemma PolyB.finset_sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} {a b : ℝ}
    (hf : ∀ i ∈ S, PolyB (f i) a b) : PolyB (fun w => ∑ i ∈ S, f i w) a b := by
  classical
  induction S using Finset.induction_on with
  | empty => exact PolyB.const_bound le_rfl fun w _ _ => by simp
  | insert i S hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma PolyB.finset_prod {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} {a b : ℝ}
    (hf : ∀ i ∈ S, PolyB (f i) a b) : PolyB (fun w => ∏ i ∈ S, f i w) a b := by
  classical
  induction S using Finset.induction_on with
  | empty => exact PolyB.const_bound zero_le_one fun w _ _ => by simp
  | insert i S hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma PolyB_natCast_cpow {n : ℕ} (hn : 1 ≤ n) (a b : ℝ) (β : ℂ) (κ : ℝ) :
    PolyB (fun w => (n : ℂ) ^ (β + κ * w)) a b := by
  have := PolyB_cpow_const (X := (n : ℝ)) (by exact_mod_cast hn) a b β κ
  simpa using this

lemma PolyB.congr {f g : ℂ → ℂ} {a b : ℝ} (hg : PolyB g a b)
    (h : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → f w = g w) : PolyB f a b := by
  obtain ⟨C, A, hC, hA, hb⟩ := hg
  exact ⟨C, A, hC, hA, fun w h1 h2 => by rw [h w h1 h2]; exact hb w h1 h2⟩

lemma PolyB_one_sub {c : ℂ} (hc : ‖c‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) (a b : ℝ) (β : ℂ) (κ : ℝ) :
    PolyB (fun w => 1 - c * (n : ℂ) ^ (β + κ * w)) a b := by
  have h := (PolyB.const_bound (f := fun _ => -c) (a := a) (b := b) (norm_nonneg c)
    fun _ _ _ => by rw [norm_neg]).mul (PolyB_natCast_cpow hn a b β κ)
  have h1 := PolyB.const_bound (f := fun _ : ℂ => (1 : ℂ)) (a := a) (b := b) zero_le_one
    fun _ _ _ => by simp
  exact (h1.add h).congr fun w _ _ => by ring

/-! ### The dual kernels -/

/-! ### Bounds and holomorphy of the kernels -/

lemma Dc_eq {c : Ideal (𝓞 F)} : Dc c = (((|discr F| : ℤ) * (Ideal.absNorm c : ℝ) : ℝ) : ℂ) := by
  simp only [Dc, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]

lemma Dc_pos {c : Ideal (𝓞 F)} (hc : c ≠ ⊥) : (0 : ℝ) < (|discr F| : ℤ) * (Ideal.absNorm c : ℝ) := by
  have h1 : (0 : ℝ) < ((|discr F| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero F
    exact_mod_cast abs_pos.2 this
  exact mul_pos h1 (absNorm_pos hc)

lemma Dc_ne_zero {c : Ideal (𝓞 F)} (hc : c ≠ ⊥) : Dc c ≠ 0 := by
  rw [Dc_eq]; exact_mod_cast (Dc_pos hc).ne'

lemma PolyB_Em (𝔪 𝔤 : Ideal (𝓞 F)) {ψ : Ideal (𝓞 F) → ℂ} (hψ : ∀ I, ‖ψ I‖ ≤ 1) (a b : ℝ) :
    PolyB (Em 𝔪 𝔤 ψ) a b := by
  refine (((PolyB.finset_prod (primesOf 𝔪) fun P hP =>
    PolyB_one_sub (c := 1) (by simp) (one_le_absNorm_of_mem_primesOf hP) a b 0 (-1))).mul
    (PolyB.finset_prod (primesOf 𝔤) fun P hP =>
    PolyB_one_sub (hψ P) (one_le_absNorm_of_mem_primesOf hP) a b 0 (-1))).congr fun w _ _ => ?_
  unfold Em
  congr 1
  · refine Finset.prod_congr rfl fun P _ => ?_; push_cast; ring_nf
  · refine Finset.prod_congr rfl fun P _ => ?_; push_cast; ring_nf

lemma PolyB_Dpow {c : Ideal (𝓞 F)} (hc : c ≠ ⊥) (a b : ℝ) :
    PolyB (fun w => Dc c ^ (1 / 2 - w)) a b := by
  refine (PolyB_cpow_const (Dc_pos hc) a b (1 / 2) (-1)).congr fun w _ _ => ?_
  rw [Dc_eq]; push_cast; ring_nf

lemma PolyB_G0pow (a b : ℝ) (hb : b < 1) (n : ℕ) : PolyB (fun w => G0 w ^ n) a b := by
  obtain ⟨C, A, hC, hA, h⟩ := G0_bound a b hb
  exact PolyB.pow ⟨C, A, hC, hA, h⟩ n

lemma norm_prod_one_sub_ge (q : Ideal (𝓞 F)) {δ : ℝ} (hδ : 0 < δ) {u : ℂ} (hu : δ ≤ u.re) :
    (1 - (2 : ℝ) ^ (-δ)) ^ (primesOf q).card ≤
      ‖∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-u))‖ := by
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => ?_) fun P hP => ?_
  · have : (2 : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  · have hN := two_le_absNorm_of_mem_primesOf hP
    have h1 : ‖(Ideal.absNorm P : ℂ) ^ (-u)‖ ≤ (2 : ℝ) ^ (-δ) := by
      rw [show ((Ideal.absNorm P : ℂ)) = ((Ideal.absNorm P : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : 0 < Ideal.absNorm P))]
      calc (Ideal.absNorm P : ℝ) ^ (-u).re ≤ (Ideal.absNorm P : ℝ) ^ (-δ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ Ideal.absNorm P))
              (by simp; linarith)
        _ ≤ (2 : ℝ) ^ (-δ) := by
            apply Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hN) (by linarith)
    have := norm_sub_norm_le (1 : ℂ) ((Ideal.absNorm P : ℂ) ^ (-u))
    rw [norm_one] at this
    linarith

lemma norm_Zm_le (𝔪 : Ideal (𝓞 F)) {δ : ℝ} (hδ : 0 < δ) {u : ℂ} (hu : δ ≤ u.re) :
    ‖Zm 𝔪 u‖ ≤ ((1 - (2 : ℝ) ^ (-δ)) ^ (primesOf 𝔪).card)⁻¹ := by
  have hpos : 0 < (1 - (2 : ℝ) ^ (-δ)) ^ (primesOf 𝔪).card := by
    have : (2 : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact pow_pos (by linarith) _
  rw [Zm, norm_inv]
  exact inv_anti₀ hpos (norm_prod_one_sub_ge 𝔪 hδ hu)

lemma PolyB_Zm (𝔪 : Ideal (𝓞 F)) (a b : ℝ) (hb : b < 1) :
    PolyB (fun w => Zm 𝔪 (1 - w)) a b := by
  have hδ : 0 < 1 - b := by linarith
  have h2 : (2 : ℝ) ^ (-(1 - b)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine PolyB.const_bound (inv_nonneg.2 (pow_nonneg (by linarith) _)) fun w h1 h2 =>
    norm_Zm_le 𝔪 hδ (by simp; linarith)

lemma PolyB_prod2 (q : Ideal (𝓞 F)) (a b : ℝ) (hb : b ≤ 1) :
    PolyB (fun w => ∏ P ∈ primesOf q, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * (1 - w))))) a b :=
  PolyB.const_bound (by positivity) fun w h1 h2 =>
    norm_prod_one_sub_le q (by simp; linarith)

lemma PolyB_Mpow {M : ℝ} (hM : 0 < M) (a b : ℝ) : PolyB (fun w => (M : ℂ) ^ w) a b :=
  (PolyB_cpow_const hM a b 0 1).congr fun w _ _ => by simp

lemma PolyB_Kd (𝔪 𝔤 : Ideal (𝓞 F)) {c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ}
    (hψ : ∀ I, ‖ψ I‖ ≤ 1) (hc : c ≠ ⊥) {M : ℝ} (hM : 0 < M) (a b : ℝ) (hb : b < 1) :
    PolyB (Kd 𝔪 𝔤 c ψ M) a b :=
  ((((((PolyB_Mpow hM a b).mul (PolyB_Em 𝔪 𝔤 hψ a b)).mul (PolyB_Dpow hc a b)).mul
    (PolyB_G0pow a b hb _)).mul (PolyB_Zm 𝔪 a b hb)).mul (PolyB_prod2 (𝔪 * c) a b hb.le)).congr
    fun w _ _ => rfl

lemma PolyB_R0 (a b : ℝ) (ha : -1 / 2 ≤ 2 * (1 - b)) :
    PolyB (fun w => R0 F (2 * (1 - w))) a b := by
  obtain ⟨C, A, hC, hA, h⟩ := R0_bound F (2 * (1 - a) + 1)
  refine (PolyB.comp_affine (f := R0 F) ⟨C, A, hC, hA, h⟩ (-2) 2 (by norm_num)
    (a' := a) (b' := b) fun w h1 h2 => ⟨by simp; linarith, by simp; linarith⟩).congr
    fun w _ _ => by push_cast; ring_nf

lemma Pf_def (𝔪 : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (L' : ℝ) (u : ℂ) :
    Pf 𝔪 ψ L' u = ∑ s ∈ L3H.rowsF 𝔪 0 L', ψ s * (Ideal.absNorm s : ℂ) ^ (-u) := by
  rw [Pf, sqfRows_eq]

lemma PolyB_Pf (𝔪 : Ideal (𝓞 F)) {ψ : Ideal (𝓞 F) → ℂ} (hψ : ∀ I, ‖ψ I‖ ≤ 1) (L' : ℝ)
    (a b : ℝ) (hb : b ≤ 1) : PolyB (fun w => Pf 𝔪 ψ L' (1 - w)) a b := by
  refine PolyB.finset_sum _ fun s hs => PolyB.const_bound zero_le_one fun w h1 h2 => ?_
  rw [norm_mul]
  have hs1 : 1 ≤ Ideal.absNorm s := by
    have := (mem_sqfRows.1 hs).1.1
    exact Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact this)
  exact mul_le_one₀ (hψ s) (norm_nonneg _)
    (norm_natCast_cpow_neg_le_one hs1 (by simp; linarith))

/-! ### Holomorphy -/

lemma differentiable_one_sub_cpow {c : ℂ} {n : ℕ} (hn : 1 ≤ n) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ fun w => 1 - c * (n : ℂ) ^ (f w) := by
  have hN : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  intro w
  exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
    ((hf w).const_cpow (Or.inl hN)))

lemma differentiable_Em (𝔪 𝔤 : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) :
    Differentiable ℂ (Em 𝔪 𝔤 ψ) := by
  intro w
  unfold Em
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.fun_finsetProd fun P hP => ?_
    have := differentiable_one_sub_cpow (c := 1) (one_le_absNorm_of_mem_primesOf hP)
      (differentiable_id.neg) w
    simpa using this
  · refine DifferentiableAt.fun_finsetProd fun P hP => ?_
    exact differentiable_one_sub_cpow (c := ψ P) (one_le_absNorm_of_mem_primesOf hP)
      (differentiable_id.neg) w

lemma differentiableOn_Kd (𝔪 𝔤 : Ideal (𝓞 F)) {c : Ideal (𝓞 F)} (ψ : Ideal (𝓞 F) → ℂ)
    (hc : c ≠ ⊥) {M : ℝ} (hM : 0 < M) {a b : ℝ} (hb : b < 1) :
    DifferentiableOn ℂ (Kd 𝔪 𝔤 c ψ M) {s | a ≤ s.re ∧ s.re ≤ b} := by
  intro w hw
  have hwb : w.re < 1 := lt_of_le_of_lt hw.2 hb
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Kd
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
    (DifferentiableAt.mul ?_ (differentiable_Em 𝔪 𝔤 ψ w)) ?_) ?_) ?_) ?_
  · exact differentiableAt_id.const_cpow (Or.inl hM')
  · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl (Dc_ne_zero hc))
  · exact (G0_differentiableAt hwb).pow _
  · unfold Zm
    refine DifferentiableAt.inv ?_ (prod_one_sub_ne_zero 𝔪 (by simp; linarith))
    refine DifferentiableAt.fun_finsetProd fun P hP => ?_
    have := differentiable_one_sub_cpow (c := 1) (one_le_absNorm_of_mem_primesOf hP)
      (f := fun w => -(1 - w)) (by fun_prop) w
    simpa using this
  · refine DifferentiableAt.fun_finsetProd fun P hP => ?_
    have := differentiable_one_sub_cpow (c := 1) (one_le_absNorm_of_mem_primesOf hP)
      (f := fun w => -(2 * (1 - w))) (by fun_prop) w
    simpa using this

lemma differentiable_Pf (𝔪 : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (L' : ℝ) :
    Differentiable ℂ fun w => Pf 𝔪 ψ L' (1 - w) := by
  intro w
  unfold Pf
  refine DifferentiableAt.fun_sum fun s hs => ?_
  have hs1 : (Ideal.absNorm s : ℂ) ≠ 0 := by
    have := (mem_sqfRows.1 hs).1.1
    have h0 : Ideal.absNorm s ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact this
    exact_mod_cast h0
  exact (differentiableAt_const _).mul
    ((((differentiableAt_const _).sub differentiableAt_id).neg).const_cpow (Or.inl hs1))

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_DualC: the full sum via the functional equation (GL's `T` plus `DP` and `DQ`)

`∑_{a ⊔ 𝔤 = ⊤} W(Na/M) ψ(a) = T + (2π)⁻¹ ∫_{(1−ε′)} Wm Kd R0(2(1−w))/(1−2w) P_{L′}(1−w)
  + (2π)⁻¹ ∫_{(−σ₁)} Wm Kd ζ(2(1−w)) Q_{L′}(1−w)`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-- GL's dual main term `T`. -/
noncomputable def Tdual (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M L' : ℝ) : ℂ :=
  R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2) *
    (∏ P ∈ primesOf (𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) *
    (∏ P ∈ primesOf 𝔤, (1 - ψ P * (Ideal.absNorm P : ℂ) ^ (-(1 / 2 : ℂ)))) * Pf 𝔪 ψ L' (1 / 2)

lemma integrable_Wm_mul {h : ℂ → ℂ} {a b σ : ℝ} (hh : PolyB h a b) (h1 : a ≤ σ) (h2 : σ ≤ b)
    (hc : Continuous fun t : ℝ => h (σ + t * I)) :
    Integrable fun t : ℝ => Wm (σ + t * I) * h (σ + t * I) := by
  obtain ⟨C₀, A, hC₀, hA, hb⟩ := hh
  obtain ⟨C, hC, hmaj⟩ := Wm_mul_maj a b A C₀ hA
  refine Integrable.mono' (integrable_one_add_abs_rpow_neg_two.const_mul C)
    ((differentiable_Wm.continuous.comp (by fun_prop)).mul hc).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have him : ((σ : ℂ) + t * I).im = t := by simp
  have := hmaj (σ + t * I) (by rw [hre]; exact h1) (by rw [hre]; exact h2) _
    (hb _ (by rw [hre]; exact h1) (by rw [hre]; exact h2))
  rwa [him] at this

lemma split_sf {𝔪 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ) (L' : ℝ) {u : ℂ}
    (hu : 1 < u.re) :
    ∑' s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s}, ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) =
      Pf 𝔪 ψ L' u + Qf ψ L' u := by
  classical
  rw [Pf_def]
  have hs : Summable fun s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} =>
      ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) := ((summable_psi hψ hu).subtype _).of_norm
  have hs1 : Summable fun s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} =>
      if (Ideal.absNorm s.1 : ℝ) ≤ L' then ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) else 0 := by
    refine (((summable_psi hψ hu).subtype _)).of_norm_bounded fun s => ?_
    split_ifs <;> simp [norm_mul]; positivity
  have hs2 : Summable fun s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s} =>
      if L' < (Ideal.absNorm s.1 : ℝ) then ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) else 0 := by
    refine (((summable_psi hψ hu).subtype _)).of_norm_bounded fun s => ?_
    split_ifs <;> simp [norm_mul]; positivity
  have hsplit : ∀ s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s},
      ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) =
        (if (Ideal.absNorm s.1 : ℝ) ≤ L' then ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) else 0) +
        (if L' < (Ideal.absNorm s.1 : ℝ) then ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) else 0) := by
    intro s
    by_cases h : (Ideal.absNorm s.1 : ℝ) ≤ L'
    · rw [if_pos h, if_neg (not_lt.2 h), add_zero]
    · rw [if_neg h, if_pos (not_le.1 h), zero_add]
  rw [tsum_congr hsplit, hs1.tsum_add hs2, Qf]
  congr 1
  refine tsum_subtype_of_zero' (fun s => s ≠ ⊥ ∧ Squarefree s) (L3H.rowsF 𝔪 0 L')
    (fun s hs => ⟨(L3H.mem_rowsF_zero.1 hs).1.1, (L3H.mem_rowsF_zero.1 hs).2.1⟩)
    (fun s => if (Ideal.absNorm s : ℝ) ≤ L' then ψ s * (Ideal.absNorm s : ℂ) ^ (-u) else 0) ?_ |>.trans ?_
  · intro s hs hsR
    split_ifs with h
    · have hext : s ⊔ 𝔪 ≠ ⊤ := fun he =>
        hsR (L3H.mem_rowsF_zero.2 ⟨⟨hs.1, he⟩, hs.2, h⟩)
      rw [hψ.nonext s hs.1 hext, zero_mul]
    · rfl
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [if_pos (L3H.mem_rowsF_zero.1 hs).2.2]

lemma PolyB_Lam {𝔪 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} {Λ : ℂ → ℂ} (hΛ : LamHyp 𝔪 c ψ Λ)
    (a b : ℝ) : PolyB Λ a b := by
  obtain ⟨C, A, h⟩ := hΛ.growth a b
  refine ⟨max C 0, max A 0, le_max_right _ _, le_max_right _ _, fun w h1 h2 => ?_⟩
  have ht : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
  calc ‖Λ w‖ ≤ C * (1 + |w.im|) ^ A := h w h1 h2
    _ ≤ max C 0 * (1 + |w.im|) ^ max A 0 := by
        apply mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _))
          (by positivity) (le_max_right _ _)

lemma cpow_div' {N : ℝ} (hN : 0 ≤ N) {D : ℝ} (hD : 0 < D) (s : ℂ) :
    (((N / D : ℝ)) : ℂ) ^ (-s) = (N : ℂ) ^ (-s) * (D : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hN (inv_nonneg.2 hD.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hD.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg (D : ℂ) s, inv_inv]

/-- The full sum by the functional equation. -/
theorem Aall_eq {𝔪 𝔤 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} {Λ : ℂ → ℂ}
    (hψ : PsiHyp 𝔪 c ψ) (hΛ : LamHyp 𝔪 c ψ Λ) (h𝔤 : 𝔤 ≠ ⊥) (h𝔪c : 𝔪 * c ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤)
    (hc : c ≠ ⊥) {M : ℝ} (hM : 0 < M) {σ₁ : ℝ} (hσ₁ : 0 < σ₁) (hσint : ∀ m : ℕ, σ₁ ≠ m)
    {ε' : ℝ} (hε' : 0 < ε') (hε'2 : ε' < 1 / 2) (L' : ℝ) :
    ∑' a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ then (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0) =
      Tdual 𝔪 𝔤 c ψ M L' +
      (1 / (2 * π) : ℂ) * (∫ t : ℝ, Wm (((1 - ε' : ℝ) : ℂ) + t * I) *
        HP 𝔪 𝔤 c ψ M L' (((1 - ε' : ℝ) : ℂ) + t * I)) +
      (1 / (2 * π) : ℂ) * (∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) *
        HQ 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I)) := by
  classical
  -- the integrand on `Re w = 2` and its continuation
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, h = fun w => (M : ℂ) ^ w * (Λ w * Em 𝔪 𝔤 ψ w) := ⟨_, rfl⟩
  -- (A) Mellin inversion
  set ι := {a : Ideal (𝓞 F) // a ≠ ⊥}
  have hx : ∀ a : ι, 0 < (Ideal.absNorm a.1 : ℝ) / M := fun a => div_pos (absNorm_pos a.2) hM
  set bb : ι → ℂ := fun a => if a.1 ⊔ 𝔤 = ⊤ then ψ a.1 else 0 with hbb
  have hsum : Summable fun a : ι => ‖bb a‖ * ((Ideal.absNorm a.1 : ℝ) / M) ^ (-(2 : ℝ)) := by
    have h2 := (summable_absNorm_rpow (F := F) (σ := 2) (by norm_num)).subtype
      {a : Ideal (𝓞 F) | a ≠ ⊥}
    refine (h2.mul_left (M ^ (2 : ℝ))).of_nonneg_of_le (fun _ => by positivity) fun a => ?_
    have hN := absNorm_pos a.2
    rw [Real.div_rpow hN.le hM.le, Real.rpow_neg hM.le, div_inv_eq_mul]
    have hb1 : ‖bb a‖ ≤ 1 := by
      simp only [hbb]; split_ifs
      · exact hψ.norm_le _
      · simp
    have : (Ideal.absNorm a.1 : ℝ) ^ (-(2 : ℝ)) * M ^ (2 : ℝ) =
        M ^ (2 : ℝ) * ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hb1
  have hL : ∑' a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ then (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a
      else 0) = ∑' a : ι, bb a * (W ((Ideal.absNorm a.1 : ℝ) / M) : ℂ) := by
    have hsupp : Function.support (fun a : Ideal (𝓞 F) => if a ⊔ 𝔤 = ⊤ then
        (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0) ⊆ {a | a ≠ ⊥} := by
      refine Function.support_subset_iff.2 fun a ha => ?_
      rintro rfl
      apply ha
      simp [W_zero]
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    refine tsum_congr fun a => ?_
    simp only [hbb]
    split_ifs <;> ring
  rw [hL, tsum_W_eq bb (fun a => (Ideal.absNorm a.1 : ℝ) / M) hx 2 hsum]
  have hin : ∀ t : ℝ, ∑' a : ι, bb a * ((((Ideal.absNorm a.1 : ℝ) / M : ℝ)) : ℂ) ^
      (-(((2 : ℝ) : ℂ) + t * I)) = h (((2 : ℝ) : ℂ) + t * I) := by
    intro t
    have hre : 1 < (((2 : ℝ) : ℂ) + t * I).re := by norm_num
    rw [hh]
    dsimp only
    rw [← tsum_cop_eq hψ hΛ h𝔤 hre, ← tsum_mul_left]
    have hsupp : Function.support (fun a : Ideal (𝓞 F) => (M : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) *
        (if a ⊔ 𝔤 = ⊤ then ψ a * (Ideal.absNorm a : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) else 0)) ⊆
        {a | a ≠ ⊥} := by
      refine Function.support_subset_iff.2 fun a ha => ?_
      rintro rfl
      apply ha
      have h0 : (((2 : ℝ) : ℂ) + t * I) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this
      split_ifs
      · rw [psi_bot_term h0, mul_zero]
      · rw [mul_zero]
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    refine tsum_congr fun a => ?_
    simp only [hbb]
    rw [cpow_div' (by positivity) hM]
    split_ifs <;> push_cast <;> ring
  simp_rw [hin]
  -- (B) shift to `Re w = -σ₁`
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hhd : Differentiable ℂ h := by
    rw [hh]
    exact (differentiable_id.const_cpow (Or.inl hMne)).mul (hΛ.diff.mul (differentiable_Em 𝔪 𝔤 ψ))
  have hhP : PolyB h (-σ₁) 2 :=
    ((PolyB_Mpow hM (-σ₁) 2).mul ((PolyB_Lam hΛ (-σ₁) 2).mul
      (PolyB_Em 𝔪 𝔤 hψ.norm_le (-σ₁) 2))).congr fun w _ _ => by rw [hh]
  obtain ⟨Ch, Ah, hCh, hAh, hhb⟩ := hhP
  have hshift := shift_hol (h := h) (a := -σ₁) (b := 2) (by linarith) hAh
    hhd.differentiableOn hhb
  rw [← hshift]
  -- (C) the integrand on `Re w = -σ₁`
  have hD := Dc_ne_zero hc
  have hline : ∀ t : ℝ, h (((-σ₁ : ℝ) : ℂ) + t * I) =
      HP 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I) + HQ 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I) := by
    intro t
    set w : ℂ := ((-σ₁ : ℝ) : ℂ) + t * I with hw
    have hwre : w.re = -σ₁ := by simp [hw]
    have hw1 : ∀ m : ℕ, w ≠ -(m : ℂ) := by
      intro m h'
      have := congrArg Complex.re h'
      rw [hwre] at this; simp at this
      exact hσint m (by linarith)
    have hw2 : ∀ m : ℕ, 1 - w ≠ -(m : ℂ) := by
      intro m h'
      have := congrArg Complex.re h'
      simp [hwre] at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hu : 1 < (1 - w).re := by simp [hwre]; linarith
    have hu2 : 1 < (2 * (1 - w)).re := by simp [hwre]; linarith
    have hfe := fe_line hΛ hD hw1 hw2
    have hdir := hΛ.dir (1 - w) hu
    have hsq := tsum_psi_sqdec hψ h𝔪c h𝔪t hu
    have hsp := split_sf hψ L' hu
    have hR0 := R0_eq (F := F) hu2
    have hne2 : 1 - 2 * w ≠ 0 := by
      intro h'; have := congrArg Complex.re h'; simp [hwre] at this; linarith
    have hz : dedekindZeta F (2 * (1 - w)) = R0 F (2 * (1 - w)) / (1 - 2 * w) := by
      rw [hR0, eq_div_iff hne2]; ring
    rw [hh]; dsimp only
    rw [hfe, hdir, hsq, hsp, HP, HQ, Kd, Zm, hz]
    ring
  -- (E) the pole function
  obtain ⟨Af, hAf⟩ : ∃ Af : ℂ → ℂ, Af = fun w =>
      -(1 / 2 : ℂ) * (Kd 𝔪 𝔤 c ψ M w * R0 F (2 * (1 - w)) * Pf 𝔪 ψ L' (1 - w)) := ⟨_, rfl⟩
  have hHPAf : ∀ w : ℂ, w ≠ 1 / 2 → HP 𝔪 𝔤 c ψ M L' w = Af w / (w - 1 / 2) := by
    intro w hw
    have h1 : w - 1 / 2 ≠ 0 := sub_ne_zero.2 hw
    have h2 : 1 - 2 * w ≠ 0 := by
      intro h'; apply h1; linear_combination (-1 / 2 : ℂ) * h'
    rw [HP, hAf, eq_div_iff h1]; dsimp only
    rw [show w - 1 / 2 = -(1 / 2) * (1 - 2 * w) by ring, div_eq_mul_inv]
    have hinv : (1 - 2 * w)⁻¹ * (1 - 2 * w) = 1 := inv_mul_cancel₀ h2
    linear_combination (-(1 / 2) * Kd 𝔪 𝔤 c ψ M w * R0 F (2 * (1 - w)) * Pf 𝔪 ψ L' (1 - w)) * hinv
  have hAfP : PolyB Af (-σ₁) (1 - ε') :=
    ((PolyB.const_bound (f := fun _ => -(1 / 2 : ℂ)) (a := -σ₁) (b := 1 - ε') (C := 1 / 2)
      (by norm_num) fun _ _ _ => by norm_num).mul
      (((PolyB_Kd 𝔪 𝔤 hψ.norm_le hc hM (-σ₁) (1 - ε') (by linarith)).mul
      (PolyB_R0 (F := F) (-σ₁) (1 - ε') (by linarith))).mul
      (PolyB_Pf 𝔪 hψ.norm_le L' (-σ₁) (1 - ε') (by linarith)))).congr fun w _ _ => by rw [hAf]
  have hAfd : DifferentiableOn ℂ Af {s | -σ₁ ≤ s.re ∧ s.re ≤ 1 - ε'} := by
    rw [hAf]
    refine DifferentiableOn.const_mul (((differentiableOn_Kd 𝔪 𝔤 ψ hc hM (by linarith)).mul ?_).mul
      (differentiable_Pf 𝔪 ψ L').differentiableOn) _
    exact ((R0_diff F).comp (by fun_prop : Differentiable ℂ fun w : ℂ => 2 * (1 - w))).differentiableOn
  obtain ⟨CA, AA, hCA, hAA, hAfb⟩ := hAfP
  have hpole := shift_pole (Af := Af) (a := -σ₁) (b := 1 - ε') (p := 1 / 2) (by linarith)
    (by linarith) hAA hAfd hAfb
  -- integrability on the line `-σ₁`
  have hne_a : ∀ t : ℝ, (((-σ₁ : ℝ) : ℂ) + t * I) ≠ 1 / 2 := by
    intro t h'; have := congrArg Complex.re h'; simp at this; linarith
  have hne_b : ∀ t : ℝ, (((1 - ε' : ℝ) : ℂ) + t * I) ≠ 1 / 2 := by
    intro t h'; have := congrArg Complex.re h'; simp at this; linarith
  have hcl : ∀ σ : ℝ, -σ₁ ≤ σ → σ ≤ 1 - ε' → Continuous fun t : ℝ => Af (σ + t * I) := by
    intro σ h1 h2
    refine hAfd.continuousOn.comp_continuous (by fun_prop) fun t => ?_
    simp only [Set.mem_setOf_eq, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
      mul_one, sub_self, add_zero]
    exact ⟨h1, h2⟩
  have hp2 : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by push_cast; ring
  have hHPline : ∀ σ : ℝ, σ ≠ 1 / 2 → ∀ t : ℝ, HP 𝔪 𝔤 c ψ M L' (σ + t * I) =
      Af (σ + t * I) / ((σ + t * I) - ((1 / 2 : ℝ) : ℂ)) := by
    intro σ hσ t
    rw [hp2]
    refine hHPAf _ fun h' => hσ ?_
    have := congrArg Complex.re h'; simpa using this
  -- integrability on `Re w = -σ₁`
  have hIh : Integrable fun t : ℝ => Wm (((-σ₁ : ℝ) : ℂ) + t * I) * h (((-σ₁ : ℝ) : ℂ) + t * I) :=
    integrable_Wm_mul ⟨Ch, Ah, hCh, hAh, hhb⟩ le_rfl (by linarith) (hhd.continuous.comp (by fun_prop))
  have hHPa : PolyB (HP 𝔪 𝔤 c ψ M L') (-σ₁) (-σ₁) := by
    refine ⟨2 * CA, AA, by positivity, hAA, fun w h1 h2 => ?_⟩
    have hwre : w.re = -σ₁ := le_antisymm h2 h1
    have hw : w ≠ 1 / 2 := by intro h'; rw [h'] at hwre; norm_num at hwre; linarith
    rw [hHPAf w hw, norm_div]
    have hden : 1 / 2 ≤ ‖w - 1 / 2‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      simp only [sub_re, hwre]; norm_num
      rw [abs_of_neg (by linarith)]; linarith
    have hAfw := hAfb w (by linarith) (by linarith)
    rw [div_le_iff₀ (by linarith)]
    calc ‖Af w‖ ≤ CA * (1 + |w.im|) ^ AA := hAfw
      _ = 2 * CA * (1 + |w.im|) ^ AA * (1 / 2) := by ring
      _ ≤ 2 * CA * (1 + |w.im|) ^ AA * ‖w - 1 / 2‖ := by gcongr
  have hIP : Integrable fun t : ℝ =>
      Wm (((-σ₁ : ℝ) : ℂ) + t * I) * HP 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I) := by
    refine integrable_Wm_mul hHPa le_rfl le_rfl ?_
    have hcont : Continuous fun t : ℝ => Af (((-σ₁ : ℝ) : ℂ) + t * I) /
        ((((-σ₁ : ℝ) : ℂ) + t * I) - ((1 / 2 : ℝ) : ℂ)) := by
      refine (hcl (-σ₁) le_rfl (by linarith)).div (by fun_prop) fun t h' => ?_
      have := congrArg Complex.re h'; simp at this; linarith
    refine hcont.congr fun t => (hHPline (-σ₁) (by linarith) t).symm
  have hIQ : Integrable fun t : ℝ =>
      Wm (((-σ₁ : ℝ) : ℂ) + t * I) * HQ 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I) := by
    refine (hIh.sub hIP).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    rw [hline t]; ring
  have hsplit : ∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) * h (((-σ₁ : ℝ) : ℂ) + t * I) =
      (∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) * HP 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I)) +
      ∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) * HQ 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I) := by
    rw [← integral_add hIP hIQ]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [hline t]; ring
  -- the pole shift for the `P`-part
  have hPa : ∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) * HP 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I) =
      (∫ t : ℝ, Wm (((1 - ε' : ℝ) : ℂ) + t * I) * HP 𝔪 𝔤 c ψ M L' (((1 - ε' : ℝ) : ℂ) + t * I)) -
        2 * (π : ℂ) * (Wm ((1 / 2 : ℝ) : ℂ) * Af ((1 / 2 : ℝ) : ℂ)) := by
    have e1 : ∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) * HP 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I) =
        ∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) * (Af (((-σ₁ : ℝ) : ℂ) + t * I) /
          ((((-σ₁ : ℝ) : ℂ) + t * I) - ((1 / 2 : ℝ) : ℂ))) :=
      integral_congr_ae (Eventually.of_forall fun t => by
        simp only; rw [hHPline (-σ₁) (by linarith) t])
    have e2 : ∫ t : ℝ, Wm (((1 - ε' : ℝ) : ℂ) + t * I) *
        HP 𝔪 𝔤 c ψ M L' (((1 - ε' : ℝ) : ℂ) + t * I) =
        ∫ t : ℝ, Wm (((1 - ε' : ℝ) : ℂ) + t * I) * (Af (((1 - ε' : ℝ) : ℂ) + t * I) /
          ((((1 - ε' : ℝ) : ℂ) + t * I) - ((1 / 2 : ℝ) : ℂ))) :=
      integral_congr_ae (Eventually.of_forall fun t => by
        simp only; rw [hHPline (1 - ε') (by linarith) t])
    rw [e1, e2, hpole]; ring
  -- the residue is `-T`
  have hres : Wm ((1 / 2 : ℝ) : ℂ) * Af ((1 / 2 : ℝ) : ℂ) = -Tdual 𝔪 𝔤 c ψ M L' := by
    rw [hp2, hAf]; dsimp only
    rw [Tdual, Kd]
    have h12 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
    have h21 : (2 : ℂ) * (1 - 1 / 2) = 1 := by norm_num
    rw [h12, show (2 : ℂ) * (1 / 2) = 1 by norm_num, show (1 / 2 : ℂ) - 1 / 2 = 0 by ring,
      cpow_zero, G0_half, one_pow, Em, Zm]
    have hne := prod_one_sub_ne_zero 𝔪 (u := 1 / 2) (by norm_num)
    field_simp
  rw [hsplit, hPa, hres]
  generalize (∫ t : ℝ, Wm (((1 - ε' : ℝ) : ℂ) + t * I) *
    HP 𝔪 𝔤 c ψ M L' (((1 - ε' : ℝ) : ℂ) + t * I)) = J1
  generalize (∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) *
    HQ 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I)) = J2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3H_Mob: Möbius function and divisor counts for squarefree ideals of `𝓞 F`

* `pf n`: the set of prime factors; for squarefree `n ≠ ⊥`, `∏_{p ∈ pf n} p = n`.
* `mobI`: `μ(d) = (-1)^ω(d)` on squarefree `d`, `0` otherwise.
* `sum_mobI`: `∑_{d ∈ S, d ∣ n} μ(d) = [n = ⊤]` for squarefree `n ≠ ⊥`, if `S` holds every divisor.
* `card_dvd_le`: `#{d ∈ S, d ∣ n} ≤ 2^ω(n)` for squarefree `n ≠ ⊥`.
* `two_pow_card_pf_le`: `2^ω(n) ≤ C_ε (N n)^ε` for squarefree `n ≠ ⊥`.
-/

open NumberField UniqueFactorizationMonoid

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

lemma nf_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) :
    normalizedFactors (∏ p ∈ T, p) = T.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact normalizedFactors_prod_of_prime fun p hp => hT p hp

lemma sq_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) : Squarefree (∏ p ∈ T, p) := by
  have h0 : ∏ p ∈ T, p ≠ ⊥ := by
    have : ∏ p ∈ T, p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hT p hp).ne_zero
    rwa [Ideal.zero_eq_bot] at this
  rw [squarefree_iff_nodup_normalizedFactors h0, nf_prod T hT]
  exact T.nodup

end L3H

end
end

section
section
/-!
# L3Q_TT: the two main terms `T` and `T′`

`T − T′ = κ √M Wm(1/2) ∏_{P ∣ 𝔪c}(1 − 1/NP) ∑_{e, f ⊆ primes(𝔤)} (−1)^{|e|} (NeNf)^{-1/2} ψ(e)ψ(f)
  ∑_{s coprime 𝔤} (1[Ns ≤ L′/Nf] − 1[Ns ≤ L]) ψ(s) Ns^{-1/2}`: only rows between `L′/Nf` and `L`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology UniqueFactorizationMonoid
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma pideal_ne_bot {𝔤 : Ideal (𝓞 F)} {f : Finset (Ideal (𝓞 F))} (hf : f ⊆ primesOf 𝔤) :
    pideal f ≠ ⊥ := by
  rw [pideal, Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff, not_exists]
  intro P ⟨hP, h0⟩
  exact (primesOf_prime (hf hP)).2 (by rw [← Ideal.zero_eq_bot]; exact h0)

lemma pideal_le_iff {𝔤 P : Ideal (𝓞 F)} {f : Finset (Ideal (𝓞 F))} (hf : f ⊆ primesOf 𝔤)
    (hP : P ∈ primesOf 𝔤) : pideal f ≤ P ↔ P ∈ f := by
  constructor
  · intro h
    obtain ⟨Q, hQ, hQP⟩ := ((primesOf_prime hP).1.prod_le (s := f) (f := id)).1 (by simpa [pideal] using h)
    have hQm := (primesOf_prime (hf hQ))
    have : Q = P := (Ideal.IsMaximal.eq_of_le (hQm.1.isMaximal hQm.2) (primesOf_prime hP).1.ne_top hQP)
    exact this ▸ hQ
  · intro h
    exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ h)

lemma isExterior_of_mem_primesOf {𝔪 𝔤 P : Ideal (𝓞 F)} (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) (hP : P ∈ primesOf 𝔤) :
    IsExterior 𝔪 P :=
  ⟨(primesOf_prime hP).2, top_le_iff.1 (h𝔤m ▸ sup_le_sup_right (le_of_mem_primesOf hP) 𝔪)⟩

lemma sup_pideal_of_cop {𝔤 s : Ideal (𝓞 F)} {f : Finset (Ideal (𝓞 F))} (hf : f ⊆ primesOf 𝔤)
    (hs : s ⊔ 𝔤 = ⊤) : s ⊔ pideal f = ⊤ := by
  classical
  unfold pideal
  induction f using Finset.induction_on with
  | empty => simp
  | insert P f hP ih =>
    rw [Finset.prod_insert hP, sup_comm, sup_mul_eq_top_iff, sup_comm, sup_comm (∏ P ∈ f, P)]
    refine ⟨top_le_iff.1 (hs ▸ sup_le_sup_left (le_of_mem_primesOf (hf (Finset.mem_insert_self _ _))) s),
      ih (fun Q hQ => hf (Finset.mem_insert_of_mem hQ))⟩

lemma isExterior_pideal {𝔪 𝔤 : Ideal (𝓞 F)} (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) {f : Finset (Ideal (𝓞 F))}
    (hf : f ⊆ primesOf 𝔤) : IsExterior 𝔪 (pideal f) := by
  classical
  unfold pideal
  induction f using Finset.induction_on with
  | empty => exact ⟨by simp, by simp⟩
  | insert P f hP ih =>
    rw [Finset.prod_insert hP]
    exact C3I.isExterior_mul (isExterior_of_mem_primesOf h𝔤m (hf (Finset.mem_insert_self _ _)))
      (ih fun Q hQ => hf (Finset.mem_insert_of_mem hQ))

lemma squarefree_pideal {𝔤 : Ideal (𝓞 F)} {f : Finset (Ideal (𝓞 F))} (hf : f ⊆ primesOf 𝔤) :
    Squarefree (pideal f) :=
  L3H.sq_prod f fun P hP => Ideal.prime_of_isPrime (primesOf_prime (hf hP)).2
    (primesOf_prime (hf hP)).1

lemma absNorm_pideal_pos {𝔤 : Ideal (𝓞 F)} {f : Finset (Ideal (𝓞 F))} (hf : f ⊆ primesOf 𝔤) :
    (0 : ℝ) < Ideal.absNorm (pideal f) := absNorm_pos (pideal_ne_bot hf)

/-- Rows `s` of norm `≤ Y` regrouped by their `𝔤`-part. -/
theorem regroup {𝔪 𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) (Y : ℝ)
    (G : Ideal (𝓞 F) → ℂ) :
    ∑ s ∈ L3H.rowsF 𝔪 0 Y, G s = ∑ f ∈ (primesOf 𝔤).powerset,
      ∑ s ∈ Srow 𝔪 𝔤 (Y / Ideal.absNorm (pideal f)), G (pideal f * s) := by
  classical
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => pideal x.1 * x.2) ?_ ?_ ?_ ?_
  · rintro ⟨f, s⟩ hx
    rw [Finset.mem_sigma, Finset.mem_powerset] at hx
    obtain ⟨hf, hs⟩ := hx
    obtain ⟨hse, hsq, hsY, hsg⟩ := mem_Srow.1 hs
    have hfp := absNorm_pideal_pos hf
    refine L3H.mem_rowsF_zero.2 ⟨C3I.isExterior_mul (isExterior_pideal h𝔤m hf) hse, ?_, ?_⟩
    · refine squarefree_mul_iff.2 ⟨?_, squarefree_pideal hf, hsq⟩
      have := sup_pideal_of_cop hf hsg
      rw [sup_comm] at this
      exact (Ideal.isCoprime_iff_sup_eq.2 this).isRelPrime
    · rw [map_mul, Nat.cast_mul]
      rw [le_div_iff₀ hfp] at hsY
      linarith
  · rintro ⟨f, s⟩ hx ⟨f', s'⟩ hx' heq
    rw [Finset.mem_sigma, Finset.mem_powerset] at hx hx'
    simp only at heq
    have hsg := (mem_Srow.1 hx.2).2.2.2
    have hsg' := (mem_Srow.1 hx'.2).2.2.2
    have hff : f = f' := by
      ext P
      constructor
      · intro hP
        have hPg := hx.1 hP
        have h1 : pideal f * s ≤ P := le_trans Ideal.mul_le_left ((pideal_le_iff hx.1 hPg).2 hP)
        rw [heq] at h1
        rcases (primesOf_prime hPg).1.mul_le.1 h1 with h2 | h2
        · exact (pideal_le_iff hx'.1 hPg).1 h2
        · exfalso
          exact (sup_eq_top_iff_forall h𝔤).1 hsg' P hPg h2
      · intro hP
        have hPg := hx'.1 hP
        have h1 : pideal f' * s' ≤ P := le_trans Ideal.mul_le_left ((pideal_le_iff hx'.1 hPg).2 hP)
        rw [← heq] at h1
        rcases (primesOf_prime hPg).1.mul_le.1 h1 with h2 | h2
        · exact (pideal_le_iff hx.1 hPg).1 h2
        · exfalso
          exact (sup_eq_top_iff_forall h𝔤).1 hsg P hPg h2
    subst hff
    have hss : s = s' := by
      have h0 : pideal f ≠ 0 := by rw [Ideal.zero_eq_bot]; exact pideal_ne_bot hx.1
      exact mul_left_cancel₀ h0 heq
    subst hss; rfl
  · intro s hs
    obtain ⟨hse, hsq, hsY⟩ := L3H.mem_rowsF_zero.1 hs
    set f := (primesOf 𝔤).filter (fun P => s ≤ P) with hfdef
    have hf : f ⊆ primesOf 𝔤 := Finset.filter_subset _ _
    have hdvd : pideal f ∣ s := by
      refine Finset.prod_primes_dvd s (fun P hP => Ideal.prime_of_isPrime
        (primesOf_prime (hf hP)).2 (primesOf_prime (hf hP)).1) fun P hP => ?_
      exact Ideal.dvd_iff_le.2 (Finset.mem_filter.1 hP).2
    obtain ⟨s', hs'⟩ := hdvd
    rw [hs'] at hse hsq hsY
    have hs'0 : s' ≠ ⊥ := by rintro rfl; rw [Ideal.mul_bot] at hse; exact hse.1 rfl
    have hs'g : s' ⊔ 𝔤 = ⊤ := by
      refine (sup_eq_top_iff_forall h𝔤).2 fun P hP hle => ?_
      by_cases hPf : P ∈ f
      · -- `P² ∣ s`
        have h1 : P ∣ pideal f := Finset.dvd_prod_of_mem _ hPf
        have h2 : P ∣ s' := Ideal.dvd_iff_le.2 hle
        have := hsq P (mul_dvd_mul h1 h2)
        exact (primesOf_prime hP).1.ne_top (Ideal.isUnit_iff.1 this)
      · apply hPf
        rw [hfdef, Finset.mem_filter]
        exact ⟨hP, hs' ▸ le_trans Ideal.mul_le_right hle⟩
    refine ⟨⟨f, s'⟩, ?_, hs'.symm⟩
    rw [Finset.mem_sigma, Finset.mem_powerset]
    refine ⟨hf, mem_Srow.2 ⟨⟨hs'0, ?_⟩, hsq.of_mul_right, ?_, hs'g⟩⟩
    · exact top_le_iff.1 (hse.2 ▸ sup_le_sup_right Ideal.mul_le_right 𝔪)
    · rw [le_div_iff₀ (absNorm_pideal_pos hf)]
      rw [map_mul, Nat.cast_mul] at hsY
      linarith
  · intro x hx; rfl

lemma psi_pideal {𝔪 c 𝔤 : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ)
    {f : Finset (Ideal (𝓞 F))} (hf : f ⊆ primesOf 𝔤) : ψ (pideal f) = ∏ P ∈ f, ψ P := by
  classical
  unfold pideal
  induction f using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]; exact hψ.top
  | insert P f hP ih =>
    have hf' : f ⊆ primesOf 𝔤 := fun Q hQ => hf (Finset.mem_insert_of_mem hQ)
    rw [Finset.prod_insert hP, Finset.prod_insert hP, hψ.mul P (∏ x ∈ f, x) (primesOf_prime (hf
      (Finset.mem_insert_self _ _))).2 (pideal_ne_bot hf'), ih hf']

lemma natCast_prod_cpow {ι : Type*} (S : Finset ι) (n : ι → ℕ) (z : ℂ) :
    ((∏ i ∈ S, n i : ℕ) : ℂ) ^ z = ∏ i ∈ S, (n i : ℂ) ^ z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Nat.cast_mul, natCast_mul_natCast_cpow, ih]

lemma absNorm_pideal_cpow (f : Finset (Ideal (𝓞 F))) (z : ℂ) :
    (Ideal.absNorm (pideal f) : ℂ) ^ z = ∏ P ∈ f, (Ideal.absNorm P : ℂ) ^ z := by
  unfold pideal
  rw [map_prod]
  exact natCast_prod_cpow f (fun P => Ideal.absNorm P) z

lemma primesOf_mul {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    primesOf (I * J) = primesOf I ∪ primesOf J := by
  classical
  ext P
  rw [Finset.mem_union, mem_primesOf, mem_primesOf, mem_primesOf,
    normalizedFactors_mul (by rwa [Ne, ← Ideal.zero_eq_bot] at hI)
      (by rwa [Ne, ← Ideal.zero_eq_bot] at hJ), Multiset.mem_add]

lemma disjoint_primesOf {I J : Ideal (𝓞 F)} (h : I ⊔ J = ⊤) :
    Disjoint (primesOf I) (primesOf J) := by
  rw [Finset.disjoint_left]
  intro P hI hJ
  exact (primesOf_prime hI).1.ne_top (top_le_iff.1 (h ▸ sup_le (le_of_mem_primesOf hI)
    (le_of_mem_primesOf hJ)))

lemma prod_one_sub_expand {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    ∏ i ∈ S, (1 - a i) = ∑ e ∈ S.powerset, (-1 : ℂ) ^ e.card * ∏ i ∈ e, a i := by
  classical
  have h := Finset.prod_add (fun i => -a i) (fun _ => (1 : ℂ)) S
  simp only [Finset.prod_const_one, mul_one, Finset.prod_neg] at h
  rw [← h]
  exact Finset.prod_congr rfl fun i _ => by ring

lemma prod_one_add_expand {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    ∏ i ∈ S, (1 + a i) = ∑ f ∈ S.powerset, ∏ i ∈ f, a i := by
  classical
  have h := Finset.prod_add a (fun _ => (1 : ℂ)) S
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- `T − T′`, exactly. -/
theorem TT_eq {𝔪 𝔤 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} (hψ : PsiHyp 𝔪 c ψ) (h𝔤 : 𝔤 ≠ ⊥)
    (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) (h𝔤c : 𝔤 ⊔ c = ⊤) (h𝔪c : 𝔪 * c ≠ ⊥) {M : ℝ} (hM : 0 < M) (L L' : ℝ) :
    Tdual 𝔪 𝔤 c ψ M L' - ∑ s ∈ Srow 𝔪 𝔤 L, ψ s *
        (R0 F 1 / 2 * (((Ideal.absNorm s : ℝ) / M : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * Wm (1 / 2) *
          (∏ P ∈ primesOf (𝔤 * 𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ))))) =
      R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2) *
        (∏ P ∈ primesOf (𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) *
        ∑ e ∈ (primesOf 𝔤).powerset, ∑ f ∈ (primesOf 𝔤).powerset,
          ((-1 : ℂ) ^ e.card * ψ (pideal e) * (Ideal.absNorm (pideal e) : ℂ) ^ (-(1 / 2 : ℂ)) *
            ψ (pideal f) * (Ideal.absNorm (pideal f) : ℂ) ^ (-(1 / 2 : ℂ))) *
          ((∑ s ∈ Srow 𝔪 𝔤 (L' / Ideal.absNorm (pideal f)),
              ψ s * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ))) -
            ∑ s ∈ Srow 𝔪 𝔤 L, ψ s * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ))) := by
  classical
  set P𝔤 := primesOf 𝔤
  set x : Ideal (𝓞 F) → ℂ := fun P => (Ideal.absNorm P : ℂ) ^ (-(1 / 2 : ℂ))
  set S : ℝ → ℂ := fun Y => ∑ s ∈ Srow 𝔪 𝔤 Y, ψ s * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ))
  -- primes of `q`
  have h𝔤𝔪c : 𝔤 ⊔ 𝔪 * c = ⊤ := by
    rw [sup_comm, sup_mul_eq_top_iff, sup_comm, sup_comm c]; exact ⟨h𝔤m, h𝔤c⟩
  have hq : primesOf (𝔤 * 𝔪 * c) = P𝔤 ∪ primesOf (𝔪 * c) := by
    rw [mul_assoc, primesOf_mul h𝔤 h𝔪c]
  have hprod_q : ∏ P ∈ primesOf (𝔤 * 𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ))) =
      (∏ P ∈ P𝔤, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) *
        ∏ P ∈ primesOf (𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ))) := by
    rw [hq, Finset.prod_union (disjoint_primesOf h𝔤𝔪c)]
  -- `T′` as `κ √M Wm ∏_q S(L)`
  have hTp : ∑ s ∈ Srow 𝔪 𝔤 L, ψ s *
        (R0 F 1 / 2 * (((Ideal.absNorm s : ℝ) / M : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * Wm (1 / 2) *
          (∏ P ∈ primesOf (𝔤 * 𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ))))) =
      R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2) *
        (∏ P ∈ primesOf (𝔤 * 𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) * S L := by
    simp only [S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [cpow_div' (Nat.cast_nonneg _) hM]
    push_cast; ring
  -- the dual rows regrouped
  have hPf : Pf 𝔪 ψ L' (1 / 2) = ∑ f ∈ P𝔤.powerset, ψ (pideal f) * x (pideal f) *
      S (L' / Ideal.absNorm (pideal f)) := by
    rw [Pf_def, regroup h𝔤 h𝔤m L']
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mem_powerset] at hf
    simp only [S, x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs0 := (mem_Srow.1 hs).1.1
    rw [hψ.mul _ _ (pideal_ne_bot hf) hs0, cpow_absNorm_mul]; ring
  -- the Euler factors at `𝔤`
  have hsq : ∀ P ∈ P𝔤, ψ P ^ 2 = 1 := by
    intro P hP
    have hPe := isExterior_of_mem_primesOf h𝔤m hP
    rw [hψ.sq P hPe.1 hPe.2, if_pos]
    exact top_le_iff.1 (h𝔤c ▸ sup_le_sup_right (le_of_mem_primesOf hP) c)
  have hx2 : ∀ P ∈ P𝔤, x P * x P = (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)) := by
    intro P hP
    have hN : (Ideal.absNorm P : ℂ) ≠ 0 := by
      have := one_le_absNorm_of_mem_primesOf hP
      exact_mod_cast (by omega : Ideal.absNorm P ≠ 0)
    simp only [x]; rw [← cpow_add _ _ hN]; norm_num
  have hE1 : ∏ P ∈ P𝔤, (1 - ψ P * (Ideal.absNorm P : ℂ) ^ (-(1 / 2 : ℂ))) =
      ∑ e ∈ P𝔤.powerset, (-1 : ℂ) ^ e.card * (ψ (pideal e) * x (pideal e)) := by
    rw [prod_one_sub_expand]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_powerset] at he
    simp only [x]
    rw [psi_pideal hψ he, absNorm_pideal_cpow, ← Finset.prod_mul_distrib]
  have hE2 : ∏ P ∈ P𝔤, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ))) =
      ∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, (-1 : ℂ) ^ e.card *
        (ψ (pideal e) * x (pideal e)) * (ψ (pideal f) * x (pideal f)) := by
    have hfac : ∀ P ∈ P𝔤, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ))) =
        (1 - ψ P * x P) * (1 + ψ P * x P) := by
      intro P hP
      have : (1 - ψ P * x P) * (1 + ψ P * x P) = 1 - ψ P ^ 2 * (x P * x P) := by ring
      rw [this, hsq P hP, hx2 P hP, one_mul]
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_one_sub_expand,
      prod_one_add_expand, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mem_powerset] at he hf
    simp only [x]
    rw [psi_pideal hψ he, psi_pideal hψ hf, absNorm_pideal_cpow, absNorm_pideal_cpow,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [hTp, hprod_q, Tdual, hPf, hE1, hE2]
  simp only [x]
  generalize R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2) = K
  generalize (∏ P ∈ primesOf (𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) = Pc
  have key : ∀ (a b Sf : Finset (Ideal (𝓞 F)) → ℂ) (SL : ℂ),
      K * Pc * (∑ e ∈ P𝔤.powerset, a e) * (∑ f ∈ P𝔤.powerset, b f * Sf f) -
        K * ((∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, a e * b f) * Pc) * SL =
      K * Pc * ∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, (a e * b f) * (Sf f - SL) := by
    intro a b Sf SL
    have h1 : ∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, (a e * b f) * (Sf f - SL) =
        (∑ e ∈ P𝔤.powerset, a e) * (∑ f ∈ P𝔤.powerset, b f * Sf f) -
          (∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, a e * b f) * SL := by
      rw [Finset.sum_mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun f _ => by ring
    rw [h1]; ring
  have := key (fun e => (-1 : ℂ) ^ e.card * (ψ (pideal e) *
      (Ideal.absNorm (pideal e) : ℂ) ^ (-(1 / 2 : ℂ))))
    (fun f => ψ (pideal f) * (Ideal.absNorm (pideal f) : ℂ) ^ (-(1 / 2 : ℂ)))
    (fun f => S (L' / Ideal.absNorm (pideal f))) (S L)
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Sum: the Poisson sum and the Gauss sum with free generators; CRT and twists

* `PS 𝔰 𝔄 s A Af c h = ∑_{d mod 𝔰} ∑_{v mod 𝔄} [h ≡ Af d (𝔰)] χ_𝔰(d) χ_𝔄(v) e((h − Af d) v c/(sA))`;
  `poissonFactor g 𝔰 𝔄 h = PS 𝔰 𝔄 (gen 𝔰) (gen 𝔄) (gen 𝔄) 1 h`.
* `GS 𝔠 c c' j = ∑_{x mod 𝔠} χ_𝔠(x)^j e(x c'/c)`; `gaussPhase g j 𝔠 = q^{-1/2} GS 𝔠 (gen 𝔠) 1 j`.
* `PS_crt`, `GS_crt`: Chinese remainders with idempotents `β s₂A₂`, `α s₁A₁`.
* `PS_twist`, `GS_twist`: unit substitutions.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

section defs

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

/-! ### Coercions -/

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

end U

/-! ### Field identities -/

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

end gs

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Mul: twisted multiplicativity of `γ_j`, of `F(𝔰, 𝔄, gen(𝔯)⁶)`, of `ϑ`, and reciprocity

* `gaussPhase_mul` (3.10): `γ_j(𝔠₁𝔠₂) = χ_{𝔠₁}(c₂)^j χ_{𝔠₂}(c₁)^j γ_j(𝔠₁) γ_j(𝔠₂)`.
* `poissonFactor_mul`: for `𝔰₁𝔄₁` coprime to `𝔰₂𝔄₂`, `𝔯ᵢ` coprime to the other side,
  `χ_{𝔰₁}(A₂) χ_{𝔰₂}(A₁) F(𝔰₁𝔰₂, 𝔄₁𝔄₂, gen(𝔯₁𝔯₂)⁶)
     = χ_{𝔄₁}(s₂A₂) χ_{𝔄₂}(s₁A₁) F(𝔰₁, 𝔄₁, gen(𝔯₁)⁶) F(𝔰₂, 𝔄₂, gen(𝔯₂)⁶)`.
* `residueSymbol_gen_prime`: `χ_𝔟(gen P) = χ_P(gen 𝔟)` (from (3.3)).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Coprimality in `R` -/

/-! ### Change of generators -/

/-! ### Generators and residue symbols -/

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Main: CutMul from `HypAdd` and `HypChi`

`b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀}, P^l, P^k, P^m) b(𝔠, 𝔫, 𝔰, 𝔯)`: `ϑ` is completely
multiplicative; `γ₂` and `F` split by (3.10) and `poissonFactor_mul`; with `a = χ_P(gen 𝔠)`,
`w = χ_P(gen 𝔠𝔫³) = a b³`, `σ = χ_P(gen 𝔰)`, `t = e₀ + 3l` the cross factors are
`a^{4e₀}` and `w^{2t}`, whose product is `1`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {v : HeightOneSpectrum (𝓞 F)}

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

end roots

section chi

variable {ι : F →+* ℂ}

end chi

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Chk: `HypChi` from section A's `χ_P` (`C3I_Char`), and CutMul

Exterior primes are `C3I.Good` once `N₀ ≥ max(3^[F:ℚ], N 𝔇)`: `12 ∣ N P − 1` because `μ₁₂ ⊂ F`
and `P ∤ 6`, and `P ∤ 𝔇` because `N P > N 𝔇`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Arith: the off-diagonal coefficient `χ_𝔡(g𝔠₁)³ conj χ_𝔡(g𝔠₂)³`

For exterior squarefree `𝔠₁ ≠ 𝔠₂`, with `𝔞 = 𝔠₁ ⊔ 𝔠₂`, `𝔠ᵢ = 𝔞 𝔟ᵢ`, `𝔲 = (𝔟₁𝔟₂)³` and
`T` the primes of `𝔞`: the frequency class `r = (𝔲, 1)` is not principal, `N 𝔲 ≤ (N𝔠₁ N𝔠₂)³`,
`2^{|T|} ≤ N𝔠₁`, and for every exterior `𝔡`
`χ_𝔡(g𝔠₁)³ conj χ_𝔡(g𝔠₂)³ = 1[𝔡 ⊄ P ∀ P ∈ T] χ_𝔡(freqElt g r)`. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

namespace L3E

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end L3E

end ArtinPrimitiveRoots

end
end

section
section
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L3Q_Chi: the quadratic family `χ_c(a) = residueSymbol a (gen c)³`

* `rs_nonext`: the symbol vanishes at non-exterior ideals;
* `chiK_sq`: `χ_c(r)² = [r ⊔ c = ⊤]` for exterior `r, c`;
* `chiK_symm`: exact reciprocity `χ_b(a) = χ_a(b)` for exterior `a, b`;
* `psiHyp_pair`: `a ↦ χ_{c₁}(a) χ_{c₂}(a)` satisfies `PsiHyp 𝔪 (c₁ c₂)`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

set_option linter.unusedSectionVars false

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Pair: the explicit formula for one pair `(c₁, c₂)`

`O = ∑'_{a ⊔ 𝔤 = ⊤, s(a) > L} W(Na/M) ψ(a) = (T − T′) + DP + DQ − RP`, from `Aall_eq`, `Ale_eq`, `TT_eq`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory UniqueFactorizationMonoid
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

open Classical in
/-- The explicit formula for one pair. -/
theorem pair_eq {𝔪 𝔤 c : Ideal (𝓞 F)} {ψ : Ideal (𝓞 F) → ℂ} {Λ : ℂ → ℂ}
    (hψ : PsiHyp 𝔪 c ψ) (hΛ : LamHyp 𝔪 c ψ Λ) (h𝔤 : 𝔤 ≠ ⊥) (h𝔪0 : 𝔪 ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤)
    (hc : c ≠ ⊥) (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) (h𝔤c : 𝔤 ⊔ c = ⊤) {M : ℝ} (hM : 0 < M) (L L' : ℝ)
    {ε ε' σ₁ : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hε' : 0 < ε') (hε'2 : ε' < 1 / 2)
    (hσ₁ : 0 < σ₁) (hσint : ∀ m : ℕ, σ₁ ≠ m) :
    ∑' a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ ∧ sgt L a then
        (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0) =
      TTt 𝔪 𝔤 c ψ M L L' + DPt 𝔪 𝔤 c ψ M L' ε' + DQt 𝔪 𝔤 c ψ M L' σ₁ - RPt 𝔪 𝔤 c ψ M L ε := by
  have h𝔪c : 𝔪 * c ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    exact ⟨by rwa [Ideal.zero_eq_bot], by rwa [Ideal.zero_eq_bot]⟩
  have hq : 𝔤 * 𝔪 * c ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, mul_eq_zero, not_or, not_or]
    exact ⟨⟨by rwa [Ideal.zero_eq_bot], by rwa [Ideal.zero_eq_bot]⟩, by rwa [Ideal.zero_eq_bot]⟩
  -- finite support
  have hfin : ∀ f : Ideal (𝓞 F) → ℂ, (∀ a, 3 * M ≤ (Ideal.absNorm a : ℝ) → f a = 0) →
      Summable f := by
    intro f hf
    refine summable_of_finite_support ((finite_absNorm_le (F := F) (3 * M)).subset ?_)
    intro a ha
    simp only [Function.mem_support] at ha
    show (Ideal.absNorm a : ℝ) ≤ 3 * M
    by_contra hc'; push Not at hc'
    exact ha (hf a hc'.le)
  have hsplit : ∀ a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ ∧ sgt L a then
      (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0) =
      (if a ⊔ 𝔤 = ⊤ then (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0) -
      (if a ⊔ 𝔤 = ⊤ ∧ ¬ sgt L a then (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a else 0) := by
    intro a
    by_cases h1 : a ⊔ 𝔤 = ⊤ <;> by_cases h2 : sgt L a <;> simp [h1, h2]
  have hz : ∀ a : Ideal (𝓞 F), 3 * M ≤ (Ideal.absNorm a : ℝ) →
      (W ((Ideal.absNorm a : ℝ) / M) : ℂ) = 0 := fun a ha => by rw [W_div_eq_zero hM ha]; simp
  rw [tsum_congr hsplit, Summable.tsum_sub (hfin _ fun a ha => by simp [hz a ha])
      (hfin _ fun a ha => by simp [hz a ha]),
    Aall_eq hψ hΛ h𝔤 h𝔪c h𝔪t hc hM hσ₁ hσint hε' hε'2 L',
    Ale_eq hψ hq h𝔪t hM L hε hε2]
  have hTT := TT_eq hψ h𝔤 h𝔤m h𝔤c h𝔪c hM L L'
  rw [TTt, DPt, DQt, RPt, ← hTT]
  rw [Finset.sum_congr rfl fun s _ => mul_add (ψ s) _ _, Finset.sum_add_distrib]
  ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3Q_PS_Dev: the explicit formula for one pair (seam of 85b89dd7), statement verbatim

From `L3Q.pair_eq`. Does not import its own stub. -/

namespace ArtinPrimitiveRoots

open NumberField

theorem tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt (F : Type*) [Field F] [NumberField F]
    (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (Λ : ℂ → ℂ) (hψ : GLW.PsiHyp 𝔪 c ψ)
    (hΛ : GLW.LamHyp 𝔪 c ψ Λ) (h𝔤 : 𝔤 ≠ ⊥) (h𝔪0 : 𝔪 ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤) (hc : c ≠ ⊥)
    (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) (h𝔤c : 𝔤 ⊔ c = ⊤) (M : ℝ) (hM : 0 < M) (L L' ε ε' σ₁ : ℝ)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hε' : 0 < ε') (hε'2 : ε' < 1 / 2) (hσ₁ : 0 < σ₁)
    (hσint : ∀ m : ℕ, σ₁ ≠ m) :
    ∑' a : Ideal (𝓞 F), ({a | a ⊔ 𝔤 = ⊤ ∧ GLW.sgt L a} : Set (Ideal (𝓞 F))).indicator
        (fun a => (GLW.W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a) a =
      GLW.TTt 𝔪 𝔤 c ψ M L L' + GLW.DPt 𝔪 𝔤 c ψ M L' ε' + GLW.DQt 𝔪 𝔤 c ψ M L' σ₁ -
        GLW.RPt 𝔪 𝔤 c ψ M L ε := by
  classical
  rw [← L3Q.pair_eq hψ hΛ h𝔤 h𝔪0 h𝔪t hc h𝔤m h𝔤c hM L L' hε hε2 hε' hε'2 hσ₁ hσint]
  refine tsum_congr fun a => ?_
  by_cases hh : a ⊔ 𝔤 = ⊤ ∧ GLW.sgt L a
  · rw [Set.indicator_of_mem (show a ∈ {a | a ⊔ 𝔤 = ⊤ ∧ GLW.sgt L a} from hh), if_pos hh]
  · rw [Set.indicator_of_notMem (show a ∉ {a | a ⊔ 𝔤 = ⊤ ∧ GLW.sgt L a} from hh), if_neg hh]

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (F : Type*) [Field F] [NumberField F]
    (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (Λ : ℂ → ℂ) (hψ : GLW.PsiHyp 𝔪 c ψ)
    (hΛ : GLW.LamHyp 𝔪 c ψ Λ) (h𝔤 : 𝔤 ≠ ⊥) (h𝔪0 : 𝔪 ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤) (hc : c ≠ ⊥)
    (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) (h𝔤c : 𝔤 ⊔ c = ⊤) (M : ℝ) (hM : 0 < M) (L L' ε ε' σ₁ : ℝ)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hε' : 0 < ε') (hε'2 : ε' < 1 / 2) (hσ₁ : 0 < σ₁)
    (hσint : ∀ m : ℕ, σ₁ ≠ m) :
    ∑' a : Ideal (𝓞 F), ({a | a ⊔ 𝔤 = ⊤ ∧ GLW.sgt L a} : Set (Ideal (𝓞 F))).indicator
        (fun a => (GLW.W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a) a =
      GLW.TTt 𝔪 𝔤 c ψ M L L' + GLW.DPt 𝔪 𝔤 c ψ M L' ε' + GLW.DQt 𝔪 𝔤 c ψ M L' σ₁ -
        GLW.RPt 𝔪 𝔤 c ψ M L ε := by
  exact ArtinPrimitiveRoots.tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt F 𝔪 𝔤 c ψ Λ hψ hΛ h𝔤 h𝔪0 h𝔪t hc h𝔤m h𝔤c M hM L L' ε ε' σ₁ hε hε2 hε' hε'2 hσ₁ hσint

end
