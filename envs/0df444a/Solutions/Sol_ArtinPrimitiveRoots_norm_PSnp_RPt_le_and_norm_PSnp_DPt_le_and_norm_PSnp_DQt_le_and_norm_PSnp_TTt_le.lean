-- Prove2me | solution 1 for ArtinPrimitiveRoots.norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T11:04:25.393759+00:00
-- url     : https://prove2.me/submissions/b72a16a2-3270-43b0-909b-31c79fb7536d

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

theorem tsupport_W : tsupport W ⊆ Set.Icc (1 / 2) (5 / 2) := by
  have : tsupport W = Metric.closedBall (3 / 2 : ℝ) 1 := WB.tsupport_eq
  rw [this, Real.closedBall_eq_Icc]
  norm_num

theorem differentiable_Wm : Differentiable ℂ Wm :=
  L92M.mellin_differentiable W contDiff_W (1 / 2) (5 / 2) (by norm_num) tsupport_W

theorem Wm_decay (A σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Wm s‖ ≤ C * (1 + |s.im|) ^ (-A) :=
  L92M.mellin_decay_rpow W contDiff_W (1 / 2) (5 / 2) (by norm_num) tsupport_W A σ₁ σ₂

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

/-! ### A simple pole -/

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

/-! ### Mellin inversion against a Dirichlet series -/

/-! ### Bounding a line integral -/

/-- `∫ ‖Wm(σ+it)‖ (1+|t|)^A dt`. -/
noncomputable def IW (σ A : ℝ) : ℝ := ∫ t : ℝ, ‖Wm (σ + t * I)‖ * (1 + |t|) ^ A

lemma integrable_IW (σ A : ℝ) : Integrable fun t : ℝ => ‖Wm (σ + t * I)‖ * (1 + |t|) ^ A := by
  obtain ⟨C, hC0, hC⟩ := Wm_mul_maj σ σ (max A 0) 1 (le_max_right _ _)
  have hcont : Continuous fun t : ℝ => ‖Wm (σ + t * I)‖ * (1 + |t|) ^ A := by
    refine ((differentiable_Wm.continuous.comp (by fun_prop)).norm).mul ?_
    exact Continuous.rpow_const (by fun_prop) (fun t => Or.inl (by positivity))
  refine Integrable.mono' (integrable_one_add_abs_rpow_neg_two.const_mul C)
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1t : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have him : ((σ : ℂ) + t * I).im = t := by simp
  have hz : ‖(((1 + |t|) ^ A : ℝ) : ℂ)‖ ≤ 1 * (1 + |((σ : ℂ) + t * I).im|) ^ max A 0 := by
    rw [him, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le h1t (le_max_left _ _)
  have := hC (σ + t * I) (by simp) (by simp) _ hz
  rw [him, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (1 + |t|) ^ A)] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact this

lemma IW_nonneg (σ A : ℝ) : 0 ≤ IW σ A := integral_nonneg fun t => by positivity

theorem norm_integral_Wm_le {σ A B : ℝ} {Φ : ℝ → ℂ} (hΦ : AEStronglyMeasurable Φ volume)
    (hb : ∀ t, ‖Φ t‖ ≤ B * (1 + |t|) ^ A) :
    ‖∫ t : ℝ, Wm (σ + t * I) * Φ t‖ ≤ B * IW σ A := by
  have hB : ∀ t : ℝ, ‖Wm (σ + t * I) * Φ t‖ ≤ B * (‖Wm (σ + t * I)‖ * (1 + |t|) ^ A) := by
    intro t
    rw [norm_mul]
    calc ‖Wm (σ + t * I)‖ * ‖Φ t‖ ≤ ‖Wm (σ + t * I)‖ * (B * (1 + |t|) ^ A) :=
          mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)
      _ = _ := by ring
  refine (norm_integral_le_of_norm_le ((integrable_IW σ A).const_mul B)
    (Eventually.of_forall hB)).trans ?_
  rw [integral_const_mul]; rfl

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

lemma absNorm_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (0 : ℝ) < Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  exact_mod_cast Nat.pos_of_ne_zero this

/-! ### Coprimality -/

lemma sup_mul_eq_top_iff {I J K : Ideal (𝓞 F)} : I * J ⊔ K = ⊤ ↔ I ⊔ K = ⊤ ∧ J ⊔ K = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq]
  exact IsCoprime.mul_left_iff

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

theorem summable_norm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) => ‖(Ideal.absNorm I : ℂ) ^ (-s)‖) := by
  refine (summable_absNorm_rpow hs).congr fun I => ?_
  rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
  simp

variable (F) in
theorem exists_dedekindZeta_bound : ∃ B : ℝ, ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := by
  refine ⟨∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)), fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  rw [zeta_tsum hs1]
  refine (norm_tsum_le_tsum_norm (summable_norm_cpow hs1)).trans ?_
  refine Summable.tsum_le_tsum (fun I => ?_) (summable_norm_cpow hs1)
    (summable_absNorm_rpow (by norm_num))
  rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
  simp only [neg_re]
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h | h
  · rw [h, Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by norm_num)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h) (by linarith)

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

/-- The finite sieve-form bound. -/
def SBf (χ : I → I → ℂ) (R Cs : Finset I) (v : ℝ) : Prop :=
  ∀ z : I → ℂ, ∑ a ∈ R, ‖∑ c ∈ Cs, z c * χ a c‖ ^ 2 ≤ v * ∑ c ∈ Cs, ‖z c‖ ^ 2

variable {χ : I → I → ℂ}

theorem SBf.mono_rows {R R' Cs : Finset I} {v : ℝ} (h : SBf χ R' Cs v) (hR : R ⊆ R') :
    SBf χ R Cs v := fun z =>
  le_trans (sum_le_sum_of_subset_of_nonneg hR fun _ _ _ => by positivity) (h z)

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

/-- `χ_𝔠(𝔡)`, the quadratic symbol of the family. -/
noncomputable def chiK (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (𝔡 𝔠 : Ideal (𝓞 F)) : ℂ :=
  residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 3

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

lemma cpow_div' {N : ℝ} (hN : 0 ≤ N) {D : ℝ} (hD : 0 < D) (s : ℂ) :
    (((N / D : ℝ)) : ℂ) ^ (-s) = (N : ℂ) ^ (-s) * (D : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hN (inv_nonneg.2 hD.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hD.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg (D : ℂ) s, inv_inv]

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

open Classical in
/-- The prime factors. -/
noncomputable def pf (n : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := (normalizedFactors n).toFinset

open Classical in
/-- The Möbius function on ideals. -/
noncomputable def mobI (d : Ideal (𝓞 F)) : ℤ :=
  if Squarefree d then (-1) ^ (normalizedFactors d).card else 0

lemma nodup_of_sq {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (normalizedFactors n).Nodup :=
  (squarefree_iff_nodup_normalizedFactors hn0).1 hn

open Classical in
lemma pf_val {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (pf n).val = normalizedFactors n := by
  unfold pf; rw [Multiset.toFinset_val, Multiset.dedup_eq_self.2 (nodup_of_sq hn0 hn)]

lemma prod_pf {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) : ∏ p ∈ pf n, p = n := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', pf_val hn0 hn]
  exact Ideal.prod_normalizedFactors_eq_self hn0

lemma prime_of_mem_pf {n p : Ideal (𝓞 F)} (hp : p ∈ pf n) : Prime p := by
  unfold pf at hp; rw [Multiset.mem_toFinset] at hp
  exact prime_of_normalized_factor p hp

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

open Classical in
lemma pf_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) : pf (∏ p ∈ T, p) = T := by
  unfold pf; rw [nf_prod T hT]; simp

open Classical in
lemma mobI_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) :
    mobI (∏ p ∈ T, p) = (-1) ^ T.card := by
  unfold mobI; rw [if_pos (sq_prod T hT), nf_prod T hT]; rfl

lemma pf_subset_of_dvd {d n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hd : d ∣ n) : pf d ⊆ pf n := by
  classical
  have hd0 : d ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd)
  intro p hp
  unfold pf at hp ⊢
  rw [Multiset.mem_toFinset] at hp ⊢
  exact Multiset.subset_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn0).1 hd) hp

lemma sq_of_dvd {d n : Ideal (𝓞 F)} (hn : Squarefree n) (hd : d ∣ n) : Squarefree d :=
  hn.squarefree_of_dvd hd

open Classical in
/-- Divisors of a squarefree `n` and subsets of its prime factors. -/
lemma sum_dvd_eq_sum_powerset {M : Type*} [AddCommMonoid M] (S : Finset (Ideal (𝓞 F)))
    {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) (hS : ∀ d, d ∣ n → d ∈ S)
    (f : Ideal (𝓞 F) → M) :
    ∑ d ∈ S.filter (· ∣ n), f d = ∑ T ∈ (pf n).powerset, f (∏ p ∈ T, p) := by
  refine Finset.sum_nbij' (fun d => pf d) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_powerset]
    exact pf_subset_of_dvd hn0 hd.2
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_filter]
    have hdvd : ∏ p ∈ T, p ∣ n := by
      rw [← prod_pf hn0 hn]; exact Finset.prod_dvd_prod_of_subset _ _ _ hT
    exact ⟨hS _ hdvd, hdvd⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hd0 : d ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd.2)
    exact prod_pf hd0 (sq_of_dvd hn hd.2)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact pf_prod T fun p hp => prime_of_mem_pf (hT hp)
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hd0 : d ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd.2)
    rw [prod_pf hd0 (sq_of_dvd hn hd.2)]

lemma pf_eq_empty {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    pf n = ∅ ↔ n = ⊤ := by
  constructor
  · intro h; rw [← prod_pf hn0 hn, h, Finset.prod_empty, Ideal.one_eq_top]
  · rintro rfl
    classical
    unfold pf; rw [← Ideal.one_eq_top, normalizedFactors_one]; rfl

open Classical in
theorem sum_mobI (S : Finset (Ideal (𝓞 F))) {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n)
    (hS : ∀ d, d ∣ n → d ∈ S) :
    ∑ d ∈ S.filter (· ∣ n), mobI d = if n = ⊤ then 1 else 0 := by
  rw [sum_dvd_eq_sum_powerset S hn0 hn hS]
  rw [Finset.sum_congr rfl fun T hT => mobI_prod T fun p hp =>
    prime_of_mem_pf (Finset.mem_powerset.1 hT hp)]
  rw [Finset.sum_powerset_neg_one_pow_card]
  simp only [pf_eq_empty hn0 hn]

open Classical in
theorem card_dvd_le (S : Finset (Ideal (𝓞 F))) {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥)
    (hn : Squarefree n) : (S.filter (· ∣ n)).card ≤ 2 ^ (pf n).card := by
  rw [← Finset.card_powerset]
  refine Finset.card_le_card_of_injOn (fun d => pf d) ?_ ?_
  · intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    rw [Finset.mem_coe, Finset.mem_powerset]
    exact pf_subset_of_dvd hn0 hd.2
  · intro d₁ hd₁ d₂ hd₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
    have h1 : d₁ ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd₁.2)
    have h2 : d₂ ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd₂.2)
    rw [← prod_pf h1 (sq_of_dvd hn hd₁.2), ← prod_pf h2 (sq_of_dvd hn hd₂.2)]
    exact congrArg (fun T => ∏ p ∈ T, p) h

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

lemma absNorm_pideal_pos {𝔤 : Ideal (𝓞 F)} {f : Finset (Ideal (𝓞 F))} (hf : f ⊆ primesOf 𝔤) :
    (0 : ℝ) < Ideal.absNorm (pideal f) := absNorm_pos (pideal_ne_bot hf)

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

lemma norm_sext_le (P : Ideal (𝓞 F)) (x : SInt 𝔪) : ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow, h2.choose_spec.1]; simp
    rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
  · simp

lemma norm_rs_le (I : Ideal (𝓞 F)) (x : SInt 𝔪) : ‖residueSymbol ι 𝔪 I x‖ ≤ 1 := by
  unfold residueSymbol
  induction normalizedFactors I using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (norm_sext_le P x) (norm_nonneg _) ih

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

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Bil: the bilinear bound for coprime pairs

For a kernel `χ` (rows × columns), rows `R`, columns `C`, a Möbius system for coprimality on `C`,
and an `SBf` bound `β` for `χ` on `R × C`:
`‖∑_{c₁,c₂ ∈ C, cop} u(c₁) v(c₂) ∑_{s ∈ R} a(s) χ(s,c₁) χ(s,c₂)‖ ≤ A β √U √V`,
`U = ∑_h ∑_{c, h | c} ‖u c‖²`, `A ≥ ‖a‖`.
-/

namespace ArtinPrimitiveRoots.L3Q


open Finset

variable {I : Type*} [DecidableEq I]

lemma sum_sqrt_mul_sqrt_le (S : Finset I) (f g : I → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i ∈ S, Real.sqrt (f i) * Real.sqrt (g i) ≤
      Real.sqrt (∑ i ∈ S, f i) * Real.sqrt (∑ i ∈ S, g i) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt S (fun i => Real.sqrt (f i)) (fun i => Real.sqrt (g i))
  simp only [Real.sq_sqrt (hf _), Real.sq_sqrt (hg _)] at h
  exact h

lemma sum4_comm {α β γ δ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, f a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ D, f a b c d := sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, f a b c d :=
        sum_congr rfl fun c _ => sum_congr rfl fun a _ => sum_comm
    _ = _ := sum_congr rfl fun c _ => sum_comm

theorem bil_bound (χ : I → I → ℂ) (R C H : Finset I) (μ : I → ℤ) (dv : I → I → Prop)
    [DecidableRel dv] (cop : I → I → Prop) [DecidableRel cop]
    (hmob : ∀ c₁ ∈ C, ∀ c₂ ∈ C, (if cop c₁ c₂ then (1 : ℂ) else 0) =
      ∑ h ∈ H, (μ h : ℂ) * (if dv h c₁ ∧ dv h c₂ then 1 else 0))
    (hμ : ∀ h, ‖(μ h : ℂ)‖ ≤ 1) {β A : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hS : L3H.SBf χ R C β) (a : I → ℂ) (ha : ∀ s ∈ R, ‖a s‖ ≤ A) (u v : I → ℂ) :
    ‖∑ c₁ ∈ C, ∑ c₂ ∈ C, (if cop c₁ c₂ then
        u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0)‖ ≤
      A * β * Real.sqrt (∑ h ∈ H, ∑ c ∈ C, (if dv h c then ‖u c‖ ^ 2 else 0)) *
        Real.sqrt (∑ h ∈ H, ∑ c ∈ C, (if dv h c then ‖v c‖ ^ 2 else 0)) := by
  set uh : I → I → ℂ := fun h c => if dv h c then u c else 0
  set vh : I → I → ℂ := fun h c => if dv h c then v c else 0
  set X : I → I → ℂ := fun h s => ∑ c ∈ C, uh h c * χ s c
  set Y : I → I → ℂ := fun h s => ∑ c ∈ C, vh h c * χ s c
  have hexp : ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if cop c₁ c₂ then
        u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0) =
      ∑ h ∈ H, (μ h : ℂ) * ∑ s ∈ R, a s * (X h s * Y h s) := by
    have e1 : ∀ c₁ ∈ C, ∀ c₂ ∈ C, (if cop c₁ c₂ then
        u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0) =
        ∑ h ∈ H, (μ h : ℂ) * ∑ s ∈ R, a s * ((uh h c₁ * χ s c₁) * (vh h c₂ * χ s c₂)) := by
      intro c₁ hc₁ c₂ hc₂
      have hm := hmob c₁ hc₁ c₂ hc₂
      calc (if cop c₁ c₂ then u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0)
          = (if cop c₁ c₂ then (1 : ℂ) else 0) * (u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂)) := by
            split_ifs <;> simp
        _ = ∑ h ∈ H, (μ h : ℂ) * (if dv h c₁ ∧ dv h c₂ then 1 else 0) *
              (u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂)) := by rw [hm, sum_mul]
        _ = _ := by
            refine sum_congr rfl fun h _ => ?_
            by_cases h1 : dv h c₁ <;> by_cases h2 : dv h c₂
            · simp only [uh, vh, if_pos h1, if_pos h2, if_pos (And.intro h1 h2), mul_one, mul_sum]
              exact sum_congr rfl fun s _ => by ring
            all_goals simp [uh, vh, h1, h2]
    rw [sum_congr rfl fun c₁ hc₁ => sum_congr rfl fun c₂ hc₂ => e1 c₁ hc₁ c₂ hc₂]
    simp only [mul_sum]
    rw [sum4_comm]
    refine sum_congr rfl fun h _ => sum_congr rfl fun s _ => ?_
    have hxy : X h s * Y h s =
        ∑ c₁ ∈ C, ∑ c₂ ∈ C, (uh h c₁ * χ s c₁) * (vh h c₂ * χ s c₂) := by
      simp only [X, Y]; exact Finset.sum_mul_sum _ _ _ _
    rw [hxy, mul_sum, mul_sum]
    refine sum_congr rfl fun c₁ _ => ?_
    rw [mul_sum, mul_sum]
  rw [hexp]
  -- norms
  have hXb : ∀ h, ∑ s ∈ R, ‖X h s‖ ^ 2 ≤ β * ∑ c ∈ C, (if dv h c then ‖u c‖ ^ 2 else 0) := by
    intro h
    refine (hS (uh h)).trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun c _ => ?_
    simp only [uh]; split_ifs <;> simp
  have hYb : ∀ h, ∑ s ∈ R, ‖Y h s‖ ^ 2 ≤ β * ∑ c ∈ C, (if dv h c then ‖v c‖ ^ 2 else 0) := by
    intro h
    refine (hS (vh h)).trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun c _ => ?_
    simp only [vh]; split_ifs <;> simp
  set U : I → ℝ := fun h => ∑ c ∈ C, (if dv h c then ‖u c‖ ^ 2 else 0)
  set V : I → ℝ := fun h => ∑ c ∈ C, (if dv h c then ‖v c‖ ^ 2 else 0)
  have hU0 : ∀ h, 0 ≤ U h := fun h => sum_nonneg fun c _ => by split_ifs <;> positivity
  have hV0 : ∀ h, 0 ≤ V h := fun h => sum_nonneg fun c _ => by split_ifs <;> positivity
  have hterm : ∀ h, ‖(μ h : ℂ) * ∑ s ∈ R, a s * (X h s * Y h s)‖ ≤
      A * β * (Real.sqrt (U h) * Real.sqrt (V h)) := by
    intro h
    rw [norm_mul]
    have h1 : ‖∑ s ∈ R, a s * (X h s * Y h s)‖ ≤ A * ∑ s ∈ R, ‖X h s‖ * ‖Y h s‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun s hs => ?_
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (ha s hs) (by positivity)
    have h2 : ∑ s ∈ R, ‖X h s‖ * ‖Y h s‖ ≤
        Real.sqrt (∑ s ∈ R, ‖X h s‖ ^ 2) * Real.sqrt (∑ s ∈ R, ‖Y h s‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt R _ _
    have h3 : Real.sqrt (∑ s ∈ R, ‖X h s‖ ^ 2) * Real.sqrt (∑ s ∈ R, ‖Y h s‖ ^ 2) ≤
        Real.sqrt (β * U h) * Real.sqrt (β * V h) :=
      mul_le_mul (Real.sqrt_le_sqrt (hXb h)) (Real.sqrt_le_sqrt (hYb h)) (by positivity)
        (by positivity)
    have h4 : Real.sqrt (β * U h) * Real.sqrt (β * V h) = β * (Real.sqrt (U h) * Real.sqrt (V h)) := by
      rw [Real.sqrt_mul hβ, Real.sqrt_mul hβ, show Real.sqrt β * Real.sqrt (U h) *
        (Real.sqrt β * Real.sqrt (V h)) = (Real.sqrt β * Real.sqrt β) *
          (Real.sqrt (U h) * Real.sqrt (V h)) by ring, Real.mul_self_sqrt hβ]
    calc ‖(μ h : ℂ)‖ * ‖∑ s ∈ R, a s * (X h s * Y h s)‖
        ≤ 1 * (A * (β * (Real.sqrt (U h) * Real.sqrt (V h)))) := by
          refine mul_le_mul (hμ h) (h1.trans ?_) (norm_nonneg _) zero_le_one
          exact mul_le_mul_of_nonneg_left (h2.trans (h3.trans h4.le)) hA
      _ = _ := by ring
  refine (norm_sum_le _ _).trans ((sum_le_sum fun h _ => hterm h).trans ?_)
  rw [← mul_sum]
  have := sum_sqrt_mul_sqrt_le H U V hU0 hV0
  calc A * β * ∑ i ∈ H, Real.sqrt (U i) * Real.sqrt (V i)
      ≤ A * β * (Real.sqrt (∑ i ∈ H, U i) * Real.sqrt (∑ i ∈ H, V i)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3H_S3: the weighted forms `Q` (GL's `Σ₂`, `B₂`) and `S3` (GL's `Σ₃`)

Rows `a ∈ Rw` with weights `w a ≥ 0`, kernel `χ a c`, columns a `Finset`.
* `Qf Cs μ = ∑_a w a ‖∑_{c ∈ Cs} μ c χ a c‖²`; `B2f Cs v`: `Qf Cs μ ≤ v ∑ ‖μ c‖²` for all `μ`.
* `S3 Cs 𝔤 λ = ∑_{b₁, b₂ ∈ Cs, b₁ ⊔ b₂ = 𝔤} λ b₁ conj(λ b₂) ∑_a w a χ a b₁ conj(χ a b₂)`.
* `Qf_eq_sum_S3`: `Qf = ∑_𝔤 S3` (sorting the pairs by their gcd).
* `Qf_le_classes`: Cauchy–Schwarz over `k` classes.
* `norm_S3_le_tail`: GL Lemma 5.1's Möbius step: for `𝔤 ≠ ⊥`, `‖S3 Cs 𝔤 λ‖` is at most
  `v' ∑_{d} ∑_{c, d ∣ c} ‖λ(𝔤 c)‖²` from the bound `v'` on columns `c` with `𝔤 c ∈ Cs`.
-/

open NumberField

namespace L3H

section abstract

variable {I : Type*} (χ : I → I → ℂ) (Rw : Finset I) (w : I → ℝ)

variable {χ Rw w}

end abstract

end L3H

end
end

section
section
/-! # L3H_Tail: the Möbius step of GL Lemma 5.1

For `𝔤 ≠ ⊥`: pairs `b₁, b₂` with `b₁ ⊔ b₂ = 𝔤` are `b_i = 𝔤 c_i` with `c₁ ⊔ c₂ = ⊤`; detecting
`c₁ ⊔ c₂ = ⊤` by `∑_{d ∣ c₁, d ∣ c₂} μ(d)` turns `S3` into `∑_d μ(d) Q(c ≡ 0 mod d)`. -/

open NumberField UniqueFactorizationMonoid

namespace L3H

variable {F : Type*} [Field F] [NumberField F]


lemma mobI_abs_le (d : Ideal (𝓞 F)) : |(mobI d : ℝ)| ≤ 1 := by
  classical
  unfold mobI
  split_ifs
  · push_cast; rw [abs_pow, abs_neg, abs_one, one_pow]
  · simp

variable {χ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ} {Rw : Finset (Ideal (𝓞 F))} {w : Ideal (𝓞 F) → ℝ}

end L3H

end
end

section
section
/-!
# L3Q_Mob: the Möbius system on squarefree exterior columns, and the bilinear bound for pairs

`bil_np`: for columns `C ⊆ rows(≤ Cmax)` and an `SBf` bound `β`,
`‖∑_{c₁ ⊔ c₂ = ⊤, (c₁,c₂) ≠ (1,1)} u(c₁) v(c₂) ∑_s a(s) χ(s,c₁)χ(s,c₂)‖ ≤ 2 A β √(∑ 2^ω |u|²) √(∑ 2^ω |v|²)`.
-/

namespace ArtinPrimitiveRoots.L3Q


open NumberField Finset

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma dvd_sup_iff {h c₁ c₂ : Ideal (𝓞 F)} : h ∣ c₁ ⊔ c₂ ↔ h ∣ c₁ ∧ h ∣ c₂ := by
  simp only [Ideal.dvd_iff_le, sup_le_iff]

open Classical in
theorem mob_system {𝔪 : Ideal (𝓞 F)} (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ)
    (hC : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax) :
    ∀ c₁ ∈ C, ∀ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ then (1 : ℂ) else 0) =
      ∑ h ∈ L3H.rowsF 𝔪 0 Cmax, (L3H.mobI h : ℂ) * (if h ∣ c₁ ∧ h ∣ c₂ then 1 else 0) := by
  classical
  intro c₁ hc₁ c₂ hc₂
  obtain ⟨he₁, hsq₁, hN₁⟩ := L3H.mem_rowsF_zero.1 (hC c₁ hc₁)
  set n := c₁ ⊔ c₂
  have hn0 : n ≠ ⊥ := fun h => he₁.1 (le_bot_iff.1 (h ▸ le_sup_left))
  have hn1 : n ∣ c₁ := Ideal.dvd_iff_le.2 le_sup_left
  have hnsq : Squarefree n := hsq₁.squarefree_of_dvd hn1
  have hS : ∀ d, d ∣ n → d ∈ L3H.rowsF 𝔪 0 Cmax := by
    intro d hd
    have hd1 : d ∣ c₁ := dvd_trans hd hn1
    have hle : c₁ ≤ d := Ideal.le_of_dvd hd1
    refine L3H.mem_rowsF_zero.2 ⟨⟨fun h => he₁.1 (le_bot_iff.1 (h ▸ hle)), ?_⟩,
      hsq₁.squarefree_of_dvd hd1, ?_⟩
    · exact top_le_iff.1 (he₁.2 ▸ sup_le_sup_right hle 𝔪)
    · have : Ideal.absNorm d ∣ Ideal.absNorm c₁ := Ideal.absNorm_dvd_absNorm_of_le hle
      have h0 : Ideal.absNorm c₁ ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact he₁.1
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) this
      have : (Ideal.absNorm d : ℝ) ≤ Ideal.absNorm c₁ := by exact_mod_cast this
      linarith
  have hm := L3H.sum_mobI (L3H.rowsF 𝔪 0 Cmax) hn0 hnsq hS
  have e : ∑ h ∈ L3H.rowsF 𝔪 0 Cmax, (L3H.mobI h : ℂ) * (if h ∣ c₁ ∧ h ∣ c₂ then 1 else 0) =
      ((∑ d ∈ (L3H.rowsF 𝔪 0 Cmax).filter (· ∣ n), L3H.mobI d : ℤ) : ℂ) := by
    rw [Int.cast_sum, Finset.sum_filter]
    refine sum_congr rfl fun h _ => ?_
    by_cases hh : h ∣ c₁ ∧ h ∣ c₂
    · rw [if_pos hh, if_pos (dvd_sup_iff.2 hh)]; ring
    · rw [if_neg hh, if_neg (fun h' => hh (dvd_sup_iff.1 h'))]; ring
  rw [e, hm]
  split_ifs <;> simp

lemma mobI_norm_le (h : Ideal (𝓞 F)) : ‖(L3H.mobI h : ℂ)‖ ≤ 1 := by
  have := L3H.mobI_abs_le h
  rw [Complex.norm_intCast]; exact_mod_cast this

open Classical in
theorem tau_sum_le {𝔪 : Ideal (𝓞 F)} (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ)
    (hC : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax) (u : Ideal (𝓞 F) → ℂ) :
    ∑ h ∈ L3H.rowsF 𝔪 0 Cmax, ∑ c ∈ C, (if h ∣ c then ‖u c‖ ^ 2 else 0) ≤
      ∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖u c‖ ^ 2 := by
  classical
  rw [sum_comm]
  refine sum_le_sum fun c hc => ?_
  obtain ⟨he, hsq, -⟩ := L3H.mem_rowsF_zero.1 (hC c hc)
  rw [← sum_filter]
  rw [sum_const, nsmul_eq_mul]
  have := L3H.card_dvd_le (L3H.rowsF 𝔪 0 Cmax) he.1 hsq
  have h2 : (((L3H.rowsF 𝔪 0 Cmax).filter (· ∣ c)).card : ℝ) ≤ (2 : ℝ) ^ (L3H.pf c).card := by
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

open Classical in
theorem bil_np {𝔪 : Ideal (𝓞 F)} (χ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (R C : Finset (Ideal (𝓞 F))) (Cmax : ℝ) (hC : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax)
    {β A : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A) (hS : L3H.SBf χ R C β) (a : Ideal (𝓞 F) → ℂ)
    (ha : ∀ s ∈ R, ‖a s‖ ≤ A) (u v : Ideal (𝓞 F) → ℂ) :
    ‖∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
        u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0)‖ ≤
      2 * A * β * Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖u c‖ ^ 2) *
        Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖v c‖ ^ 2) := by
  set u₀ : Ideal (𝓞 F) → ℂ := fun c => if c = ⊤ then 0 else u c
  set du : Ideal (𝓞 F) → ℂ := fun c => if c = ⊤ then u c else 0
  set v₀ : Ideal (𝓞 F) → ℂ := fun c => if c = ⊤ then 0 else v c
  set Sc : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun c₁ c₂ => ∑ s ∈ R, a s * (χ s c₁ * χ s c₂)
  have hsplit : ∀ c₁ c₂, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
      u c₁ * v c₂ * Sc c₁ c₂ else 0) =
      (if c₁ ⊔ c₂ = ⊤ then u₀ c₁ * v c₂ * Sc c₁ c₂ else 0) +
      (if c₁ ⊔ c₂ = ⊤ then du c₁ * v₀ c₂ * Sc c₁ c₂ else 0) := by
    intro c₁ c₂
    by_cases h : c₁ ⊔ c₂ = ⊤ <;> by_cases h1 : c₁ = ⊤ <;> by_cases h2 : c₂ = ⊤ <;>
      simp [u₀, du, v₀, h, h1, h2]
  simp_rw [show ∀ c₁ c₂, (∑ s ∈ R, a s * (χ s c₁ * χ s c₂)) = Sc c₁ c₂ from fun _ _ => rfl]
  rw [sum_congr rfl fun c₁ _ => sum_congr rfl fun c₂ _ => hsplit c₁ c₂]
  simp only [sum_add_distrib]
  have hm := mob_system (𝔪 := 𝔪) C Cmax hC
  have b1 := bil_bound χ R C (L3H.rowsF 𝔪 0 Cmax) L3H.mobI (fun h c => h ∣ c) (fun c₁ c₂ => c₁ ⊔ c₂ = ⊤)
    hm mobI_norm_le hβ hA hS a ha u₀ v
  have b2 := bil_bound χ R C (L3H.rowsF 𝔪 0 Cmax) L3H.mobI (fun h c => h ∣ c) (fun c₁ c₂ => c₁ ⊔ c₂ = ⊤)
    hm mobI_norm_le hβ hA hS a ha du v₀
  have hU : ∀ f : Ideal (𝓞 F) → ℂ, (∀ c, ‖f c‖ ≤ ‖u c‖) →
      ∑ h ∈ L3H.rowsF 𝔪 0 Cmax, ∑ c ∈ C, (if h ∣ c then ‖f c‖ ^ 2 else 0) ≤
        ∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖u c‖ ^ 2 := by
    intro f hf
    refine (tau_sum_le C Cmax hC f).trans (sum_le_sum fun c _ => ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf c) 2) (by positivity)
  have hV : ∀ f : Ideal (𝓞 F) → ℂ, (∀ c, ‖f c‖ ≤ ‖v c‖) →
      ∑ h ∈ L3H.rowsF 𝔪 0 Cmax, ∑ c ∈ C, (if h ∣ c then ‖f c‖ ^ 2 else 0) ≤
        ∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖v c‖ ^ 2 := by
    intro f hf
    refine (tau_sum_le C Cmax hC f).trans (sum_le_sum fun c _ => ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf c) 2) (by positivity)
  have hu₀ : ∀ c, ‖u₀ c‖ ≤ ‖u c‖ := fun c => by simp only [u₀]; split_ifs <;> simp
  have hdu : ∀ c, ‖du c‖ ≤ ‖u c‖ := fun c => by simp only [du]; split_ifs <;> simp
  have hv₀ : ∀ c, ‖v₀ c‖ ≤ ‖v c‖ := fun c => by simp only [v₀]; split_ifs <;> simp
  have hAβ : 0 ≤ A * β := mul_nonneg hA hβ
  refine (norm_add_le _ _).trans ?_
  have e1 := b1.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hU u₀ hu₀)) hAβ)
    (Real.sqrt_le_sqrt (hV v fun _ => le_rfl)) (Real.sqrt_nonneg _) (by positivity))
  have e2 := b2.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hU du hdu)) hAβ)
    (Real.sqrt_le_sqrt (hV v₀ hv₀)) (Real.sqrt_nonneg _) (by positivity))
  linarith

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Piece: finite sums of line integrals against `Wm`
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open MeasureTheory Complex Filter
open scoped Real

lemma integrable_Wm_of_cont {σ A C : ℝ} {Φ : ℝ → ℂ} (hc : Continuous Φ)
    (hb : ∀ t, ‖Φ t‖ ≤ C * (1 + |t|) ^ A) :
    Integrable fun t : ℝ => Wm (σ + t * I) * Φ t := by
  refine Integrable.mono' ((integrable_IW σ A).const_mul C)
    ((differentiable_Wm.continuous.comp (by fun_prop)).mul hc).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖Wm (σ + t * I)‖ * ‖Φ t‖ ≤ ‖Wm (σ + t * I)‖ * (C * (1 + |t|) ^ A) :=
        mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)
    _ = C * (‖Wm (σ + t * I)‖ * (1 + |t|) ^ A) := by ring

theorem sum_mul_integral {ι : Type*} (S : Finset ι) (w : ι → ℂ) (σ : ℝ) (Φ : ι → ℝ → ℂ)
    (hint : ∀ i ∈ S, Integrable fun t : ℝ => Wm (σ + t * I) * Φ i t) :
    ∑ i ∈ S, w i * ∫ t : ℝ, Wm (σ + t * I) * Φ i t =
      ∫ t : ℝ, Wm (σ + t * I) * ∑ i ∈ S, w i * Φ i t := by
  have e1 : ∀ i, w i * ∫ t : ℝ, Wm (σ + t * I) * Φ i t =
      ∫ t : ℝ, w i * (Wm (σ + t * I) * Φ i t) := fun i => (integral_const_mul _ _).symm
  simp_rw [e1]
  rw [← integral_finset_sum S (fun i hi => (hint i hi).const_mul (w i))]
  congr 1; funext t
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem norm_sum_integral_le {ι : Type*} (S : Finset ι) (w : ι → ℂ) {σ A B : ℝ}
    (Φ : ι → ℝ → ℂ) (hc : ∀ i ∈ S, Continuous (Φ i))
    (hb : ∀ i ∈ S, ∃ C A' : ℝ, ∀ t, ‖Φ i t‖ ≤ C * (1 + |t|) ^ A')
    (hB : ∀ t : ℝ, ‖∑ i ∈ S, w i * Φ i t‖ ≤ B * (1 + |t|) ^ A) :
    ‖∑ i ∈ S, w i * ∫ t : ℝ, Wm (σ + t * I) * Φ i t‖ ≤ B * IW σ A := by
  have hint : ∀ i ∈ S, Integrable fun t : ℝ => Wm (σ + t * I) * Φ i t := by
    intro i hi
    obtain ⟨C, A', hC⟩ := hb i hi
    exact integrable_Wm_of_cont (hc i hi) hC
  rw [sum_mul_integral S w σ Φ hint]
  refine norm_integral_Wm_le ?_ hB
  exact (continuous_finsetSum S fun i hi => continuous_const.mul (hc i hi)).aestronglyMeasurable

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PRP: the error term `RP` summed over pairs

`‖∑_{pairs} z(c₁) conj z(c₂) RP(c₁c₂)‖ ≤ (2π)⁻¹ IW · M^ε 2^{ω(𝔤𝔪)} C_R 2^{A_R}/(1 − 2ε) · 2β · Zτ`,
with `β` an `SBf` bound on rows `≤ L` and `Zτ = ∑ 8^{ω(c)} |z(c)|²`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma primesOf_eq_pf (c : Ideal (𝓞 F)) : primesOf c = L3H.pf c := by
  ext P; simp [primesOf, L3H.pf]

lemma Ztau_def (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ) :
    Ztau C z = ∑ c ∈ C, (8 : ℝ) ^ (L3H.pf c).card * ‖z c‖ ^ 2 := by
  unfold Ztau; simp only [primesOf_eq_pf]

lemma psiP_apply {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (c₁ c₂ a : Ideal (𝓞 F)) :
    psiP g c₁ c₂ a = L3H.chiK ι 𝔪 g a c₁ * L3H.chiK ι 𝔪 g a c₂ := rfl

lemma prod_primes_split {X c₁ c₂ : Ideal (𝓞 F)} (hX : X ≠ ⊥) (h₁ : c₁ ≠ ⊥) (h₂ : c₂ ≠ ⊥)
    (hX₁ : X ⊔ c₁ = ⊤) (hX₂ : X ⊔ c₂ = ⊤) (h₁₂ : c₁ ⊔ c₂ = ⊤) (f : Ideal (𝓞 F) → ℂ) :
    ∏ P ∈ primesOf (X * (c₁ * c₂)), f P =
      (∏ P ∈ primesOf X, f P) * (∏ P ∈ primesOf c₁, f P) * ∏ P ∈ primesOf c₂, f P := by
  have h12 : c₁ * c₂ ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    exact ⟨by rwa [Ideal.zero_eq_bot], by rwa [Ideal.zero_eq_bot]⟩
  have hX12 : X ⊔ c₁ * c₂ = ⊤ := by
    rw [sup_comm, sup_mul_eq_top_iff, sup_comm, sup_comm c₂]; exact ⟨hX₁, hX₂⟩
  rw [primesOf_mul hX h12, prod_union (disjoint_primesOf hX12), primesOf_mul h₁ h₂,
    prod_union (disjoint_primesOf h₁₂)]
  ring

lemma norm_e_le (c : Ideal (𝓞 F)) {u : ℂ} (hu : 0 ≤ u.re) :
    ‖∏ P ∈ primesOf c, (1 - (Ideal.absNorm P : ℂ) ^ (-u))‖ ≤ (2 : ℝ) ^ (L3H.pf c).card := by
  rw [← primesOf_eq_pf]; exact norm_prod_one_sub_le c hu

lemma sqrt_mul_sqrt_le_of_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxz : x ≤ z) (hyz : y ≤ z) :
    Real.sqrt x * Real.sqrt y ≤ z := by
  calc Real.sqrt x * Real.sqrt y ≤ Real.sqrt z * Real.sqrt z :=
        mul_le_mul (Real.sqrt_le_sqrt hxz) (Real.sqrt_le_sqrt hyz) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = z := Real.mul_self_sqrt (le_trans hx hxz)

lemma tau_e_le (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ) (e : Ideal (𝓞 F) → ℂ)
    (he : ∀ c, ‖e c‖ ≤ (2 : ℝ) ^ (L3H.pf c).card) :
    ∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖z c * e c‖ ^ 2 ≤ Ztau C z := by
  rw [Ztau_def]
  refine sum_le_sum fun c _ => ?_
  rw [norm_mul, mul_pow]
  have h1 : ‖e c‖ ^ 2 ≤ ((2 : ℝ) ^ (L3H.pf c).card) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (he c) 2
  have h8 : (8 : ℝ) ^ (L3H.pf c).card = 2 ^ (L3H.pf c).card * ((2 : ℝ) ^ (L3H.pf c).card) ^ 2 := by
    rw [← pow_mul, ← pow_add, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]; ring_nf
  rw [h8]
  calc (2 : ℝ) ^ (L3H.pf c).card * (‖z c‖ ^ 2 * ‖e c‖ ^ 2)
      ≤ 2 ^ (L3H.pf c).card * (‖z c‖ ^ 2 * ((2 : ℝ) ^ (L3H.pf c).card) ^ 2) := by gcongr
    _ = _ := by ring

/-- The `RP` integrand of one row. -/
noncomputable def Thrp (𝔪 𝔤 c : Ideal (𝓞 F)) (M ε : ℝ) (s : Ideal (𝓞 F)) (t : ℝ) : ℂ :=
  (((Ideal.absNorm s : ℝ) / M : ℝ) : ℂ) ^ (-((ε : ℂ) + t * I)) *
    (∏ P ∈ primesOf (𝔤 * 𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((ε : ℂ) + t * I))))) *
    R0 F (2 * ((ε : ℂ) + t * I)) / (2 * ((ε : ℂ) + t * I) - 1)

lemma continuous_cpow_line {X : ℝ} (hX : 0 < X) (β : ℂ) (κ : ℂ) (σ : ℝ) :
    Continuous fun t : ℝ => (X : ℂ) ^ (β + κ * ((σ : ℂ) + t * I)) := by
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  exact_mod_cast hX.ne'

lemma continuous_prod_line (q : Ideal (𝓞 F)) (κ : ℂ) (β : ℂ) (σ : ℝ) :
    Continuous fun t : ℝ => ∏ P ∈ primesOf q,
      (1 - (Ideal.absNorm P : ℂ) ^ (β + κ * ((σ : ℂ) + t * I))) := by
  refine continuous_finsetProd _ fun P hP => continuous_const.sub ?_
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  have := one_le_absNorm_of_mem_primesOf hP
  exact_mod_cast (by omega : Ideal.absNorm P ≠ 0)

lemma continuous_Thrp {𝔪 𝔤 c s : Ideal (𝓞 F)} {M ε : ℝ} (hM : 0 < M) (hs : s ≠ ⊥)
    (hε2 : ε < 1 / 2) : Continuous (Thrp 𝔪 𝔤 c M ε s) := by
  unfold Thrp
  have hX : 0 < (Ideal.absNorm s : ℝ) / M := div_pos (absNorm_pos hs) hM
  refine Continuous.div (((continuous_cpow_line hX 0 (-1) ε).congr fun t => by ring_nf).mul
    ((continuous_prod_line (𝔤 * 𝔪 * c) (-2) 0 ε).congr fun t => by ring_nf) |>.mul
    ((R0_diff F).continuous.comp (by fun_prop))) (by fun_prop) fun t h => ?_
  have := congrArg Complex.re h; simp at this; linarith

lemma norm_line_cpow_le {X : ℝ} (hX : 1 ≤ X) {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (t : ℝ) :
    ‖(((X / M : ℝ)) : ℂ) ^ (-((ε : ℂ) + t * I))‖ ≤ M ^ ε := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos (by linarith) hM)]
  have : (-((ε : ℂ) + t * I)).re = -ε := by simp
  rw [this, Real.div_rpow (by linarith) hM.le, Real.rpow_neg (by linarith), Real.rpow_neg hM.le]
  rw [div_eq_mul_inv, inv_inv]
  have h1 : (X ^ ε)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hX hε)
  have h2 : 0 ≤ M ^ ε := by positivity
  nlinarith

/-- The `RP` term summed over pairs. -/
theorem PS_RP_le {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (𝔤 : Ideal (𝓞 F)), 𝔤 ≠ ⊥ → 𝔤 * 𝔪 ≠ ⊥ →
      ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ), (∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax) →
      (∀ c ∈ C, c ⊔ 𝔤 * 𝔪 = ⊤) →
      ∀ (z : Ideal (𝓞 F) → ℂ) {M L β : ℝ}, 0 < M → 0 ≤ β →
      L3H.SBf (L3H.chiK ι 𝔪 g) (Srow 𝔪 𝔤 L) C β →
        ‖PSnp C z (fun c₁ c₂ => RPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L ε)‖ ≤
          K * M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪)).card * β * Ztau C z := by
  classical
  obtain ⟨CR, AR, hCR, hAR, hRb⟩ := R0_bound F 2
  have h12 : 0 < 1 - 2 * ε := by linarith
  set Kt : ℝ := CR * 2 ^ AR / (1 - 2 * ε) with hKt
  refine ⟨(1 / (2 * π)) * Kt * 2 * IW ε AR, by
    have := IW_nonneg ε AR; have := Real.pi_pos; positivity, ?_⟩
  intro 𝔤 h𝔤 hq0 C Cmax hCr hC z M L β hM hβ hS
  set w : ℝ → ℂ := fun t => (ε : ℂ) + t * I with hw
  have hwre : ∀ t, (w t).re = ε := fun t => by simp [hw]
  -- bounds on the line
  have hR0line : ∀ t, ‖R0 F (2 * w t) / (2 * w t - 1)‖ ≤ Kt * (1 + |t|) ^ AR := by
    intro t
    have hden : 1 - 2 * ε ≤ ‖2 * w t - 1‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      simp only [sub_re, mul_re, hwre, one_re]; norm_num
      rw [abs_of_neg (by linarith)]; linarith
    have hR := hRb (2 * w t) (by simp [hwre]; linarith) (by simp [hwre]; linarith)
    have him : |(2 * w t).im| = 2 * |t| := by simp [hw, abs_mul]
    rw [him] at hR
    have e4 : (1 + 2 * |t|) ^ AR ≤ 2 ^ AR * (1 + |t|) ^ AR := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hAR
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le h12 hden)]
    calc ‖R0 F (2 * w t)‖ ≤ CR * (2 ^ AR * (1 + |t|) ^ AR) := hR.trans (by gcongr)
      _ = Kt * (1 + |t|) ^ AR * (1 - 2 * ε) := by rw [hKt]; field_simp
      _ ≤ Kt * (1 + |t|) ^ AR * ‖2 * w t - 1‖ := by gcongr
  have hThb : ∀ (c s : Ideal (𝓞 F)), s ≠ ⊥ → ∀ t, ‖Thrp 𝔪 𝔤 c M ε s t‖ ≤
      M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪 * c)).card * (Kt * (1 + |t|) ^ AR) := by
    intro c s hs t
    unfold Thrp
    rw [mul_div_assoc, norm_mul, norm_mul]
    have hN1 : (1 : ℝ) ≤ Ideal.absNorm s := L3H.one_le_absNorm hs
    have e1 := norm_line_cpow_le hN1 hM hε.le t
    have e2 := norm_prod_one_sub_le (𝔤 * 𝔪 * c) (u := 2 * w t) (by simp [hwre]; linarith)
    have e3 := hR0line t
    simp only [hw] at e2 e3
    gcongr
  -- each pair's `RP` as one line integral
  set Φ : Ideal (𝓞 F) × Ideal (𝓞 F) → ℝ → ℂ := fun p t =>
    ∑ s ∈ Srow 𝔪 𝔤 L, psiP g p.1 p.2 s * Thrp 𝔪 𝔤 (p.1 * p.2) M ε s t with hΦ
  have hΦc : ∀ p, Continuous (Φ p) := fun p =>
    continuous_finsetSum _ fun s hs => continuous_const.mul
      (continuous_Thrp hM (mem_Srow.1 hs).1.1 hε2)
  have hpsi1 : ∀ c₁ c₂ s, ‖psiP g c₁ c₂ s‖ ≤ 1 := by
    intro c₁ c₂ s
    simp only [psiP_apply, L3H.chiK, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _)) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _))
  have hΦb : ∀ p, ∃ C₀ A' : ℝ, ∀ t, ‖Φ p t‖ ≤ C₀ * (1 + |t|) ^ A' := by
    intro p
    refine ⟨(Srow 𝔪 𝔤 L).card * (M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪 * (p.1 * p.2))).card * Kt), AR,
      fun t => ?_⟩
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [norm_mul]
    calc ‖psiP g p.1 p.2 s‖ * ‖Thrp 𝔪 𝔤 (p.1 * p.2) M ε s t‖ ≤ 1 *
          (M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪 * (p.1 * p.2))).card * (Kt * (1 + |t|) ^ AR)) :=
          mul_le_mul (hpsi1 _ _ _) (hThb _ _ (mem_Srow.1 hs).1.1 t) (norm_nonneg _) zero_le_one
      _ = _ := by ring
  have hRPt : ∀ c₁ c₂, RPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L ε =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (ε + t * I) * Φ (c₁, c₂) t := by
    intro c₁ c₂
    rw [RPt]
    simp_rw [mul_left_comm (psiP g c₁ c₂ _) (1 / (2 * π) : ℂ)]
    rw [← Finset.mul_sum]
    congr 1
    refine sum_mul_integral _ _ ε (fun s t => Thrp 𝔪 𝔤 (c₁ * c₂) M ε s t) fun s hs => ?_
    exact integrable_Wm_of_cont (C := M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪 * (c₁ * c₂))).card * Kt)
      (A := AR) (continuous_Thrp hM (mem_Srow.1 hs).1.1 hε2)
      (fun t => (hThb _ _ (mem_Srow.1 hs).1.1 t).trans (le_of_eq (by ring)))
  -- the pair sum as one finite sum of line integrals
  set cond : Ideal (𝓞 F) × Ideal (𝓞 F) → Prop := fun p => p.1 ⊔ p.2 = ⊤ ∧ ¬ (p.1 = ⊤ ∧ p.2 = ⊤)
  set wp : Ideal (𝓞 F) × Ideal (𝓞 F) → ℂ := fun p =>
    if cond p then z p.1 * starRingEnd ℂ (z p.2) * (1 / (2 * π) : ℂ) else 0
  have hPS : PSnp C z (fun c₁ c₂ => RPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L ε) =
      ∑ p ∈ C ×ˢ C, wp p * ∫ t : ℝ, Wm (ε + t * I) * Φ p t := by
    rw [PSnp, Finset.sum_product]
    refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
    simp only [wp, cond, hRPt]
    split_ifs <;> ring
  rw [hPS]
  set e : ℝ → Ideal (𝓞 F) → ℂ := fun t c =>
    ∏ P ∈ primesOf c, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * w t)))
  set Kq : ℝ → ℂ := fun t => (M : ℂ) ^ w t *
    (∏ P ∈ primesOf (𝔤 * 𝔪), (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * w t)))) *
    (R0 F (2 * w t) / (2 * w t - 1))
  have hpair : ∀ t, ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ⊔ c₂ = ⊤ → Φ (c₁, c₂) t =
      Kq t * (e t c₁ * e t c₂ * ∑ s ∈ Srow 𝔪 𝔤 L, (Ideal.absNorm s : ℂ) ^ (-w t) *
        (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂)) := by
    intro t c₁ hc₁ c₂ hc₂ h12
    have h1 := (L3H.mem_rowsF_zero.1 (hCr c₁ hc₁)).1.1
    have h2 := (L3H.mem_rowsF_zero.1 (hCr c₂ hc₂)).1.1
    have hX₁ : 𝔤 * 𝔪 ⊔ c₁ = ⊤ := by rw [sup_comm]; exact hC c₁ hc₁
    have hX₂ : 𝔤 * 𝔪 ⊔ c₂ = ⊤ := by rw [sup_comm]; exact hC c₂ hc₂
    simp only [hΦ, Thrp, Kq, e, psiP_apply]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_primes_split hq0 h1 h2 hX₁ hX₂ h12, cpow_div' (Nat.cast_nonneg _) hM]
    simp only [hw]
    push_cast
    ring
  have hB : ∀ t : ℝ, ‖∑ p ∈ C ×ˢ C, wp p * Φ p t‖ ≤
      ((1 / (2 * π)) * Kt * 2 * (M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪)).card * β * Ztau C z)) *
        (1 + |t|) ^ AR := by
    intro t
    have hsum : ∑ p ∈ C ×ˢ C, wp p * Φ p t = (1 / (2 * π) : ℂ) * Kq t *
        ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
          (z c₁ * e t c₁) * (starRingEnd ℂ (z c₂) * e t c₂) *
            ∑ s ∈ Srow 𝔪 𝔤 L, (Ideal.absNorm s : ℂ) ^ (-w t) *
              (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂) else 0) := by
      rw [Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c₁ hc₁ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c₂ hc₂ => ?_
      simp only [wp, cond]
      split_ifs with h
      · rw [hpair t c₁ hc₁ c₂ hc₂ h.1]; ring
      · ring
    rw [hsum, norm_mul, norm_mul]
    have hbil := bil_np (𝔪 := 𝔪) (L3H.chiK ι 𝔪 g) (Srow 𝔪 𝔤 L) C Cmax hCr hβ zero_le_one hS
      (fun s => (Ideal.absNorm s : ℂ) ^ (-w t)) (fun s hs => norm_natCast_cpow_neg_le_one
        (Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (mem_Srow.1 hs).1.1))
        (by rw [hwre]; exact hε.le))
      (fun c => z c * e t c) (fun c => starRingEnd ℂ (z c) * e t c)
    have he : ∀ c, ‖e t c‖ ≤ (2 : ℝ) ^ (L3H.pf c).card := fun c =>
      norm_e_le c (u := 2 * w t) (by simp [hwre]; linarith)
    have hu := tau_e_le C z (e t) he
    have hv := tau_e_le C (fun c => starRingEnd ℂ (z c)) (e t) he
    have hZ : Ztau C (fun c => starRingEnd ℂ (z c)) = Ztau C z := by
      simp [Ztau, Complex.norm_conj]
    rw [hZ] at hv
    have hsq := sqrt_mul_sqrt_le_of_le (by positivity) (by positivity) hu hv
    have hKq : ‖Kq t‖ ≤ M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪)).card * (Kt * (1 + |t|) ^ AR) := by
      simp only [Kq, norm_mul]
      have e1 : ‖(M : ℂ) ^ w t‖ = M ^ ε := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hM, hwre]
      rw [e1]
      gcongr
      · exact norm_prod_one_sub_le (𝔤 * 𝔪) (by simp [hwre]; linarith)
      · exact hR0line t
    have hpi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hpi]
    have hZ0 : 0 ≤ Ztau C z := Finset.sum_nonneg fun _ _ => by positivity
    calc 1 / (2 * π) * ‖Kq t‖ * ‖∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
          (z c₁ * e t c₁) * (starRingEnd ℂ (z c₂) * e t c₂) *
            ∑ s ∈ Srow 𝔪 𝔤 L, (Ideal.absNorm s : ℂ) ^ (-w t) *
              (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂) else 0)‖
        ≤ 1 / (2 * π) * (M ^ ε * 2 ^ (primesOf (𝔤 * 𝔪)).card * (Kt * (1 + |t|) ^ AR)) *
          (2 * 1 * β * Ztau C z) := by
          gcongr
          refine hbil.trans ?_
          rw [mul_assoc (2 * 1 * β)]
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  refine (norm_sum_integral_le (C ×ˢ C) wp Φ (fun p _ => hΦc p) (fun p _ => hΦb p) hB).trans
    (le_of_eq ?_)
  ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PDP: the error term `DP` summed over pairs

On `Re w = 1 − ε′`: `HP = Kc(w) ∑_{e ⊆ primes(𝔤)} (−1)^{|e|} N(e)^{-w} u_e(c₁) u_e(c₂) ∑_s N s^{w−1} χ χ`,
`u_e(c) = χ_c(e) N c^{1/2 − w} ∏_{P ∣ c}(1 − NP^{-2(1−w)})`; then the bilinear bound.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-- The pair-independent part of the `DP` integrand. -/
noncomputable def Kc (𝔪 : Ideal (𝓞 F)) (M : ℝ) (w : ℂ) : ℂ :=
  (M : ℂ) ^ w * (∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-w))) *
    (((|discr F| : ℤ) : ℝ) : ℂ) ^ (1 / 2 - w) * G0 w ^ InfinitePlace.nrComplexPlaces F *
    Zm 𝔪 (1 - w) * (∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * (1 - w))))) *
    (R0 F (2 * (1 - w)) / (1 - 2 * w))

/-- The column factor `∏_{P ∣ c}(1 − NP^{-2(1−w)})`. -/
noncomputable def eD (w : ℂ) (c : Ideal (𝓞 F)) : ℂ :=
  ∏ P ∈ primesOf c, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * (1 - w))))

lemma Dc_mul_cpow {c₁ c₂ : Ideal (𝓞 F)} (z : ℂ) :
    Dc (c₁ * c₂) ^ z = (((|discr F| : ℤ) : ℝ) : ℂ) ^ z * (Ideal.absNorm c₁ : ℂ) ^ z *
      (Ideal.absNorm c₂ : ℂ) ^ z := by
  rw [Dc_eq, map_mul, Nat.cast_mul, ← mul_assoc]
  have h0 : (0 : ℝ) ≤ ((|discr F| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (discr F)
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (Nat.cast_nonneg _),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h0 (Nat.cast_nonneg _)]
  push_cast; ring

theorem HP_pair_eq {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (hψ0 : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      PsiHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂))
    (h𝔪 : 𝔪 ≠ ⊥) {𝔤 c₁ c₂ : Ideal (𝓞 F)} (hc₁ : IsExterior 𝔪 c₁) (hc₂ : IsExterior 𝔪 c₂)
    (h12 : c₁ ⊔ c₂ = ⊤) (M L' : ℝ) (w : ℂ) :
    HP 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' w = Kc 𝔪 M w *
      ∑ e ∈ (primesOf 𝔤).powerset, (-1 : ℂ) ^ e.card *
        (Ideal.absNorm (pideal e) : ℂ) ^ (-w) *
        ((L3H.chiK ι 𝔪 g (pideal e) c₁ * (Ideal.absNorm c₁ : ℂ) ^ (1 / 2 - w) * eD w c₁) *
          (L3H.chiK ι 𝔪 g (pideal e) c₂ * (Ideal.absNorm c₂ : ℂ) ^ (1 / 2 - w) * eD w c₂) *
          ∑ s ∈ L3H.rowsF 𝔪 0 L', (Ideal.absNorm s : ℂ) ^ (-(1 - w)) *
            (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂)) := by
  have hψ : PsiHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂) := hψ0 c₁ c₂ hc₁ hc₂
  have hE : ∏ P ∈ primesOf 𝔤, (1 - psiP g c₁ c₂ P * (Ideal.absNorm P : ℂ) ^ (-w)) =
      ∑ e ∈ (primesOf 𝔤).powerset, (-1 : ℂ) ^ e.card *
        (psiP g c₁ c₂ (pideal e) * (Ideal.absNorm (pideal e) : ℂ) ^ (-w)) := by
    rw [prod_one_sub_expand]
    refine sum_congr rfl fun e he => ?_
    rw [mem_powerset] at he
    rw [psi_pideal hψ he, absNorm_pideal_cpow, ← prod_mul_distrib]
  have hX₁ : 𝔪 ⊔ c₁ = ⊤ := by rw [sup_comm]; exact hc₁.2
  have hX₂ : 𝔪 ⊔ c₂ = ⊤ := by rw [sup_comm]; exact hc₂.2
  have hsplit := prod_primes_split h𝔪 hc₁.1 hc₂.1 hX₁ hX₂ h12
    (fun P => 1 - (Ideal.absNorm P : ℂ) ^ (-(2 * (1 - w))))
  unfold HP Kd Em eD Kc
  rw [Pf_def]
  rw [hE, hsplit, Dc_mul_cpow]
  simp only [psiP_apply, mul_sum, sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun e _ => sum_congr rfl fun s _ => ?_
  ring

lemma tau_e_le_K (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ) (e : Ideal (𝓞 F) → ℂ) {K : ℝ}
    (hK : 0 ≤ K) (he : ∀ c ∈ C, ‖e c‖ ≤ K * (2 : ℝ) ^ (L3H.pf c).card) :
    ∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖z c * e c‖ ^ 2 ≤ K ^ 2 * Ztau C z := by
  rw [Ztau_def]
  rw [mul_sum]
  refine sum_le_sum fun c hc => ?_
  rw [norm_mul, mul_pow]
  have h1 : ‖e c‖ ^ 2 ≤ (K * (2 : ℝ) ^ (L3H.pf c).card) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (he c hc) 2
  have h8 : (8 : ℝ) ^ (L3H.pf c).card = 2 ^ (L3H.pf c).card * ((2 : ℝ) ^ (L3H.pf c).card) ^ 2 := by
    rw [← pow_mul, ← pow_add, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]; ring_nf
  rw [h8]
  calc (2 : ℝ) ^ (L3H.pf c).card * (‖z c‖ ^ 2 * ‖e c‖ ^ 2)
      ≤ 2 ^ (L3H.pf c).card * (‖z c‖ ^ 2 * (K * (2 : ℝ) ^ (L3H.pf c).card) ^ 2) := by gcongr
    _ = _ := by ring

lemma continuous_line_of_diffOn {f : ℂ → ℂ} {σ : ℝ}
    (hf : DifferentiableOn ℂ f {s | σ ≤ s.re ∧ s.re ≤ σ}) :
    Continuous fun t : ℝ => f (σ + t * I) := by
  refine hf.continuousOn.comp_continuous (by fun_prop) fun t => ?_
  simp

lemma norm_mul7_le {a b c d e f g : ℂ} {A B C D E G H : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) (hf : ‖f‖ ≤ G) (hg : ‖g‖ ≤ H) :
    ‖a * b * c * d * e * f * g‖ ≤ A * B * C * D * E * G * H := by
  simp only [norm_mul]
  have hA := (norm_nonneg a).trans ha
  have hB := (norm_nonneg b).trans hb
  have hC := (norm_nonneg c).trans hc
  have hD := (norm_nonneg d).trans hd
  have hE := (norm_nonneg e).trans he
  have hG := (norm_nonneg f).trans hf
  gcongr

/-- The `DP` term summed over pairs. -/
theorem PS_DP_le {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (hψ0 : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      PsiHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂))
    (h𝔪 : 𝔪 ≠ ⊥) {ε' : ℝ} (hε' : 0 < ε') (hε'2 : ε' < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) {M L' β Cmin : ℝ}, 0 < M → 0 ≤ β → 0 < Cmin →
      (∀ c ∈ C, Cmin ≤ (Ideal.absNorm c : ℝ)) →
      L3H.SBf (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 L') C β →
        ‖PSnp C z (fun c₁ c₂ => DPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' ε')‖ ≤
          K * M ^ (1 - ε') * 2 ^ (primesOf 𝔤).card * β * Cmin ^ (-(1 - 2 * ε')) *
            Ztau C z := by
  classical
  set b : ℝ := 1 - ε' with hb
  have hb1 : b < 1 := by linarith
  set r := InfinitePlace.nrComplexPlaces F
  obtain ⟨CG, AG, hCG, hAG, hG⟩ := G0_bound b b hb1
  obtain ⟨CR, AR, hCR, hAR, hRb⟩ := R0_bound F 2
  have h2e : (2 : ℝ) ^ (-ε') < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set Zb : ℝ := ((1 - (2 : ℝ) ^ (-ε')) ^ (primesOf 𝔪).card)⁻¹ with hZb
  have hZb0 : 0 ≤ Zb := inv_nonneg.2 (pow_nonneg (by linarith) _)
  set dd : ℝ := ((|discr F| : ℤ) : ℝ) ^ (ε' - 1 / 2) with hdd
  have hd1 : (1 : ℝ) ≤ ((|discr F| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero F
    exact_mod_cast Int.one_le_abs this
  have h12 : 0 < 1 - 2 * ε' := by linarith
  set Kk : ℝ := 2 ^ (primesOf 𝔪).card * dd * CG ^ r * Zb * 2 ^ (primesOf 𝔪).card *
    (CR * 2 ^ AR / (1 - 2 * ε')) with hKk
  have hKk0 : 0 ≤ Kk := by positivity
  set AK : ℝ := AG * r + AR with hAK
  refine ⟨(1 / (2 * π)) * Kk * 2 * IW b AK, by
    have := IW_nonneg b AK; have := Real.pi_pos; positivity, ?_⟩
  intro 𝔤 C Cmax hCr z M L' β Cmin hM hβ hCmin hCN hS
  set w : ℝ → ℂ := fun t => (b : ℂ) + t * I with hw
  have hwre : ∀ t, (w t).re = b := fun t => by simp [hw]
  have hwim : ∀ t, (w t).im = t := fun t => by simp [hw]
  -- the pair-independent factor
  have hKc : ∀ t, ‖Kc 𝔪 M (w t)‖ ≤ M ^ (1 - ε') * (Kk * (1 + |t|) ^ AK) := by
    intro t
    have e1 : ‖(M : ℂ) ^ w t‖ ≤ M ^ (1 - ε') := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hM, hwre]
    have e2 : ‖∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-w t))‖ ≤ 2 ^ (primesOf 𝔪).card :=
      norm_prod_one_sub_le 𝔪 (by rw [hwre]; linarith)
    have e3 : ‖(((|discr F| : ℤ) : ℝ) : ℂ) ^ (1 / 2 - w t)‖ ≤ dd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      apply le_of_eq; congr 1; simp [hwre, hb]; ring
    have e4 : ‖G0 (w t) ^ r‖ ≤ CG ^ r * (1 + |t|) ^ (AG * r) := by
      rw [norm_pow]
      have h := hG (w t) (by rw [hwre]) (by rw [hwre])
      rw [hwim] at h
      calc ‖G0 (w t)‖ ^ r ≤ (CG * (1 + |t|) ^ AG) ^ r := pow_le_pow_left₀ (norm_nonneg _) h r
        _ = CG ^ r * (1 + |t|) ^ (AG * r) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + |t|) ^ AG), ← Real.rpow_mul (by positivity)]
    have e5 : ‖Zm 𝔪 (1 - w t)‖ ≤ Zb := norm_Zm_le 𝔪 hε' (by simp [hwre, hb])
    have e6 : ‖∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * (1 - w t))))‖ ≤
        2 ^ (primesOf 𝔪).card := norm_prod_one_sub_le 𝔪 (by simp [hwre, hb]; linarith)
    have e7 : ‖R0 F (2 * (1 - w t)) / (1 - 2 * w t)‖ ≤ CR * 2 ^ AR / (1 - 2 * ε') *
        (1 + |t|) ^ AR := by
      have hden : 1 - 2 * ε' ≤ ‖1 - 2 * w t‖ := by
        refine le_trans ?_ (Complex.abs_re_le_norm _)
        simp only [sub_re, one_re, mul_re, hwre, hb]; norm_num
        rw [abs_of_neg (by linarith)]; linarith
      have hR := hRb (2 * (1 - w t)) (by simp [hwre, hb]; linarith) (by simp [hwre, hb]; linarith)
      have him : |(2 * (1 - w t)).im| = 2 * |t| := by simp [hwim, abs_mul]
      rw [him] at hR
      have e4' : (1 + 2 * |t|) ^ AR ≤ 2 ^ AR * (1 + |t|) ^ AR := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hAR
      rw [norm_div, div_le_iff₀ (lt_of_lt_of_le h12 hden)]
      calc ‖R0 F (2 * (1 - w t))‖ ≤ CR * (2 ^ AR * (1 + |t|) ^ AR) := hR.trans (by gcongr)
        _ = CR * 2 ^ AR / (1 - 2 * ε') * (1 + |t|) ^ AR * (1 - 2 * ε') := by field_simp
        _ ≤ CR * 2 ^ AR / (1 - 2 * ε') * (1 + |t|) ^ AR * ‖1 - 2 * w t‖ := by gcongr
    have := norm_mul7_le e1 e2 e3 e4 e5 e6 e7
    refine (le_of_eq_of_le (by rfl) this).trans (le_of_eq ?_)
    rw [hKk, hAK, Real.rpow_add (by positivity)]
    ring
  -- the pair integrands
  set Φ : Ideal (𝓞 F) × Ideal (𝓞 F) → ℝ → ℂ := fun p t =>
    HP 𝔪 𝔤 (p.1 * p.2) (psiP g p.1 p.2) M L' (w t) with hΦ
  have hpsi1 : ∀ c₁ c₂ s, ‖psiP g c₁ c₂ s‖ ≤ 1 := by
    intro c₁ c₂ s
    simp only [psiP_apply, L3H.chiK, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _)) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _))
  have hne2 : ∀ t, 1 - 2 * w t ≠ 0 := by
    intro t h; have := congrArg Complex.re h; simp [hwre, hb] at this; linarith
  have hΦc : ∀ p ∈ C ×ˢ C, Continuous (Φ p) := by
    intro p hp
    rw [Finset.mem_product] at hp
    have h0 : p.1 * p.2 ≠ ⊥ := by
      rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
      exact ⟨by rw [Ideal.zero_eq_bot]; exact (L3H.mem_rowsF_zero.1 (hCr _ hp.1)).1.1,
        by rw [Ideal.zero_eq_bot]; exact (L3H.mem_rowsF_zero.1 (hCr _ hp.2)).1.1⟩
    simp only [hΦ, HP]
    refine ((continuous_line_of_diffOn (σ := b) (differentiableOn_Kd 𝔪 𝔤 _ h0 hM hb1)).mul
      (((R0_diff F).continuous.comp (by fun_prop)).div (by fun_prop) hne2)).mul
      ((differentiable_Pf 𝔪 _ L').continuous.comp (by fun_prop))
  have hΦb : ∀ p ∈ C ×ˢ C, ∃ C₀ A' : ℝ, ∀ t, ‖Φ p t‖ ≤ C₀ * (1 + |t|) ^ A' := by
    intro p hp
    rw [Finset.mem_product] at hp
    have h0 : p.1 * p.2 ≠ ⊥ := by
      rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
      exact ⟨by rw [Ideal.zero_eq_bot]; exact (L3H.mem_rowsF_zero.1 (hCr _ hp.1)).1.1,
        by rw [Ideal.zero_eq_bot]; exact (L3H.mem_rowsF_zero.1 (hCr _ hp.2)).1.1⟩
    obtain ⟨C₁, A₁, hC₁, hA₁, h₁⟩ := (((PolyB_Kd 𝔪 𝔤 (hpsi1 p.1 p.2) h0 hM b b hb1).mul
      (PolyB_R0 (F := F) b b (by rw [hb]; linarith))).mul
      (PolyB_Pf 𝔪 (hpsi1 p.1 p.2) L' b b hb1.le))
    refine ⟨C₁ * (1 / (1 - 2 * ε')), A₁, fun t => ?_⟩
    have hden : 1 - 2 * ε' ≤ ‖1 - 2 * w t‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      simp only [sub_re, one_re, mul_re, hwre, hb]; norm_num
      rw [abs_of_neg (by linarith)]; linarith
    have hb' := h₁ (w t) (by rw [hwre]) (by rw [hwre])
    rw [hwim] at hb'
    simp only [hΦ, HP]
    rw [show Kd 𝔪 𝔤 (p.1 * p.2) (psiP g p.1 p.2) M (w t) * (R0 F (2 * (1 - w t)) / (1 - 2 * w t)) *
        Pf 𝔪 (psiP g p.1 p.2) L' (1 - w t) = (Kd 𝔪 𝔤 (p.1 * p.2) (psiP g p.1 p.2) M (w t) *
          R0 F (2 * (1 - w t)) * Pf 𝔪 (psiP g p.1 p.2) L' (1 - w t)) * (1 - 2 * w t)⁻¹ by
      field_simp]
    rw [norm_mul, norm_inv]
    have hinv : ‖1 - 2 * w t‖⁻¹ ≤ 1 / (1 - 2 * ε') := by
      rw [one_div]; exact inv_anti₀ h12 hden
    calc _ ≤ C₁ * (1 + |t|) ^ A₁ * (1 / (1 - 2 * ε')) :=
          mul_le_mul hb' hinv (by positivity) (by positivity)
      _ = _ := by ring
  have hDPt : ∀ c₁ c₂, DPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' ε' =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (b + t * I) * Φ (c₁, c₂) t := by
    intro c₁ c₂; rfl
  set cond : Ideal (𝓞 F) × Ideal (𝓞 F) → Prop := fun p => p.1 ⊔ p.2 = ⊤ ∧ ¬ (p.1 = ⊤ ∧ p.2 = ⊤)
  set wp : Ideal (𝓞 F) × Ideal (𝓞 F) → ℂ := fun p =>
    if cond p then z p.1 * starRingEnd ℂ (z p.2) * (1 / (2 * π) : ℂ) else 0
  have hPS : PSnp C z (fun c₁ c₂ => DPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' ε') =
      ∑ p ∈ C ×ˢ C, wp p * ∫ t : ℝ, Wm (b + t * I) * Φ p t := by
    rw [PSnp, Finset.sum_product]
    refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
    simp only [wp, cond, hDPt]
    split_ifs <;> ring
  rw [hPS]
  set Kz : ℝ := Cmin ^ (ε' - 1 / 2) with hKz
  have hKz0 : 0 ≤ Kz := by positivity
  set ue : ℝ → Finset (Ideal (𝓞 F)) → Ideal (𝓞 F) → ℂ := fun t e c =>
    L3H.chiK ι 𝔪 g (pideal e) c * (Ideal.absNorm c : ℂ) ^ (1 / 2 - w t) * eD (w t) c
  set Sbil : ℝ → Finset (Ideal (𝓞 F)) → ℂ := fun t e =>
    ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
      (z c₁ * ue t e c₁) * (starRingEnd ℂ (z c₂) * ue t e c₂) *
        ∑ s ∈ L3H.rowsF 𝔪 0 L', (Ideal.absNorm s : ℂ) ^ (-(1 - w t)) *
          (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂) else 0)
  have hsum : ∀ t, ∑ p ∈ C ×ˢ C, wp p * Φ p t = (1 / (2 * π) : ℂ) * Kc 𝔪 M (w t) *
      ∑ e ∈ (primesOf 𝔤).powerset, ((-1 : ℂ) ^ e.card * (Ideal.absNorm (pideal e) : ℂ) ^ (-w t)) *
        Sbil t e := by
    intro t
    rw [Finset.sum_product]
    have hR : (1 / (2 * π) : ℂ) * Kc 𝔪 M (w t) *
        ∑ e ∈ (primesOf 𝔤).powerset, ((-1 : ℂ) ^ e.card * (Ideal.absNorm (pideal e) : ℂ) ^ (-w t)) *
          Sbil t e = ∑ c₁ ∈ C, ∑ c₂ ∈ C, ∑ e ∈ (primesOf 𝔤).powerset,
            (1 / (2 * π) : ℂ) * Kc 𝔪 M (w t) * (((-1 : ℂ) ^ e.card *
              (Ideal.absNorm (pideal e) : ℂ) ^ (-w t)) *
              (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
                (z c₁ * ue t e c₁) * (starRingEnd ℂ (z c₂) * ue t e c₂) *
                  ∑ s ∈ L3H.rowsF 𝔪 0 L', (Ideal.absNorm s : ℂ) ^ (-(1 - w t)) *
                    (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂) else 0)) := by
      simp only [Sbil, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c₁ _ => ?_
      rw [Finset.sum_comm]
    rw [hR]
    refine Finset.sum_congr rfl fun c₁ hc₁ => Finset.sum_congr rfl fun c₂ hc₂ => ?_
    simp only [wp, cond]
    split_ifs with h
    · rw [hΦ]; dsimp only
      rw [HP_pair_eq g hψ0 h𝔪 (L3H.mem_rowsF_zero.1 (hCr c₁ hc₁)).1
        (L3H.mem_rowsF_zero.1 (hCr c₂ hc₂)).1 h.1, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [ue]; ring
    · simp
  have hue : ∀ t e, ∀ c ∈ C, ‖ue t e c‖ ≤ Kz * (2 : ℝ) ^ (L3H.pf c).card := by
    intro t e c hc
    have hc1 : (1 : ℝ) ≤ Ideal.absNorm c := L3H.one_le_absNorm (L3H.mem_rowsF_zero.1 (hCr c hc)).1.1
    simp only [ue, norm_mul]
    have e1 : ‖L3H.chiK ι 𝔪 g (pideal e) c‖ ≤ 1 := by
      simp only [L3H.chiK, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _)
    have e2 : ‖(Ideal.absNorm c : ℂ) ^ (1 / 2 - w t)‖ ≤ Kz := by
      rw [show ((Ideal.absNorm c : ℂ)) = ((Ideal.absNorm c : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      have : (1 / 2 - w t).re = ε' - 1 / 2 := by simp [hwre, hb]; ring
      rw [this, hKz]
      exact Real.rpow_le_rpow_of_nonpos hCmin (hCN c hc) (by linarith)
    have e3 : ‖eD (w t) c‖ ≤ (2 : ℝ) ^ (L3H.pf c).card :=
      norm_e_le c (u := 2 * (1 - w t)) (by simp [hwre, hb]; linarith)
    calc ‖L3H.chiK ι 𝔪 g (pideal e) c‖ * ‖(Ideal.absNorm c : ℂ) ^ (1 / 2 - w t)‖ * ‖eD (w t) c‖
        ≤ 1 * Kz * (2 : ℝ) ^ (L3H.pf c).card := by gcongr
      _ = _ := by ring
  have hrow1 : ∀ s ∈ L3H.rowsF 𝔪 0 L', 1 ≤ Ideal.absNorm s := by
    intro s hs
    have h0 := (L3H.mem_rowsF_zero.1 hs).1.1
    exact Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0)
  have hSb : ∀ t e, ‖Sbil t e‖ ≤ 2 * β * (Kz ^ 2 * Ztau C z) := by
    intro t e
    have hbil := bil_np (𝔪 := 𝔪) (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 L') C Cmax hCr hβ zero_le_one hS
      (fun s => (Ideal.absNorm s : ℂ) ^ (-(1 - w t))) (fun s hs => norm_natCast_cpow_neg_le_one
        (hrow1 s hs) (by simp [hwre, hb]; linarith))
      (fun c => z c * ue t e c) (fun c => starRingEnd ℂ (z c) * ue t e c)
    have hu := tau_e_le_K C z (ue t e) hKz0 (hue t e)
    have hv := tau_e_le_K C (fun c => starRingEnd ℂ (z c)) (ue t e) hKz0 (hue t e)
    have hZ : Ztau C (fun c => starRingEnd ℂ (z c)) = Ztau C z := by simp [Ztau]
    rw [hZ] at hv
    have hsq := sqrt_mul_sqrt_le_of_le (by positivity) (by positivity) hu hv
    refine hbil.trans ?_
    rw [mul_assoc (2 * 1 * β)]
    refine (mul_le_mul_of_nonneg_left hsq (by positivity)).trans (le_of_eq ?_)
    ring
  have hZ0 : 0 ≤ Ztau C z := Finset.sum_nonneg fun _ _ => by positivity
  have hB : ∀ t : ℝ, ‖∑ p ∈ C ×ˢ C, wp p * Φ p t‖ ≤
      ((1 / (2 * π)) * Kk * 2 * (M ^ (1 - ε') * 2 ^ (primesOf 𝔤).card * β *
        Cmin ^ (-(1 - 2 * ε')) * Ztau C z)) * (1 + |t|) ^ AK := by
    intro t
    rw [hsum t, norm_mul, norm_mul]
    have hpi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hpi]
    have hesum : ‖∑ e ∈ (primesOf 𝔤).powerset, ((-1 : ℂ) ^ e.card *
        (Ideal.absNorm (pideal e) : ℂ) ^ (-w t)) * Sbil t e‖ ≤
        2 ^ (primesOf 𝔤).card * (2 * β * (Kz ^ 2 * Ztau C z)) := by
      refine (norm_sum_le _ _).trans ?_
      have hcard : (((primesOf 𝔤).powerset.card : ℕ) : ℝ) = 2 ^ (primesOf 𝔤).card := by
        rw [Finset.card_powerset]; push_cast; ring
      rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun e he => ?_
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      have hN : ‖(Ideal.absNorm (pideal e) : ℂ) ^ (-w t)‖ ≤ 1 := by
        rw [Finset.mem_powerset] at he
        exact norm_natCast_cpow_neg_le_one (Nat.one_le_iff_ne_zero.2 (by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact pideal_ne_bot he)) (by rw [hwre]; linarith)
      calc ‖(Ideal.absNorm (pideal e) : ℂ) ^ (-w t)‖ * ‖Sbil t e‖ ≤ 1 * (2 * β * (Kz ^ 2 * Ztau C z)) :=
            mul_le_mul hN (hSb t e) (norm_nonneg _) zero_le_one
        _ = _ := by ring
    have hKz2 : Kz ^ 2 = Cmin ^ (-(1 - 2 * ε')) := by
      rw [hKz, ← Real.rpow_natCast, ← Real.rpow_mul hCmin.le]; congr 1; push_cast; ring
    rw [hKz2] at hesum
    generalize (∑ e ∈ (primesOf 𝔤).powerset, ((-1 : ℂ) ^ e.card *
          (Ideal.absNorm (pideal e) : ℂ) ^ (-w t)) * Sbil t e) = SS at hesum ⊢
    calc 1 / (2 * π) * ‖Kc 𝔪 M (w t)‖ * ‖SS‖
        ≤ 1 / (2 * π) * (M ^ (1 - ε') * (Kk * (1 + |t|) ^ AK)) *
          (2 ^ (primesOf 𝔤).card * (2 * β * (Cmin ^ (-(1 - 2 * ε')) * Ztau C z))) := by
          have hpi0 : (0 : ℝ) ≤ 1 / (2 * π) := by have := Real.pi_pos; positivity
          have hM0 : (0 : ℝ) ≤ M ^ (1 - ε') := Real.rpow_nonneg hM.le _
          have ht0 : (0 : ℝ) ≤ (1 + |t|) ^ AK := Real.rpow_nonneg (by positivity) _
          have hnn : 0 ≤ 1 / (2 * π) * (M ^ (1 - ε') * (Kk * (1 + |t|) ^ AK)) :=
            mul_nonneg hpi0 (mul_nonneg hM0 (mul_nonneg hKk0 ht0))
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hKc t) hpi0) hesum (norm_nonneg _) hnn
      _ = _ := by ring
  refine (norm_sum_integral_le (C ×ˢ C) wp Φ hΦc hΦb hB).trans (le_of_eq ?_)
  ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Dy: dyadic decomposition of rows with weight `N s^{-1/2}`

`bil_dyadic`: for row weights supported on `Y₀ < N s ≤ Y₁` with `|a(s)| ≤ N s^{-1/2}`, the pair sum is
at most `nblk · 2 Bm √U √V`, where `Bm` bounds `(2^k Y₀)^{-1/2} β(2^{k+1} Y₀)` on the blocks and
`nblk = clog₂ ⌈Y₁/Y₀⌉ ≤ (2(Y₁/Y₀ + 1))^δ / (δ log 2)`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Finset

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma nblk_top {Y₀ Y₁ : ℝ} (hY₀ : 0 < Y₀) : Y₁ ≤ 2 ^ nblk Y₀ Y₁ * Y₀ := by
  have h1 : Y₁ / Y₀ ≤ (⌈Y₁ / Y₀⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈Y₁ / Y₀⌉₊ : ℝ) ≤ (2 : ℝ) ^ nblk Y₀ Y₁ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  rw [div_le_iff₀ hY₀] at h1
  nlinarith

lemma nblk_cover {Y₀ Y₁ x : ℝ} (hY₀ : 0 < Y₀) (h1 : Y₀ < x) (h2 : x ≤ Y₁) :
    ∃ k < nblk Y₀ Y₁, 2 ^ k * Y₀ < x ∧ x ≤ 2 ^ (k + 1) * Y₀ := by
  classical
  have hex : ∃ k, x ≤ 2 ^ k * Y₀ := ⟨nblk Y₀ Y₁, h2.trans (nblk_top hY₀)⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀s : x ≤ 2 ^ k₀ * Y₀ := Nat.find_spec hex
  have hk₀0 : k₀ ≠ 0 := by
    intro h; rw [h, pow_zero, one_mul] at hk₀s; linarith
  have hk₀K : k₀ ≤ nblk Y₀ Y₁ := Nat.find_min' hex (h2.trans (nblk_top hY₀))
  refine ⟨k₀ - 1, by omega, ?_, ?_⟩
  · have := Nat.find_min hex (show k₀ - 1 < k₀ by omega)
    push Not at this; exact this
  · rwa [show k₀ - 1 + 1 = k₀ by omega]

open Classical in
theorem bil_dyadic {𝔪 : Ideal (𝓞 F)} (χ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (R C : Finset (Ideal (𝓞 F))) (Cmax : ℝ) (hC : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax)
    {Y₀ Y₁ : ℝ} (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y₁) (βf : ℝ → ℝ) (hβf : ∀ Y, 0 ≤ βf Y)
    (hS : ∀ Y, L3H.SBf χ (R.filter (fun s => (Ideal.absNorm s : ℝ) ≤ Y)) C (βf Y))
    (a : Ideal (𝓞 F) → ℂ)
    (ha : ∀ s ∈ R, a s ≠ 0 → Y₀ < (Ideal.absNorm s : ℝ) ∧ (Ideal.absNorm s : ℝ) ≤ Y₁)
    (ha' : ∀ s ∈ R, ‖a s‖ ≤ (Ideal.absNorm s : ℝ) ^ (-(1 / 2 : ℝ))) {Bm : ℝ}
    (hBm : ∀ k : ℕ, 2 ^ k * Y₀ ≤ 2 * Y₁ → (2 ^ k * Y₀) ^ (-(1 / 2 : ℝ)) * βf (2 ^ (k + 1) * Y₀) ≤ Bm)
    (u v : Ideal (𝓞 F) → ℂ) :
    ‖∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
        u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0)‖ ≤
      nblk Y₀ Y₁ * (2 * Bm * Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖u c‖ ^ 2) *
        Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖v c‖ ^ 2)) := by
  set K := nblk Y₀ Y₁
  set blk : ℕ → ℝ → Prop := fun k x => 2 ^ k * Y₀ < x ∧ x ≤ 2 ^ (k + 1) * Y₀
  set ak : ℕ → Ideal (𝓞 F) → ℂ := fun k s => if blk k (Ideal.absNorm s : ℝ) then a s else 0
  -- `a = ∑_k a_k` on the rows
  have hdisj : ∀ x : ℝ, ∀ k k', blk k x → blk k' x → k = k' := by
    intro x k k' h h'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ k' := pow_le_pow_right₀ (by norm_num) hl
      have := h.2.trans (mul_le_mul_of_nonneg_right this hY₀.le)
      linarith [h'.1]
    · have : (2 : ℝ) ^ (k' + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hl
      have := h'.2.trans (mul_le_mul_of_nonneg_right this hY₀.le)
      linarith [h.1]
  have hsplit : ∀ s ∈ R, a s = ∑ k ∈ Finset.range K, ak k s := by
    intro s hs
    by_cases h0 : a s = 0
    · simp [ak, h0]
    · obtain ⟨k, hk, hb⟩ := nblk_cover hY₀ (ha s hs h0).1 (ha s hs h0).2
      rw [Finset.sum_eq_single k]
      · simp only [ak]; rw [if_pos hb]
      · intro k' _ hk'
        simp only [ak]
        rw [if_neg]
        intro hb'
        exact hk' (hdisj _ _ _ hb' hb)
      · intro h; exact absurd (Finset.mem_range.2 hk) h
  set Rk : ℕ → Finset (Ideal (𝓞 F)) := fun k =>
    R.filter (fun s => (Ideal.absNorm s : ℝ) ≤ 2 ^ (k + 1) * Y₀)
  have hrow : ∀ X : Ideal (𝓞 F) → ℂ, ∑ s ∈ R, a s * X s =
      ∑ k ∈ Finset.range K, ∑ s ∈ Rk k, ak k s * X s := by
    intro X
    rw [Finset.sum_congr rfl (fun s hs => by rw [hsplit s hs, Finset.sum_mul]), Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · rfl
    · have : ak k s = 0 := by
        simp only [ak]; rw [if_neg]; intro hb; exact h hb.2
      rw [this, zero_mul]
  have hlin : ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
        u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0) =
      ∑ k ∈ Finset.range K, ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
        u c₁ * v c₂ * ∑ s ∈ Rk k, ak k s * (χ s c₁ * χ s c₂) else 0) := by
    have e : ∀ c₁ c₂, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
        u c₁ * v c₂ * ∑ s ∈ R, a s * (χ s c₁ * χ s c₂) else 0) =
        ∑ k ∈ Finset.range K, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
          u c₁ * v c₂ * ∑ s ∈ Rk k, ak k s * (χ s c₁ * χ s c₂) else 0) := by
      intro c₁ c₂
      split_ifs
      · rw [hrow (fun s => χ s c₁ * χ s c₂), Finset.mul_sum]
      · simp
    simp_rw [e]
    calc _ = ∑ c₁ ∈ C, ∑ k ∈ Finset.range K, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
          u c₁ * v c₂ * ∑ s ∈ Rk k, ak k s * (χ s c₁ * χ s c₂) else 0) :=
          Finset.sum_congr rfl fun c₁ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hlin]
  set U := Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖u c‖ ^ 2)
  set V := Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card * ‖v c‖ ^ 2)
  -- each block
  have hk2 : ∀ k ∈ Finset.range K, 2 ^ k * Y₀ ≤ 2 * Y₁ := by
    intro k hk
    rw [Finset.mem_range] at hk
    set n := ⌈Y₁ / Y₀⌉₊
    have hn : 1 < n := by
      by_contra hn; push Not at hn
      have : K = 0 := Nat.clog_of_right_le_one hn 2
      omega
    have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn
    have h2 : (2 : ℝ) ^ (K - 1) < n := by exact_mod_cast h1
    have h3 : (n : ℝ) < Y₁ / Y₀ + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hY₀.le)
    have h4 : (2 : ℝ) ^ k ≤ 2 ^ (K - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_add_one hY₀.ne', lt_div_iff₀ hY₀] at h3
    nlinarith
  have hblk : ∀ k ∈ Finset.range K, ‖∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
      u c₁ * v c₂ * ∑ s ∈ Rk k, ak k s * (χ s c₁ * χ s c₂) else 0)‖ ≤ 2 * Bm * U * V := by
    intro k hk
    have hA0 : 0 ≤ (2 ^ k * Y₀) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hak : ∀ s ∈ Rk k, ‖ak k s‖ ≤ (2 ^ k * Y₀) ^ (-(1 / 2 : ℝ)) := by
      intro s hs
      simp only [ak]
      split_ifs with hb
      · refine (ha' s (Finset.mem_filter.1 hs).1).trans ?_
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hb.1.le (by norm_num)
      · simpa using hA0
    have h := bil_np χ (Rk k) C Cmax hC (hβf _) hA0 (hS _) (ak k) hak u v
    refine h.trans ?_
    have hb := hBm k (hk2 k hk)
    have hU : 0 ≤ U := Real.sqrt_nonneg _
    have hV : 0 ≤ V := Real.sqrt_nonneg _
    calc 2 * (2 ^ k * Y₀) ^ (-(1 / 2 : ℝ)) * βf (2 ^ (k + 1) * Y₀) * U * V
        = 2 * ((2 ^ k * Y₀) ^ (-(1 / 2 : ℝ)) * βf (2 ^ (k + 1) * Y₀)) * U * V := by ring
      _ ≤ 2 * Bm * U * V := by gcongr
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hblk).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PTT: the main-term difference `T − T′` summed over pairs

The rows run between `L′/N f` and `L` with weight `N s^{-1/2}`; dyadic blocks (`bil_dyadic`).
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma Srow_filter {𝔪 𝔤 : Ideal (𝓞 F)} {Y Y' : ℝ} (h : Y ≤ Y') :
    (Srow 𝔪 𝔤 Y').filter (fun s => (Ideal.absNorm s : ℝ) ≤ Y) = Srow 𝔪 𝔤 Y := by
  ext s
  rw [mem_filter, mem_Srow, mem_Srow]
  constructor
  · rintro ⟨⟨h1, h2, _, h4⟩, h5⟩; exact ⟨h1, h2, h5, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3.trans h, h4⟩, h3⟩

lemma S_diff {𝔪 𝔤 : Ideal (𝓞 F)} (ψ : Ideal (𝓞 F) → ℂ) (Y L : ℝ) :
    (∑ s ∈ Srow 𝔪 𝔤 Y, ψ s * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ))) -
        ∑ s ∈ Srow 𝔪 𝔤 L, ψ s * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ)) =
      ∑ s ∈ Srow 𝔪 𝔤 (max Y L), ((if (Ideal.absNorm s : ℝ) ≤ Y then (1 : ℂ) else 0) -
        (if (Ideal.absNorm s : ℝ) ≤ L then 1 else 0)) * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ)) *
        ψ s := by
  classical
  rw [← Srow_filter (𝔪 := 𝔪) (𝔤 := 𝔤) (le_max_left Y L),
    ← Srow_filter (𝔪 := 𝔪) (𝔤 := 𝔤) (le_max_right Y L), sum_filter, sum_filter,
    ← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

lemma sum_ite_sum_comm {α β : Type*} (C : Finset α) (E : Finset β) (p : α → α → Prop)
    [DecidableRel p] (g : β → α → α → ℂ) :
    ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if p c₁ c₂ then ∑ e ∈ E, g e c₁ c₂ else 0) =
      ∑ e ∈ E, ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if p c₁ c₂ then g e c₁ c₂ else 0) := by
  have h : ∀ c₁ c₂, (if p c₁ c₂ then ∑ e ∈ E, g e c₁ c₂ else 0) =
      ∑ e ∈ E, (if p c₁ c₂ then g e c₁ c₂ else 0) := by
    intro c₁ c₂; split_ifs <;> simp
  simp_rw [h]
  calc _ = ∑ c₁ ∈ C, ∑ e ∈ E, ∑ c₂ ∈ C, (if p c₁ c₂ then g e c₁ c₂ else 0) :=
        sum_congr rfl fun c₁ _ => sum_comm
    _ = _ := sum_comm

/-- The row weights of `T − T′`. -/
noncomputable def aTT (Y L : ℝ) (s : Ideal (𝓞 F)) : ℂ :=
  ((if (Ideal.absNorm s : ℝ) ≤ Y then (1 : ℂ) else 0) - (if (Ideal.absNorm s : ℝ) ≤ L then 1 else 0)) *
    (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ))

/-- The column factor of `T − T′`. -/
noncomputable def E1 (c : Ideal (𝓞 F)) : ℂ :=
  ∏ P ∈ primesOf c, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))

theorem TTt_pair_eq {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (hψ0 : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      PsiHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂))
    (h𝔪 : 𝔪 ≠ ⊥) {𝔤 c₁ c₂ : Ideal (𝓞 F)} (hc₁ : IsExterior 𝔪 c₁) (hc₂ : IsExterior 𝔪 c₂)
    (h12 : c₁ ⊔ c₂ = ⊤) (M L L' : ℝ) :
    TTt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L L' =
      R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2) *
        (∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) *
      ∑ e ∈ (primesOf 𝔤).powerset, ∑ f ∈ (primesOf 𝔤).powerset,
        ((-1 : ℂ) ^ e.card * (Ideal.absNorm (pideal e) : ℂ) ^ (-(1 / 2 : ℂ)) *
          (Ideal.absNorm (pideal f) : ℂ) ^ (-(1 / 2 : ℂ))) *
        ((L3H.chiK ι 𝔪 g (pideal e) c₁ * L3H.chiK ι 𝔪 g (pideal f) c₁ * E1 c₁) *
          (L3H.chiK ι 𝔪 g (pideal e) c₂ * L3H.chiK ι 𝔪 g (pideal f) c₂ * E1 c₂) *
          ∑ s ∈ Srow 𝔪 𝔤 (max (L' / Ideal.absNorm (pideal f)) L),
            aTT (L' / Ideal.absNorm (pideal f)) L s *
              (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂)) := by
  have hX₁ : 𝔪 ⊔ c₁ = ⊤ := by rw [sup_comm]; exact hc₁.2
  have hX₂ : 𝔪 ⊔ c₂ = ⊤ := by rw [sup_comm]; exact hc₂.2
  have hsplit := prod_primes_split h𝔪 hc₁.1 hc₂.1 hX₁ hX₂ h12
    (fun P => 1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))
  unfold TTt
  rw [hsplit]
  simp_rw [S_diff (psiP g c₁ c₂)]
  simp only [mul_sum, E1, aTT, psiP_apply]
  refine sum_congr rfl fun e _ => sum_congr rfl fun f _ => sum_congr rfl fun s _ => ?_
  ring

lemma norm_chiK_le {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (a c : Ideal (𝓞 F)) :
    ‖L3H.chiK ι 𝔪 g a c‖ ≤ 1 := by
  simp only [L3H.chiK, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _)

/-- `T − T′` summed over pairs. -/
theorem PS_TT_le {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (hψ0 : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      PsiHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂))
    (h𝔪 : 𝔪 ≠ ⊥) (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ)
    (hCr : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax) (z : Ideal (𝓞 F) → ℂ) {M L L' : ℝ}
    (hL : 0 < L) (hL' : 0 < L') (βf : ℝ → ℝ) (hβf0 : ∀ Y, 0 ≤ βf Y)
    (hS : ∀ Y, L3H.SBf (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 Y) C (βf Y)) {NB Bm : ℝ}
    (hNB0 : 0 ≤ NB) (hBm0 : 0 ≤ Bm)
    (hNB : ∀ f ∈ (primesOf 𝔤).powerset,
      (nblk (min (L' / Ideal.absNorm (pideal f)) L) (max (L' / Ideal.absNorm (pideal f)) L) : ℝ) ≤ NB)
    (hBm : ∀ f ∈ (primesOf 𝔤).powerset, ∀ k : ℕ,
      2 ^ k * min (L' / Ideal.absNorm (pideal f)) L ≤ 2 * max (L' / Ideal.absNorm (pideal f)) L →
      (2 ^ k * min (L' / Ideal.absNorm (pideal f)) L) ^ (-(1 / 2 : ℝ)) *
        βf (2 ^ (k + 1) * min (L' / Ideal.absNorm (pideal f)) L) ≤ Bm) :
    ‖PSnp C z (fun c₁ c₂ => TTt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L L')‖ ≤
      ‖R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2)‖ * 2 ^ (primesOf 𝔪).card *
        (4 : ℝ) ^ (primesOf 𝔤).card * (NB * (2 * Bm * Ztau C z)) := by
  classical
  set P𝔤 := primesOf 𝔤
  set K0 : ℂ := R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2) *
    (∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ))))
  set κ : Finset (Ideal (𝓞 F)) → Finset (Ideal (𝓞 F)) → ℂ := fun e f =>
    (-1 : ℂ) ^ e.card * (Ideal.absNorm (pideal e) : ℂ) ^ (-(1 / 2 : ℂ)) *
      (Ideal.absNorm (pideal f) : ℂ) ^ (-(1 / 2 : ℂ))
  set ue : Finset (Ideal (𝓞 F)) → Finset (Ideal (𝓞 F)) → Ideal (𝓞 F) → ℂ := fun e f c =>
    L3H.chiK ι 𝔪 g (pideal e) c * L3H.chiK ι 𝔪 g (pideal f) c * E1 c
  set Rf : Finset (Ideal (𝓞 F)) → Finset (Ideal (𝓞 F)) := fun f =>
    Srow 𝔪 𝔤 (max (L' / Ideal.absNorm (pideal f)) L)
  set Sb : Finset (Ideal (𝓞 F)) → Finset (Ideal (𝓞 F)) → ℂ := fun e f =>
    ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
      (z c₁ * ue e f c₁) * (starRingEnd ℂ (z c₂) * ue e f c₂) *
        ∑ s ∈ Rf f, aTT (L' / Ideal.absNorm (pideal f)) L s *
          (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂) else 0)
  have hPS : PSnp C z (fun c₁ c₂ => TTt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L L') =
      K0 * ∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, κ e f * Sb e f := by
    unfold PSnp
    have h1 : ∀ c₁ ∈ C, ∀ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
        z c₁ * starRingEnd ℂ (z c₂) * TTt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L L' else 0) =
        (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then ∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset,
          K0 * κ e f * ((z c₁ * ue e f c₁) * (starRingEnd ℂ (z c₂) * ue e f c₂) *
            ∑ s ∈ Rf f, aTT (L' / Ideal.absNorm (pideal f)) L s *
              (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂)) else 0) := by
      intro c₁ hc₁ c₂ hc₂
      split_ifs with h
      · rw [TTt_pair_eq g hψ0 h𝔪 (L3H.mem_rowsF_zero.1 (hCr c₁ hc₁)).1
          (L3H.mem_rowsF_zero.1 (hCr c₂ hc₂)).1 h.1, mul_sum, mul_sum]
        refine sum_congr rfl fun e _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun f _ => ?_
        simp only [K0, κ, ue]; ring
      · rfl
    rw [sum_congr rfl fun c₁ hc₁ => sum_congr rfl fun c₂ hc₂ => h1 c₁ hc₁ c₂ hc₂]
    have h2 := sum_ite_sum_comm C P𝔤.powerset (fun c₁ c₂ => c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤))
      (fun e c₁ c₂ => ∑ f ∈ P𝔤.powerset, K0 * κ e f * ((z c₁ * ue e f c₁) *
        (starRingEnd ℂ (z c₂) * ue e f c₂) * ∑ s ∈ Rf f, aTT (L' / Ideal.absNorm (pideal f)) L s *
          (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂)))
    rw [h2, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    have h3 := sum_ite_sum_comm C P𝔤.powerset (fun c₁ c₂ => c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤))
      (fun f c₁ c₂ => K0 * κ e f * ((z c₁ * ue e f c₁) *
        (starRingEnd ℂ (z c₂) * ue e f c₂) * ∑ s ∈ Rf f, aTT (L' / Ideal.absNorm (pideal f)) L s *
          (L3H.chiK ι 𝔪 g s c₁ * L3H.chiK ι 𝔪 g s c₂)))
    rw [h3, mul_sum]
    refine sum_congr rfl fun f _ => ?_
    simp only [Sb, mul_sum]
    refine sum_congr rfl fun c₁ _ => sum_congr rfl fun c₂ _ => ?_
    split_ifs
    · simp only [mul_sum]; exact sum_congr rfl fun x _ => by ring
    · ring
  rw [hPS]
  have hZ0 : 0 ≤ Ztau C z := Finset.sum_nonneg fun _ _ => by positivity
  have hue : ∀ e f c, ‖ue e f c‖ ≤ (2 : ℝ) ^ (L3H.pf c).card := by
    intro e f c
    simp only [ue, norm_mul]
    have h3 : ‖E1 c‖ ≤ (2 : ℝ) ^ (L3H.pf c).card := by
      rw [E1, ← primesOf_eq_pf]; exact norm_prod_one_sub_le c (by norm_num)
    calc ‖L3H.chiK ι 𝔪 g (pideal e) c‖ * ‖L3H.chiK ι 𝔪 g (pideal f) c‖ * ‖E1 c‖
        ≤ 1 * 1 * (2 : ℝ) ^ (L3H.pf c).card := by
          gcongr
          · exact norm_chiK_le g _ _
          · exact norm_chiK_le g _ _
      _ = _ := by ring
  have hSb : ∀ e, ∀ f ∈ P𝔤.powerset, ‖Sb e f‖ ≤ NB * (2 * Bm * Ztau C z) := by
    intro e f hf
    have hpf : (0 : ℝ) < Ideal.absNorm (pideal f) :=
      absNorm_pideal_pos (Finset.mem_powerset.1 hf)
    set Y := L' / Ideal.absNorm (pideal f) with hY
    have hY0 : 0 < Y := div_pos hL' hpf
    have hmin : 0 < min Y L := lt_min hY0 hL
    have hS' : ∀ X, L3H.SBf (L3H.chiK ι 𝔪 g) ((Rf f).filter
        (fun s => (Ideal.absNorm s : ℝ) ≤ X)) C (βf X) := by
      intro X
      refine (hS X).mono_rows fun s hs => ?_
      rw [Finset.mem_filter] at hs
      obtain ⟨h1, h2, _, _⟩ := mem_Srow.1 hs.1
      exact L3H.mem_rowsF_zero.2 ⟨h1, h2, hs.2⟩
    have ha : ∀ s ∈ Rf f, aTT Y L s ≠ 0 →
        min Y L < (Ideal.absNorm s : ℝ) ∧ (Ideal.absNorm s : ℝ) ≤ max Y L := by
      intro s _ hne
      simp only [aTT] at hne
      by_cases h1 : (Ideal.absNorm s : ℝ) ≤ Y <;> by_cases h2 : (Ideal.absNorm s : ℝ) ≤ L <;>
        simp [h1, h2] at hne
      · exact ⟨lt_of_le_of_lt (min_le_right _ _) (not_le.1 h2), h1.trans (le_max_left _ _)⟩
      · exact ⟨lt_of_le_of_lt (min_le_left _ _) (not_le.1 h1), h2.trans (le_max_right _ _)⟩
    have ha' : ∀ s ∈ Rf f, ‖aTT Y L s‖ ≤ (Ideal.absNorm s : ℝ) ^ (-(1 / 2 : ℝ)) := by
      intro s hs
      have hN : (0 : ℝ) < Ideal.absNorm s := absNorm_pos (mem_Srow.1 hs).1.1
      simp only [aTT, norm_mul]
      have e1 : ‖(if (Ideal.absNorm s : ℝ) ≤ Y then (1 : ℂ) else 0) -
          (if (Ideal.absNorm s : ℝ) ≤ L then 1 else 0)‖ ≤ 1 := by
        split_ifs <;> simp
      have e2 : ‖(Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ))‖ = (Ideal.absNorm s : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [show ((Ideal.absNorm s : ℂ)) = ((Ideal.absNorm s : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hN]
        norm_num
      rw [e2]
      calc _ ≤ 1 * (Ideal.absNorm s : ℝ) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
        _ = _ := one_mul _
    have hd := bil_dyadic (𝔪 := 𝔪) (L3H.chiK ι 𝔪 g) (Rf f) C Cmax hCr hmin
      (min_le_max) βf hβf0 hS' (aTT Y L) ha ha' (hBm f hf)
      (fun c => z c * ue e f c) (fun c => starRingEnd ℂ (z c) * ue e f c)
    have hu := tau_e_le C z (ue e f) (hue e f)
    have hv := tau_e_le C (fun c => starRingEnd ℂ (z c)) (ue e f) (hue e f)
    have hZ : Ztau C (fun c => starRingEnd ℂ (z c)) = Ztau C z := by simp [Ztau]
    rw [hZ] at hv
    have hsq := sqrt_mul_sqrt_le_of_le (by positivity) (by positivity) hu hv
    refine hd.trans ?_
    have hn := hNB f hf
    have hnb0 : (0 : ℝ) ≤ nblk (min Y L) (max Y L) := Nat.cast_nonneg _
    calc (nblk (min Y L) (max Y L) : ℝ) * (2 * Bm * Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card *
          ‖z c * ue e f c‖ ^ 2) * Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card *
          ‖starRingEnd ℂ (z c) * ue e f c‖ ^ 2))
        = (nblk (min Y L) (max Y L) : ℝ) * (2 * Bm * (Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card *
          ‖z c * ue e f c‖ ^ 2) * Real.sqrt (∑ c ∈ C, (2 : ℝ) ^ (L3H.pf c).card *
          ‖starRingEnd ℂ (z c) * ue e f c‖ ^ 2))) := by ring
      _ ≤ NB * (2 * Bm * Ztau C z) := by
          apply mul_le_mul hn (mul_le_mul_of_nonneg_left hsq (by positivity))
            (by positivity) hNB0
  have hκ : ∀ e f, ‖κ e f‖ ≤ 1 := by
    intro e f
    simp only [κ, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ∀ x : Finset (Ideal (𝓞 F)), ‖(Ideal.absNorm (pideal x) : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
      intro x
      by_cases h0 : pideal x = ⊥
      · rw [h0, Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow (by norm_num)]; simp
      · exact norm_natCast_cpow_neg_le_one (Nat.one_le_iff_ne_zero.2 (by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0)) (by norm_num)
    exact mul_le_one₀ (h1 e) (norm_nonneg _) (h1 f)
  have hK0 : ‖K0‖ ≤ ‖R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2)‖ * 2 ^ (primesOf 𝔪).card := by
    simp only [K0, norm_mul]
    gcongr
    exact norm_prod_one_sub_le 𝔪 (by norm_num)
  have hsum : ‖∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, κ e f * Sb e f‖ ≤
      (4 : ℝ) ^ P𝔤.card * (NB * (2 * Bm * Ztau C z)) := by
    refine (norm_sum_le _ _).trans ?_
    have h4 : (4 : ℝ) ^ P𝔤.card = ((P𝔤.powerset.card : ℕ) : ℝ) * ((P𝔤.powerset.card : ℕ) : ℝ) := by
      rw [Finset.card_powerset]; push_cast; rw [← mul_pow]; norm_num
    rw [h4, mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun e _ => ?_
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun f hf => ?_
    rw [norm_mul]
    calc ‖κ e f‖ * ‖Sb e f‖ ≤ 1 * (NB * (2 * Bm * Ztau C z)) :=
          mul_le_mul (hκ e f) (hSb e f hf) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [norm_mul]
  have hnn : 0 ≤ (4 : ℝ) ^ P𝔤.card * (NB * (2 * Bm * Ztau C z)) := by positivity
  calc ‖K0‖ * ‖∑ e ∈ P𝔤.powerset, ∑ f ∈ P𝔤.powerset, κ e f * Sb e f‖
      ≤ (‖R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2)‖ * 2 ^ (primesOf 𝔪).card) *
          ((4 : ℝ) ^ P𝔤.card * (NB * (2 * Bm * Ztau C z))) :=
        mul_le_mul hK0 hsum (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PDQ: the dual tail `DQ` (crude bound)

On `Re w = −σ₁`: `‖HQ‖ ≤ M^{−σ₁} N𝔤^{σ₁} 2^{ω(𝔤)} (N c₁ N c₂)^{1/2+σ₁} 2^{ω(c₁)+ω(c₂)} L′^{−(σ₁−1/2)} · K (1+|t|)^A`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma prod_one_add_le_pow (S : Finset (Ideal (𝓞 F))) {σ : ℝ} (hσ : 0 ≤ σ)
    (hS : ∀ P ∈ S, 1 ≤ Ideal.absNorm P) :
    ∏ P ∈ S, (1 + (Ideal.absNorm P : ℝ) ^ σ) ≤
      2 ^ S.card * (∏ P ∈ S, (Ideal.absNorm P : ℝ)) ^ σ := by
  rw [← Real.finset_prod_rpow _ _ (fun P _ => Nat.cast_nonneg _), ← prod_const, ← prod_mul_distrib]
  refine prod_le_prod (fun P _ => by positivity) fun P hP => ?_
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm P : ℝ) ^ σ :=
    Real.one_le_rpow (by exact_mod_cast hS P hP) hσ
  linarith

lemma norm_one_sub_cpow_le {c : ℂ} (hc : ‖c‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} {w : ℂ}
    (hw : -σ ≤ w.re) : ‖1 - c * (n : ℂ) ^ (-w)‖ ≤ 1 + (n : ℝ) ^ σ := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul]
  have : ‖(n : ℂ) ^ (-w)‖ ≤ (n : ℝ) ^ σ := by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by simp; linarith)
  nlinarith [norm_nonneg c, norm_nonneg ((n : ℂ) ^ (-w))]

lemma absNorm_pideal_primesOf_le {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) :
    (∏ P ∈ primesOf 𝔤, (Ideal.absNorm P : ℝ)) ≤ Ideal.absNorm 𝔤 := by
  have hd : pideal (primesOf 𝔤) ∣ 𝔤 := by
    refine Finset.prod_primes_dvd 𝔤 (fun P hP => Ideal.prime_of_isPrime (primesOf_prime hP).2
      (primesOf_prime hP).1) fun P hP => ?_
    exact Ideal.dvd_iff_le.2 (le_of_mem_primesOf hP)
  have h1 : Ideal.absNorm (pideal (primesOf 𝔤)) ≤ Ideal.absNorm 𝔤 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔤))
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd))
  have h2 : (Ideal.absNorm (pideal (primesOf 𝔤)) : ℝ) = ∏ P ∈ primesOf 𝔤, (Ideal.absNorm P : ℝ) := by
    unfold pideal; rw [map_prod]; push_cast; rfl
  rw [← h2]; exact_mod_cast h1

lemma norm_mul8_le {a b c d e f g h : ℂ} {A B C D E G H J : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) (hf : ‖f‖ ≤ G) (hg : ‖g‖ ≤ H) (hh : ‖h‖ ≤ J) :
    ‖a * b * c * d * e * f * g * h‖ ≤ A * B * C * D * E * G * H * J := by
  rw [norm_mul]
  have h7 := norm_mul7_le ha hb hc hd he hf hg
  have hA := (norm_nonneg a).trans ha
  have hB := (norm_nonneg b).trans hb
  have hC := (norm_nonneg c).trans hc
  have hD := (norm_nonneg d).trans hd
  have hE := (norm_nonneg e).trans he
  have hG := (norm_nonneg f).trans hf
  have hH := (norm_nonneg g).trans hg
  exact mul_le_mul h7 hh (norm_nonneg _) (by positivity)

lemma norm_Qf_le {ψ : Ideal (𝓞 F) → ℂ} (hψ : ∀ I, ‖ψ I‖ ≤ 1) {L' σ₁ : ℝ} (hL' : 0 < L')
    (hσ : 1 / 2 ≤ σ₁) {u : ℂ} (hu : u.re = 1 + σ₁) :
    ‖Qf ψ L' u‖ ≤ L' ^ (-(σ₁ - 1 / 2)) *
      ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hZs := summable_absNorm_rpow (F := F) (σ := 3 / 2) (by norm_num)
  have hb : ∀ s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s},
      ‖if L' < (Ideal.absNorm s.1 : ℝ) then ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) else 0‖ ≤
        L' ^ (-(σ₁ - 1 / 2)) * ((Ideal.absNorm s.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro s
    have hN : (0 : ℝ) < Ideal.absNorm s.1 := absNorm_pos s.2.1
    split_ifs with h
    · rw [norm_mul]
      have e1 : ‖(Ideal.absNorm s.1 : ℂ) ^ (-u)‖ = (Ideal.absNorm s.1 : ℝ) ^ (-(1 + σ₁)) := by
        rw [show ((Ideal.absNorm s.1 : ℂ)) = ((Ideal.absNorm s.1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hN, neg_re, hu]
      rw [e1]
      have e2 : (Ideal.absNorm s.1 : ℝ) ^ (-(1 + σ₁)) =
          (Ideal.absNorm s.1 : ℝ) ^ (-(σ₁ - 1 / 2)) * (Ideal.absNorm s.1 : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hN]; ring_nf
      rw [e2]
      have e3 : (Ideal.absNorm s.1 : ℝ) ^ (-(σ₁ - 1 / 2)) ≤ L' ^ (-(σ₁ - 1 / 2)) :=
        Real.rpow_le_rpow_of_nonpos hL' h.le (by linarith)
      calc ‖ψ s.1‖ * ((Ideal.absNorm s.1 : ℝ) ^ (-(σ₁ - 1 / 2)) *
            (Ideal.absNorm s.1 : ℝ) ^ (-(3 / 2 : ℝ)))
          ≤ 1 * (L' ^ (-(σ₁ - 1 / 2)) * (Ideal.absNorm s.1 : ℝ) ^ (-(3 / 2 : ℝ))) := by
            gcongr
            exact hψ _
        _ = _ := by push_cast; ring
    · rw [norm_zero]; positivity
  unfold Qf
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact ((hZs.subtype _).mul_left (L' ^ (-(σ₁ - 1 / 2)))).of_nonneg_of_le
      (fun _ => norm_nonneg _) hb
  · refine (Summable.tsum_le_tsum hb ?_ ((hZs.subtype _).mul_left _)).trans ?_
    · exact ((hZs.subtype _).mul_left (L' ^ (-(σ₁ - 1 / 2)))).of_nonneg_of_le
        (fun _ => norm_nonneg _) hb
    · rw [tsum_mul_left]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hZs.tsum_subtype_le _ _ (fun _ => by positivity)

set_option maxHeartbeats 1600000 in
/-- The dual tail summed over pairs. -/
theorem PS_DQ_le {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
    {σ₁ : ℝ} (hσ₁ : 1 ≤ σ₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (𝔤 : Ideal (𝓞 F)), 𝔤 ≠ ⊥ → ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) {M L' : ℝ}, 0 < M → 0 < L' →
        ‖PSnp C z (fun c₁ c₂ => DQt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' σ₁)‖ ≤
          K * M ^ (-σ₁) * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ * 2 ^ (primesOf 𝔤).card *
            (max Cmax 1) ^ (1 + 2 * σ₁) * L' ^ (-(σ₁ - 1 / 2)) * C.card * Ztau C z := by
  classical
  set a : ℝ := -σ₁ with ha
  have ha1 : a < 1 := by linarith
  set r := InfinitePlace.nrComplexPlaces F
  obtain ⟨CG, AG, hCG, hAG, hG⟩ := G0_bound a a ha1
  obtain ⟨B, hB⟩ := exists_dedekindZeta_bound F
  set Z32 : ℝ := ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
  have hZ32 : 0 ≤ Z32 := tsum_nonneg fun _ => by positivity
  set P𝔪 : ℝ := ∏ P ∈ primesOf 𝔪, (Ideal.absNorm P : ℝ)
  have hP𝔪 : 0 ≤ P𝔪 := prod_nonneg fun _ _ => Nat.cast_nonneg _
  have hd1 : (1 : ℝ) ≤ ((|discr F| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero F; exact_mod_cast Int.one_le_abs this
  set dd : ℝ := ((|discr F| : ℤ) : ℝ)
  set Kfix : ℝ := (2 ^ (primesOf 𝔪).card * P𝔪 ^ σ₁) * dd ^ (1 / 2 + σ₁) * CG ^ r *
    2 ^ (primesOf 𝔪).card * 2 ^ (primesOf 𝔪).card * max B 0 * Z32 with hKfix
  have hKfix0 : 0 ≤ Kfix := by positivity
  set AK : ℝ := AG * r
  refine ⟨(1 / (2 * π)) * Kfix * IW a AK, by
    have := IW_nonneg a AK; have := Real.pi_pos; positivity, ?_⟩
  intro 𝔤 h𝔤 C Cmax hCr z M L' hM hL'
  set w : ℝ → ℂ := fun t => (a : ℂ) + t * I with hw
  have hwre : ∀ t, (w t).re = a := fun t => by simp [hw]
  have hwim : ∀ t, (w t).im = t := fun t => by simp [hw]
  have hpsi1 : ∀ c₁ c₂ s, ‖psiP g c₁ c₂ s‖ ≤ 1 := by
    intro c₁ c₂ s
    simp only [psiP_apply, L3H.chiK, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _)) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _))
  -- per coprime pair
  have hpair : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ⊔ c₂ = ⊤ →
      ‖DQt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' σ₁‖ ≤ (1 / (2 * π)) * Kfix * IW a AK *
        (M ^ (-σ₁) * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ * 2 ^ (primesOf 𝔤).card *
          ((Ideal.absNorm c₁ : ℝ) ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₁).card) *
          ((Ideal.absNorm c₂ : ℝ) ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₂).card) *
          L' ^ (-(σ₁ - 1 / 2))) := by
    intro c₁ hc₁ c₂ hc₂ h12
    have he₁ := (L3H.mem_rowsF_zero.1 (hCr c₁ hc₁)).1
    have he₂ := (L3H.mem_rowsF_zero.1 (hCr c₂ hc₂)).1
    have h0 : c₁ * c₂ ≠ ⊥ := by
      rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
      exact ⟨by rw [Ideal.zero_eq_bot]; exact he₁.1, by rw [Ideal.zero_eq_bot]; exact he₂.1⟩
    set Bp : ℝ := Kfix * (M ^ (-σ₁) * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ * 2 ^ (primesOf 𝔤).card *
        ((Ideal.absNorm c₁ : ℝ) ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₁).card) *
        ((Ideal.absNorm c₂ : ℝ) ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₂).card) *
        L' ^ (-(σ₁ - 1 / 2))) with hBp
    have hbound : ∀ t, ‖HQ 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' (w t)‖ ≤ Bp * (1 + |t|) ^ AK := by
      intro t
      have e1 : ‖(M : ℂ) ^ w t‖ ≤ M ^ (-σ₁) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hM, hwre]
      have e2 : ‖Em 𝔪 𝔤 (psiP g c₁ c₂) (w t)‖ ≤ (2 ^ (primesOf 𝔪).card * P𝔪 ^ σ₁) *
          (2 ^ (primesOf 𝔤).card * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁) := by
        unfold Em
        rw [norm_mul]
        have hσ0 : 0 ≤ σ₁ := by linarith
        have f1 : ‖∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-w t))‖ ≤
            2 ^ (primesOf 𝔪).card * P𝔪 ^ σ₁ := by
          rw [norm_prod]
          refine (prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_).trans
            (prod_one_add_le_pow _ hσ0 fun P hP => one_le_absNorm_of_mem_primesOf hP)
          have := norm_one_sub_cpow_le (c := 1) (by simp) (one_le_absNorm_of_mem_primesOf hP)
            (σ := σ₁) (w := w t) (by rw [hwre])
          simpa using this
        have f2 : ‖∏ P ∈ primesOf 𝔤, (1 - psiP g c₁ c₂ P * (Ideal.absNorm P : ℂ) ^ (-w t))‖ ≤
            2 ^ (primesOf 𝔤).card * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ := by
          rw [norm_prod]
          refine (prod_le_prod (fun _ _ => norm_nonneg _) fun P hP =>
            norm_one_sub_cpow_le (hpsi1 _ _ _) (one_le_absNorm_of_mem_primesOf hP)
            (σ := σ₁) (w := w t) (by rw [hwre])).trans
            ((prod_one_add_le_pow _ hσ0 fun P hP => one_le_absNorm_of_mem_primesOf hP).trans ?_)
          gcongr
          exact absNorm_pideal_primesOf_le h𝔤
        exact mul_le_mul f1 f2 (norm_nonneg _) (by positivity)
      have e3 : ‖Dc (c₁ * c₂) ^ (1 / 2 - w t)‖ ≤ dd ^ (1 / 2 + σ₁) *
          ((Ideal.absNorm c₁ : ℝ) ^ (1 / 2 + σ₁) * (Ideal.absNorm c₂ : ℝ) ^ (1 / 2 + σ₁)) := by
        rw [Dc_mul_cpow, norm_mul, norm_mul]
        have hre : (1 / 2 - w t).re = 1 / 2 + σ₁ := by simp [hwre, ha]
        have n1 : ‖(((|discr F| : ℤ) : ℝ) : ℂ) ^ (1 / 2 - w t)‖ = dd ^ (1 / 2 + σ₁) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hre]
        have n2 : ∀ c : Ideal (𝓞 F), c ≠ ⊥ → ‖(Ideal.absNorm c : ℂ) ^ (1 / 2 - w t)‖ =
            (Ideal.absNorm c : ℝ) ^ (1 / 2 + σ₁) := by
          intro c hc
          rw [show ((Ideal.absNorm c : ℂ)) = ((Ideal.absNorm c : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_cpow_eq_rpow_re_of_pos (absNorm_pos hc), hre]
        rw [n1, n2 c₁ he₁.1, n2 c₂ he₂.1]; ring_nf; rfl
      have e4 : ‖G0 (w t) ^ r‖ ≤ CG ^ r * (1 + |t|) ^ AK := by
        rw [norm_pow]
        have h := hG (w t) (by rw [hwre]) (by rw [hwre])
        rw [hwim] at h
        calc ‖G0 (w t)‖ ^ r ≤ (CG * (1 + |t|) ^ AG) ^ r := pow_le_pow_left₀ (norm_nonneg _) h r
          _ = CG ^ r * (1 + |t|) ^ AK := by
            rw [mul_pow, ← Real.rpow_natCast ((1 + |t|) ^ AG), ← Real.rpow_mul (by positivity)]
      have e5 : ‖Zm 𝔪 (1 - w t)‖ ≤ 2 ^ (primesOf 𝔪).card := by
        have := norm_Zm_le 𝔪 (δ := 1) one_pos (u := 1 - w t) (by simp [hwre, ha]; linarith)
        refine this.trans (le_of_eq ?_)
        rw [show (1 : ℝ) - (2 : ℝ) ^ (-(1 : ℝ)) = 2⁻¹ by norm_num, inv_pow, inv_inv]
      have e6 : ‖∏ P ∈ primesOf (𝔪 * (c₁ * c₂)), (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * (1 - w t))))‖ ≤
          2 ^ (primesOf 𝔪).card * (2 ^ (L3H.pf c₁).card * 2 ^ (L3H.pf c₂).card) := by
        have hX₁ : 𝔪 ⊔ c₁ = ⊤ := by rw [sup_comm]; exact he₁.2
        have hX₂ : 𝔪 ⊔ c₂ = ⊤ := by rw [sup_comm]; exact he₂.2
        rw [prod_primes_split h𝔪 he₁.1 he₂.1 hX₁ hX₂ h12, norm_mul, norm_mul]
        have hu : 0 ≤ (2 * (1 - w t)).re := by simp [hwre, ha]; linarith
        have f1 := norm_prod_one_sub_le 𝔪 hu
        have f2 := norm_e_le c₁ hu
        have f3 := norm_e_le c₂ hu
        refine (mul_le_mul (mul_le_mul f1 f2 (norm_nonneg _) (by positivity)) f3 (norm_nonneg _)
          (by positivity)).trans (le_of_eq ?_)
        ring
      have e7 : ‖dedekindZeta F (2 * (1 - w t))‖ ≤ max B 0 :=
        (hB _ (by simp [hwre, ha]; linarith)).trans (le_max_left _ _)
      have e8 := norm_Qf_le (L' := L') (σ₁ := σ₁) (hpsi1 c₁ c₂) hL' (by linarith)
        (u := 1 - w t) (by simp [hwre, ha])
      have h8 := norm_mul8_le e1 e2 e3 e4 e5 e6 e7 e8
      unfold HQ Kd
      refine h8.trans (le_of_eq ?_)
      rw [hBp, hKfix]
      ring
    have hcont : Continuous fun t : ℝ => HQ 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' (w t) := by
      unfold HQ
      have hK := continuous_line_of_diffOn (σ := a) (differentiableOn_Kd 𝔪 𝔤 (psiP g c₁ c₂) h0 hM
        (a := a) ha1)
      have hz : Continuous fun t : ℝ => dedekindZeta F (2 * (1 - w t)) := by
        have hc : Continuous fun t : ℝ => R0 F (2 * (1 - w t)) / (2 * (1 - w t) - 1) :=
          ((R0_diff F).continuous.comp (by fun_prop)).div (by fun_prop) fun t h' => by
            have := congrArg Complex.re h'; simp [hwre, ha] at this; linarith
        refine hc.congr fun t => ?_
        have hre : 1 < (2 * (1 - w t)).re := by simp [hwre, ha]; linarith
        have hne : 2 * (1 - w t) - 1 ≠ 0 := fun h' => by
          have := congrArg Complex.re h'; simp [hwre, ha] at this; linarith
        rw [R0_eq hre, mul_div_assoc, mul_comm, div_mul_cancel₀ _ hne]
      have hq : Continuous fun t : ℝ => Qf (psiP g c₁ c₂) L' (1 - w t) := by
        unfold Qf
        have hZs := (summable_absNorm_rpow (F := F) (σ := 3 / 2) (by norm_num)).subtype
          {s : Ideal (𝓞 F) | s ≠ ⊥ ∧ Squarefree s}
        refine continuous_tsum (fun s => ?_) hZs fun s t => ?_
        · split_ifs
          · refine continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl ?_))
            exact_mod_cast (absNorm_pos s.2.1).ne'
          · exact continuous_const
        · have hN : (1 : ℝ) ≤ Ideal.absNorm s.1 := L3H.one_le_absNorm s.2.1
          split_ifs
          · rw [norm_mul]
            have e1 : ‖(Ideal.absNorm s.1 : ℂ) ^ (-(1 - w t))‖ =
                (Ideal.absNorm s.1 : ℝ) ^ (-(1 + σ₁)) := by
              rw [show ((Ideal.absNorm s.1 : ℂ)) = ((Ideal.absNorm s.1 : ℝ) : ℂ) by push_cast; rfl,
                Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
              congr 1; simp [hwre, ha]; ring
            rw [e1]
            have : (Ideal.absNorm s.1 : ℝ) ^ (-(1 + σ₁)) ≤ (Ideal.absNorm s.1 : ℝ) ^ (-(3 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hN (by linarith)
            calc ‖psiP g c₁ c₂ s.1‖ * (Ideal.absNorm s.1 : ℝ) ^ (-(1 + σ₁))
                ≤ 1 * (Ideal.absNorm s.1 : ℝ) ^ (-(3 / 2 : ℝ)) :=
                  mul_le_mul (hpsi1 _ _ _) this (by positivity) zero_le_one
              _ = _ := by simp [Function.comp]
          · rw [norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact (hK.mul hz).mul hq
    have hint := norm_integral_Wm_le (σ := a) (A := AK) (B := Bp) hcont.aestronglyMeasurable hbound
    unfold DQt
    rw [norm_mul]
    have hpi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hpi]
    have hpi0 : (0 : ℝ) ≤ 1 / (2 * π) := by have := Real.pi_pos; positivity
    refine (mul_le_mul_of_nonneg_left hint hpi0).trans (le_of_eq ?_)
    rw [hBp]; ring
  set Kc0 : ℝ := (1 / (2 * π)) * Kfix * IW a AK * (M ^ (-σ₁) * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ *
    2 ^ (primesOf 𝔤).card * L' ^ (-(σ₁ - 1 / 2))) with hKc0
  have hKc00 : 0 ≤ Kc0 := by
    have := IW_nonneg a AK; have := Real.pi_pos
    have : 0 ≤ M ^ (-σ₁) := Real.rpow_nonneg hM.le _
    have : 0 ≤ L' ^ (-(σ₁ - 1 / 2)) := Real.rpow_nonneg hL'.le _
    positivity
  set X : ℝ := max Cmax 1
  have hX1 : 1 ≤ X := le_max_right _ _
  set y : Ideal (𝓞 F) → ℝ := fun c => ‖z c‖ * 2 ^ (L3H.pf c).card
  have hNc : ∀ c ∈ C, (Ideal.absNorm c : ℝ) ^ (1 / 2 + σ₁) ≤ X ^ (1 / 2 + σ₁) := by
    intro c hc
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      ((L3H.mem_rowsF_zero.1 (hCr c hc)).2.2.trans (le_max_left _ _)) (by linarith)
  unfold PSnp
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c₁ ∈ C, ∀ c₂ ∈ C, ‖(if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
      z c₁ * starRingEnd ℂ (z c₂) * DQt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' σ₁ else 0)‖ ≤
      Kc0 * X ^ (1 + 2 * σ₁) * (y c₁ * y c₂) := by
    intro c₁ hc₁ c₂ hc₂
    split_ifs with h
    · rw [norm_mul, norm_mul, Complex.norm_conj]
      have hp := hpair c₁ hc₁ c₂ hc₂ h.1
      have hX : X ^ (1 + 2 * σ₁) = X ^ (1 / 2 + σ₁) * X ^ (1 / 2 + σ₁) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
      rw [hX]
      have hz1 : 0 ≤ ‖z c₁‖ := norm_nonneg _
      have hz2 : 0 ≤ ‖z c₂‖ := norm_nonneg _
      calc ‖z c₁‖ * ‖z c₂‖ * ‖DQt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' σ₁‖
          ≤ ‖z c₁‖ * ‖z c₂‖ * (Kc0 * (((Ideal.absNorm c₁ : ℝ) ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₁).card) *
              ((Ideal.absNorm c₂ : ℝ) ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₂).card))) := by
            refine mul_le_mul_of_nonneg_left (hp.trans (le_of_eq ?_)) (by positivity)
            rw [hKc0]; ring
        _ ≤ ‖z c₁‖ * ‖z c₂‖ * (Kc0 * ((X ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₁).card) *
              (X ^ (1 / 2 + σ₁) * 2 ^ (L3H.pf c₂).card))) := by
            gcongr
            · exact (L3H.mem_rowsF_zero.1 (hCr c₁ hc₁)).2.2.trans (le_max_left _ _)
            · exact (L3H.mem_rowsF_zero.1 (hCr c₂ hc₂)).2.2.trans (le_max_left _ _)
        _ = _ := by simp only [y]; ring
    · rw [norm_zero]
      have : 0 ≤ X ^ (1 + 2 * σ₁) := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ y c₁ * y c₂ := by simp only [y]; positivity
      positivity
  calc ∑ c₁ ∈ C, ‖∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
        z c₁ * starRingEnd ℂ (z c₂) * DQt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' σ₁ else 0)‖
      ≤ ∑ c₁ ∈ C, ∑ c₂ ∈ C, Kc0 * X ^ (1 + 2 * σ₁) * (y c₁ * y c₂) :=
        Finset.sum_le_sum fun c₁ hc₁ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun c₂ hc₂ => hterm c₁ hc₁ c₂ hc₂)
    _ = Kc0 * X ^ (1 + 2 * σ₁) * (∑ c ∈ C, y c) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ Kc0 * X ^ (1 + 2 * σ₁) * (C.card * Ztau C z) := by
        have hXp : 0 ≤ X ^ (1 + 2 * σ₁) := Real.rpow_nonneg (by linarith) _
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKc00 hXp)
        refine (sq_sum_le_card_mul_sum_sq).trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (Nat.cast_nonneg _)
        simp only [y]
        rw [mul_pow, ← pow_mul]
        have : (2 : ℝ) ^ ((L3H.pf c).card * 2) ≤ 8 ^ (L3H.pf c).card := by
          rw [pow_mul']; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
        calc ‖z c‖ ^ 2 * 2 ^ ((L3H.pf c).card * 2) ≤ ‖z c‖ ^ 2 * 8 ^ (L3H.pf c).card :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by rw [primesOf_eq_pf]; ring
    _ = _ := by rw [hKc0]; ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3Q_QS_Dev: the bilinear bounds for the four pieces (seam of 85b89dd7), statement verbatim

From `L3Q.PS_RP_le`, `L3Q.PS_DP_le`, `L3Q.PS_DQ_le`, `L3Q.PS_TT_le`. Does not import its own stub. -/

namespace ArtinPrimitiveRoots

open NumberField

theorem norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le
    (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (g : AllowedGen ι 𝔪)
    (hψ : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      GLW.PsiHyp 𝔪 (c₁ * c₂) (GLW.psiP g c₁ c₂)) :
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ → 𝔤 * 𝔪 ≠ ⊥ →
      ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ), (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      (∀ c ∈ C, c ⊔ 𝔤 * 𝔪 = ⊤) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L β : ℝ), 0 < M → 0 ≤ β →
      GLW.sbBound ι 𝔪 g (GLW.Srow 𝔪 𝔤 L) C β →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.RPt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L ε)‖ ≤
          K * M ^ ε * 2 ^ (GLW.primesOf (𝔤 * 𝔪)).card * β * GLW.Ztau C z) ∧
    (∀ ε' : ℝ, 0 < ε' → ε' < 1 / 2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L' β Cmin : ℝ), 0 < M → 0 ≤ β → 0 < Cmin →
      (∀ c ∈ C, Cmin ≤ (Ideal.absNorm c : ℝ)) →
      GLW.sbBound ι 𝔪 g (GLW.sqfRows 𝔪 L') C β →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.DPt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L' ε')‖ ≤
          K * M ^ (1 - ε') * 2 ^ (GLW.primesOf 𝔤).card * β * Cmin ^ (-(1 - 2 * ε')) *
            GLW.Ztau C z) ∧
    (∀ σ₁ : ℝ, 1 ≤ σ₁ → ∃ K : ℝ, 0 ≤ K ∧ ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ →
      ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ), (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L' : ℝ), 0 < M → 0 < L' →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.DQt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L' σ₁)‖ ≤
          K * M ^ (-σ₁) * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ * 2 ^ (GLW.primesOf 𝔤).card *
            (max Cmax 1) ^ (1 + 2 * σ₁) * L' ^ (-(σ₁ - 1 / 2)) * C.card * GLW.Ztau C z) ∧
    (∀ (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L L' : ℝ), 0 < L → 0 < L' →
      ∀ βf : ℝ → ℝ, (∀ Y, 0 ≤ βf Y) → (∀ Y, GLW.sbBound ι 𝔪 g (GLW.sqfRows 𝔪 Y) C (βf Y)) →
      ∀ NB Bm : ℝ, 0 ≤ NB → 0 ≤ Bm →
      (∀ f ∈ (GLW.primesOf 𝔤).powerset,
        (GLW.nblk (min (L' / Ideal.absNorm (GLW.pideal f)) L)
          (max (L' / Ideal.absNorm (GLW.pideal f)) L) : ℝ) ≤ NB) →
      (∀ f ∈ (GLW.primesOf 𝔤).powerset, ∀ k : ℕ,
        2 ^ k * min (L' / Ideal.absNorm (GLW.pideal f)) L ≤
          2 * max (L' / Ideal.absNorm (GLW.pideal f)) L →
        (2 ^ k * min (L' / Ideal.absNorm (GLW.pideal f)) L) ^ (-(1 / 2 : ℝ)) *
          βf (2 ^ (k + 1) * min (L' / Ideal.absNorm (GLW.pideal f)) L) ≤ Bm) →
      ‖GLW.PSnp C z (fun c₁ c₂ => GLW.TTt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L L')‖ ≤
        ‖GLW.R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * GLW.Wm (1 / 2)‖ *
          2 ^ (GLW.primesOf 𝔪).card * (4 : ℝ) ^ (GLW.primesOf 𝔤).card *
          (NB * (2 * Bm * GLW.Ztau C z))) := by
  have hr : ∀ (C : Finset (Ideal (𝓞 F))) (Y : ℝ), (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Y) →
      ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Y := fun C Y h c hc => by
    rw [← L3Q.sqfRows_eq]; exact h c hc
  refine ⟨fun ε hε hε2 => ?_, fun ε' hε' hε'2 => ?_, fun σ₁ hσ₁ => ?_, ?_⟩
  · obtain ⟨K, hK0, hK⟩ := L3Q.PS_RP_le g hε hε2
    exact ⟨K, hK0, fun 𝔤 h𝔤 h𝔤𝔪 C Cmax hCr hC z M L β hM hβ hS =>
      hK 𝔤 h𝔤 h𝔤𝔪 C Cmax (hr C Cmax hCr) hC z hM hβ hS⟩
  · obtain ⟨K, hK0, hK⟩ := L3Q.PS_DP_le g hψ h𝔪 hε' hε'2
    refine ⟨K, hK0, fun 𝔤 C Cmax hCr z M L' β Cmin hM hβ hCm hCmin hS =>
      hK 𝔤 C Cmax (hr C Cmax hCr) z hM hβ hCm hCmin ?_⟩
    rw [← L3Q.sqfRows_eq]; exact hS
  · obtain ⟨K, hK0, hK⟩ := L3Q.PS_DQ_le g h𝔪 hσ₁
    exact ⟨K, hK0, fun 𝔤 h𝔤 C Cmax hCr z M L' hM hL' =>
      hK 𝔤 h𝔤 C Cmax (hr C Cmax hCr) z hM hL'⟩
  · intro 𝔤 C Cmax hCr z M L L' hL hL' βf hβf0 hS NB Bm hNB0 hBm0 hNB hBm
    refine L3Q.PS_TT_le g hψ h𝔪 𝔤 C Cmax (hr C Cmax hCr) z hL hL' βf hβf0 (fun Y => ?_)
      hNB0 hBm0 hNB hBm
    rw [← L3Q.sqfRows_eq]; exact hS Y

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution
    (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (g : AllowedGen ι 𝔪)
    (hψ : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      GLW.PsiHyp 𝔪 (c₁ * c₂) (GLW.psiP g c₁ c₂)) :
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ → 𝔤 * 𝔪 ≠ ⊥ →
      ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ), (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      (∀ c ∈ C, c ⊔ 𝔤 * 𝔪 = ⊤) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L β : ℝ), 0 < M → 0 ≤ β →
      GLW.sbBound ι 𝔪 g (GLW.Srow 𝔪 𝔤 L) C β →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.RPt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L ε)‖ ≤
          K * M ^ ε * 2 ^ (GLW.primesOf (𝔤 * 𝔪)).card * β * GLW.Ztau C z) ∧
    (∀ ε' : ℝ, 0 < ε' → ε' < 1 / 2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L' β Cmin : ℝ), 0 < M → 0 ≤ β → 0 < Cmin →
      (∀ c ∈ C, Cmin ≤ (Ideal.absNorm c : ℝ)) →
      GLW.sbBound ι 𝔪 g (GLW.sqfRows 𝔪 L') C β →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.DPt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L' ε')‖ ≤
          K * M ^ (1 - ε') * 2 ^ (GLW.primesOf 𝔤).card * β * Cmin ^ (-(1 - 2 * ε')) *
            GLW.Ztau C z) ∧
    (∀ σ₁ : ℝ, 1 ≤ σ₁ → ∃ K : ℝ, 0 ≤ K ∧ ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ →
      ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ), (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L' : ℝ), 0 < M → 0 < L' →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.DQt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L' σ₁)‖ ≤
          K * M ^ (-σ₁) * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ * 2 ^ (GLW.primesOf 𝔤).card *
            (max Cmax 1) ^ (1 + 2 * σ₁) * L' ^ (-(σ₁ - 1 / 2)) * C.card * GLW.Ztau C z) ∧
    (∀ (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L L' : ℝ), 0 < L → 0 < L' →
      ∀ βf : ℝ → ℝ, (∀ Y, 0 ≤ βf Y) → (∀ Y, GLW.sbBound ι 𝔪 g (GLW.sqfRows 𝔪 Y) C (βf Y)) →
      ∀ NB Bm : ℝ, 0 ≤ NB → 0 ≤ Bm →
      (∀ f ∈ (GLW.primesOf 𝔤).powerset,
        (GLW.nblk (min (L' / Ideal.absNorm (GLW.pideal f)) L)
          (max (L' / Ideal.absNorm (GLW.pideal f)) L) : ℝ) ≤ NB) →
      (∀ f ∈ (GLW.primesOf 𝔤).powerset, ∀ k : ℕ,
        2 ^ k * min (L' / Ideal.absNorm (GLW.pideal f)) L ≤
          2 * max (L' / Ideal.absNorm (GLW.pideal f)) L →
        (2 ^ k * min (L' / Ideal.absNorm (GLW.pideal f)) L) ^ (-(1 / 2 : ℝ)) *
          βf (2 ^ (k + 1) * min (L' / Ideal.absNorm (GLW.pideal f)) L) ≤ Bm) →
      ‖GLW.PSnp C z (fun c₁ c₂ => GLW.TTt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L L')‖ ≤
        ‖GLW.R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * GLW.Wm (1 / 2)‖ *
          2 ^ (GLW.primesOf 𝔪).card * (4 : ℝ) ^ (GLW.primesOf 𝔤).card *
          (NB * (2 * Bm * GLW.Ztau C z))) := by
  exact ArtinPrimitiveRoots.norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le F ι 𝔪 h𝔪 g hψ

end
