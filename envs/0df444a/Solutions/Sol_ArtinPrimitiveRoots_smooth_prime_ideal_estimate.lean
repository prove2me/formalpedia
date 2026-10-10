-- Prove2me | solution 1 for ArtinPrimitiveRoots.smooth_prime_ideal_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T07:46:08.354996+00:00
-- url     : https://prove2.me/submissions/c607b69d-5689-41f9-b485-06b7f3c2a9e4

import Mathlib
import Theorems.Thm_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re
import Definitions.Def_ArtinHecke
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Theorems.Thm_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package

section
/-! # L92M_Basic: Mellin transforms of smooth functions supported in `[a, b] ⊂ (0, ∞)`

For `g : ℝ → ℝ` continuous with `tsupport g ⊆ Icc a b`, `0 < a`, the Mellin transform of
`(g · : ℂ)` is entire and bounded on vertical strips; for smooth `g`, integration by parts
(`D g t = t g'(t)`, `mellin (D g) s = -s mellin g s`) gives decay faster than any power of `|Im s|`.
-/

namespace ArtinPrimitiveRoots.L92M

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval ContDiff

lemma ofReal_inv_cpow_neg {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
    cpow_neg, inv_inv]

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

/-- M3c -/
theorem mellin_le_strip :
    ∃ C : ℝ, ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖mellin (fun u : ℝ => (f u : ℂ)) w‖ ≤ C / (4 + w.im ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := mellin_decay_aux hf ha hab 2 0 1
  refine ⟨4 * C, fun w h1 h2 => le_trans (hC w h1 h2) ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  rw [this]
  have := abs_nonneg w.im
  nlinarith

/-- M3d -/
theorem mellin_neg_nat_le (k : ℕ) :
    ‖mellin (fun u : ℝ => (f u : ℂ)) (-(k : ℂ))‖ ≤ (∫ t, |f t|) / a ^ (k + 1) := by
  have hfi : Integrable (fun t => |f t|) :=
    (hf.continuous.abs).integrable_of_hasCompactSupport (hasCompactSupport_of_tsupport hab).abs
  have hconv := mellinConvergent_of_tsupport hf.continuous ha hab (-(k : ℂ))
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hpt : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) → ‖(t : ℂ) ^ (-(k : ℂ) - 1) • (f t : ℂ)‖ ≤ |f t| / a ^ (k + 1) := by
    intro t ht
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, norm_real, Real.norm_eq_abs]
    by_cases hft : f t = 0
    · simp [hft]
    have hta : a ≤ t := (hab (subset_tsupport f hft)).1
    have e : (-(k : ℂ) - 1).re = -((k + 1 : ℕ) : ℝ) := by simp; ring
    rw [e, Real.rpow_neg ht.le, Real.rpow_natCast, div_eq_mul_inv, mul_comm]
    gcongr
  calc ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (-(k : ℂ) - 1) • (f t : ℂ)‖
      ≤ ∫ t : ℝ in Ioi 0, |f t| / a ^ (k + 1) :=
        setIntegral_mono_on hconv.norm (hfi.div_const _).integrableOn measurableSet_Ioi hpt
    _ ≤ ∫ t, |f t| / a ^ (k + 1) :=
        setIntegral_le_integral (hfi.div_const _) (Eventually.of_forall fun t => by positivity)
    _ = (∫ t, |f t|) / a ^ (k + 1) := integral_div _ _

/-- M3e -/
theorem mellin_integrable_line (σ : ℝ) :
    Integrable (fun t : ℝ => mellin (fun u : ℝ => (f u : ℂ)) (σ + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := mellin_decay_aux hf ha hab 2 σ σ
  have hcont : Continuous (fun t : ℝ => mellin (fun u : ℝ => (f u : ℂ)) (σ + t * I)) :=
    (mellin_differentiable f hf a b ha hab).continuous.comp (by fun_prop)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have h := hC (σ + t * I) (by simp) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at h
  refine le_trans h ?_
  rw [div_eq_mul_inv]
  gcongr
  rw [add_sq, sq_abs]
  nlinarith [abs_nonneg t]

/-- Mellin inversion for `f` at `σ`. -/
theorem mellinInv_eq (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    mellinInv σ (mellin (fun u : ℝ => (f u : ℂ))) y = (f y : ℂ) :=
  mellinInv_mellin_eq σ _ hy (mellinConvergent_of_tsupport hf.continuous ha hab σ)
    (mellin_integrable_line f hf a b ha hab σ) (continuous_ofReal.comp hf.continuous).continuousAt

end Main

end ArtinPrimitiveRoots.L92M
end

section
/-! # L92M_Line: the line integrals of `x^s Φ(s)/(s - w)` and `x^s Φ(s)` on `Re s = 2` (M2)

`G_w(t) = t^{-w} ∫_t^β u^{w-1} f(u) du` has Mellin transform `Φ(s)/(s - w)` (`Re s > Re w`),
and `G_w(t) = t^{-w} Φ(w)` for `t ≤ a/2`; Mellin inversion at `σ = 2` and `t = 1/x` gives M2a.
-/

namespace ArtinPrimitiveRoots.L92M

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval ContDiff

section Line

variable (f : ℝ → ℝ) (a b : ℝ)

/-- `h_w(u) = u^{w-1} f(u)`. -/
noncomputable def hw (w : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (w - 1) * (f u : ℂ)

/-- `P_w(t) = ∫_t^β h_w`. -/
noncomputable def Pw (w : ℂ) (t : ℝ) : ℂ := ∫ u in t..(max a b + 1), hw f w u

/-- `G_w(t) = t^{-w} P_w(t)`. -/
noncomputable def Gw (w : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (-w) * Pw f a b w t

variable {f a b}

lemma f_eq_zero_of_lt (_ha : 0 < a) (hab : tsupport f ⊆ Icc a b) {u : ℝ} (hu : u < a) :
    f u = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => absurd (hab h).1 (not_le.mpr hu)

lemma hw_continuous (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ) :
    Continuous (hw f w) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_or_ge u (a / 2) with hu | hu
  · have : hw f w =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show u < a by linarith)] with v hv
      simp [hw, f_eq_zero_of_lt ha hab hv]
    exact (continuousAt_const).congr this.symm
  · have hu0 : 0 < u := by linarith
    exact ((continuousAt_ofReal_cpow_const _ _ (Or.inr hu0.ne'))).mul
      (continuous_ofReal.comp hc).continuousAt

lemma Pw_hasDerivAt (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ)
    (t : ℝ) : HasDerivAt (Pw f a b w) (-hw f w t) t := by
  have hh := hw_continuous hc ha hab w
  exact intervalIntegral.integral_hasDerivAt_left (hh.intervalIntegrable _ _)
    (hh.stronglyMeasurableAtFilter _ _) hh.continuousAt

lemma Pw_continuous (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ) :
    Continuous (Pw f a b w) :=
  continuous_iff_continuousAt.mpr fun t => (Pw_hasDerivAt hc ha hab w t).continuousAt

lemma Pw_eq_zero (_hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ) {t : ℝ}
    (ht : max a b + 1 ≤ t) : Pw f a b w t = 0 := by
  unfold Pw
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)), intervalIntegral.integral_zero]
  intro u hu
  rw [uIcc_of_ge ht] at hu
  have : f u = 0 := vanish_of_tsupport ha hab u (fun h => absurd h.2 (not_lt.mpr hu.1))
  simp [hw, this]

lemma Pw_eq_mellin (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ) {t : ℝ}
    (ht : t ≤ a / 2) : Pw f a b w t = mellin (fun u => (f u : ℂ)) w := by
  have hh := hw_continuous hc ha hab w
  unfold Pw
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a / 2) (hh.intervalIntegrable _ _)
    (hh.intervalIntegrable _ _), mellin_eq_intervalIntegral ha hab]
  have : ∫ u in t..(a / 2), hw f w u = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)), intervalIntegral.integral_zero]
    intro u hu
    rw [uIcc_of_le ht] at hu
    simp [hw, f_eq_zero_of_lt ha hab (show u < a by linarith [hu.2])]
  rw [this, zero_add]
  rfl

lemma Gw_eq (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ) {t : ℝ}
    (ht : t ≤ a / 2) : Gw f a b w t = (t : ℂ) ^ (-w) * mellin (fun u => (f u : ℂ)) w := by
  rw [Gw, Pw_eq_mellin hc ha hab w ht]

lemma Gw_continuousAt (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ)
    {t : ℝ} (ht : 0 < t) : ContinuousAt (Gw f a b w) t :=
  (continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')).mul (Pw_continuous hc ha hab w).continuousAt

lemma cpow_sub_one_mul_cpow_neg {t : ℝ} (ht : 0 < t) (s w : ℂ) :
    (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-w) = (t : ℂ) ^ (s - w - 1) := by
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [← cpow_add _ _ htc]
  ring_nf

lemma mellinConvergent_Gw (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ)
    {s : ℂ} (hs : w.re < s.re) : MellinConvergent (Gw f a b w) s := by
  unfold MellinConvergent
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  -- on `(0, α]`
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • Gw f a b w t) (Ioc 0 α) := by
    have hint : IntegrableOn (fun t : ℝ => mellin (fun u => (f u : ℂ)) w * (t : ℂ) ^ (s - w - 1))
        (Ioc 0 α) := by
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ.1.le).mp
        (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))).const_mul _
    refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [smul_eq_mul]
    rw [Gw_eq hc ha hab w ht.2, ← mul_assoc, cpow_sub_one_mul_cpow_neg ht.1]
    ring
  -- on `[α, β]`
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • Gw f a b w t) (Icc α β) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hαβ.1 ht.1
    exact ((continuousAt_ofReal_cpow_const _ _ (Or.inr htpos.ne')).smul
      (Gw_continuousAt hc ha hab w htpos)).continuousWithinAt
  refine (h1.union h2).of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro t ht
  have ht1 : β < t := by
    by_contra hcon
    push Not at hcon
    rcases le_or_gt t α with h | h
    · exact ht.2 (Or.inl ⟨ht.1, h⟩)
    · exact ht.2 (Or.inr ⟨h.le, hcon⟩)
  simp [Gw, Pw_eq_zero hc ha hab w ht1.le]

lemma mellin_Gw (hc : Continuous f) (ha : 0 < a) (hab : tsupport f ⊆ Icc a b) (w : ℂ)
    {s : ℂ} (hs : w.re < s.re) :
    mellin (Gw f a b w) s = mellin (fun u => (f u : ℂ)) s / (s - w) := by
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  have hsw : s - w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hconv := mellinConvergent_Gw hc ha hab w hs
  set k : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) • Gw f a b w t with hk
  have hk0 : ∀ t, β < t → k t = 0 := fun t ht => by
    simp [hk, Gw, Pw_eq_zero hc ha hab w ht.le]
  have e1 : mellin (Gw f a b w) s = ∫ t in (0 : ℝ)..β, k t := by
    rw [mellin, intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht => ht.1) (fun t ht => hk0 t ?_)
    by_contra hcon
    exact ht.2 ⟨ht.1, not_lt.mp hcon⟩
  have hkint : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable k volume c d := by
    intro c d hc0 hcd
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcd]
    exact hconv.mono_set fun t ht => lt_of_le_of_lt hc0 ht.1
  rw [e1, ← intervalIntegral.integral_add_adjacent_intervals (b := α)
    (hkint 0 α le_rfl hαβ.1.le) (hkint α β hαβ.1.le hαβ.2.le)]
  -- the piece `(0, α]`
  have e2 : ∫ t in (0 : ℝ)..α, k t = mellin (fun u => (f u : ℂ)) w * ((α : ℂ) ^ (s - w) / (s - w)) := by
    rw [intervalIntegral.integral_of_le hαβ.1.le]
    have : ∫ t in Ioc 0 α, k t = ∫ t in Ioc 0 α, mellin (fun u => (f u : ℂ)) w * (t : ℂ) ^ (s - w - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      simp only [hk, smul_eq_mul]
      rw [Gw_eq hc ha hab w ht.2, ← mul_assoc, cpow_sub_one_mul_cpow_neg ht.1]
      ring
    rw [this, integral_const_mul, ← intervalIntegral.integral_of_le hαβ.1.le,
      integral_cpow (Or.inl (by simp; linarith))]
    have e : s - w - 1 + 1 = s - w := by ring
    rw [e, ofReal_zero, zero_cpow hsw, sub_zero]
  -- the piece `[α, β]`, by parts
  have hpos : ∀ t ∈ uIcc α β, 0 < t := by
    intro t ht
    rw [uIcc_of_le hαβ.2.le] at ht
    exact lt_of_lt_of_le hαβ.1 ht.1
  have e3 : ∫ t in α..β, k t = ∫ t in α..β, Pw f a b w t * (t : ℂ) ^ (s - w - 1) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [hk, smul_eq_mul, Gw]
    rw [← mul_assoc, cpow_sub_one_mul_cpow_neg (hpos t ht)]
    ring
  have hv : ∀ t ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s - w) / (s - w))
      ((t : ℂ) ^ (s - w - 1)) t := by
    intro t ht
    have := (hasDerivAt_ofReal_cpow (s - w) (hpos t ht)).div_const (s - w)
    rwa [mul_div_cancel_left₀ _ hsw] at this
  have hu : ∀ t ∈ uIcc α β, HasDerivAt (Pw f a b w) (-hw f w t) t :=
    fun t _ => Pw_hasDerivAt hc ha hab w t
  have hu' : IntervalIntegrable (fun t => -hw f w t) volume α β :=
    (hw_continuous hc ha hab w).neg.intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - w - 1)) volume α β :=
    ContinuousOn.intervalIntegrable ((cpow_continuousOn _).mono fun t ht => hpos t ht)
  rw [e3, intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv',
    Pw_eq_zero hc ha hab w le_rfl, Pw_eq_mellin hc ha hab w le_rfl]
  have e4 : ∫ t in α..β, -hw f w t * ((t : ℂ) ^ (s - w) / (s - w)) =
      -(∫ t in α..β, (t : ℂ) ^ (s - 1) * (f t : ℂ)) / (s - w) := by
    rw [neg_div, ← intervalIntegral.integral_div, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos t ht).ne'
    simp only [hw]
    have : (t : ℂ) ^ (w - 1) * (t : ℂ) ^ (s - w) = (t : ℂ) ^ (s - 1) := by
      rw [← cpow_add _ _ htc]; ring_nf
    rw [← this]
    ring
  rw [e4, ← mellin_eq_intervalIntegral ha hab, e2]
  ring

end Line


section Main

variable (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
  (hab : tsupport f ⊆ Set.Icc a b)

include hf ha hab

/-- M2a -/
theorem line_integral_div (x : ℝ) (hx : 2 / a ≤ x) (w : ℂ) (hw : w.re < 2) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (2 + t * I) * mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) /
        (2 + t * I - w)) ∧
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (x : ℂ) ^ (2 + t * I) *
        mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) / (2 + t * I - w) =
      (x : ℂ) ^ w * mellin (fun u : ℝ => (f u : ℂ)) w := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hxa : x⁻¹ ≤ a / 2 := by
    rw [inv_le_comm₀ hx0 (by positivity)]
    calc (a / 2)⁻¹ = 2 / a := by field_simp
      _ ≤ x := hx
  have hc := hf.continuous
  have hden : ∀ t : ℝ, (2 : ℂ) + t * I - w ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hline := mellin_integrable_line f hf a b ha hab 2
  have hvert : ∀ t : ℝ, mellin (Gw f a b w) (((2 : ℝ) : ℂ) + t * I) =
      mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) / (2 + t * I - w) := by
    intro t
    rw [mellin_Gw hc ha hab w (by simp; linarith)]
    simp
  -- integrability of `t ↦ Φ(2+it)/(2+it-w)`
  have hint : Integrable (fun t : ℝ => mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) / (2 + t * I - w)) := by
    have hcont : Continuous (fun t : ℝ => mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) / (2 + t * I - w)) :=
      ((mellin_differentiable f hf a b ha hab).continuous.comp (by fun_prop)).div
        (by fun_prop) hden
    refine Integrable.mono' (hline.norm.div_const (2 - w.re)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_div]
    have hle : 2 - w.re ≤ ‖(2 : ℂ) + t * I - w‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      simp only [sub_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      exact le_abs_self _
    have h2 : (0 : ℝ) < 2 - w.re := by linarith
    simp only [ofReal_ofNat] at hline ⊢
    exact div_le_div_of_nonneg_left (norm_nonneg _) h2 hle
  have hnormx : ∀ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I)‖ = x ^ (2 : ℝ) := by
    intro t
    rw [norm_cpow_eq_rpow_re_of_pos hx0]
    simp
  have hxcont : Continuous (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx0.ne'))
  constructor
  · have : Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * (mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) / (2 + t * I - w))) := by
      refine Integrable.mono' (hint.norm.const_mul (x ^ (2 : ℝ)))
        (hxcont.aestronglyMeasurable.mul hint.aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      rw [norm_mul, hnormx]
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    ring
  · -- Mellin inversion for `G_w` at `x⁻¹`
    have hinv := mellinInv_mellin_eq 2 (Gw f a b w) (inv_pos.mpr hx0)
      (mellinConvergent_Gw hc ha hab w (by simp; linarith))
      (by
        unfold VerticalIntegrable
        refine hint.congr (Eventually.of_forall fun t => ?_)
        simp only
        rw [hvert t])
      (Gw_continuousAt hc ha hab w (inv_pos.mpr hx0))
    rw [Gw_eq hc ha hab w hxa, ofReal_inv_cpow_neg hx0] at hinv
    rw [← hinv, mellinInv]
    rw [real_smul]
    congr 1
    · push_cast; ring
    · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [smul_eq_mul]
      rw [hvert t, ofReal_inv_cpow_neg hx0]
      push_cast
      ring

/-- M2b -/
theorem line_integral_eq_zero (x : ℝ) (hx : 2 / a ≤ x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (2 + t * I) * mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I)) ∧
    ∫ t : ℝ, (x : ℂ) ^ (2 + t * I) * mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) = 0 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hxa : x⁻¹ < a := by
    rw [inv_lt_comm₀ hx0 ha]
    calc a⁻¹ < 2 / a := by rw [inv_eq_one_div]; gcongr; norm_num
      _ ≤ x := hx
  have hline := mellin_integrable_line f hf a b ha hab 2
  have hnormx : ∀ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I)‖ = x ^ (2 : ℝ) := by
    intro t
    rw [norm_cpow_eq_rpow_re_of_pos hx0]
    simp
  have hxcont : Continuous (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx0.ne'))
  simp only [ofReal_ofNat] at hline
  constructor
  · refine Integrable.mono' (hline.norm.const_mul (x ^ (2 : ℝ)))
      (hxcont.aestronglyMeasurable.mul hline.aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, hnormx]
  · have hinv := mellinInv_eq f hf a b ha hab 2 (inv_pos.mpr hx0)
    rw [f_eq_zero_of_lt ha hab hxa, mellinInv] at hinv
    have h2pi : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
    rw [ofReal_zero, smul_eq_zero] at hinv
    rcases hinv with h | h
    · exact absurd h h2pi
    · rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [smul_eq_mul]
      rw [ofReal_inv_cpow_neg hx0]
      push_cast
      ring

end Main

end ArtinPrimitiveRoots.L92M
end

section
/-! # L92M_Primes: prime ideals of `𝓞 K` grouped by residue characteristic

For a nonzero prime `P` of `𝓞 K` let `resChar P = absNorm (P ∩ ℤ)`, a rational prime `p`, with
`absNorm P = p ^ f`, `f ≥ 1`. At most `n = [K : ℚ]` primes lie over each `p`
(`∑ e f = n`). Consequences: the type of nonzero primes is countable, `∑_P N P ^ (-σ) < ∞` for
`σ > 1`, and fiberwise sums over primes are at most `n` times the sum over rational primes.
-/

namespace ArtinPrimitiveRoots.L92M

open NumberField Ideal

variable {K : Type} [Field K] [NumberField K]

/-- Nonzero prime ideals of `𝓞 K`. -/
abbrev PI (K : Type) [Field K] [NumberField K] := {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}

lemma absNorm_ne_zero (P : PI K) : Ideal.absNorm P.1 ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.2.2

lemma two_le_absNorm (P : PI K) : 2 ≤ Ideal.absNorm P.1 := by
  have h0 := absNorm_ne_zero P
  have h1 : Ideal.absNorm P.1 ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.2.1.ne_top
  omega

instance countable_ideal : Countable (Ideal (𝓞 K)) := by
  have hU : Set.Countable (⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n}) :=
    Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
  have : (⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n}) = Set.univ := by
    ext I; simp
  rw [this] at hU
  exact Set.countable_univ_iff.mp hU

/-- The residue characteristic of a nonzero prime. -/
noncomputable def resChar (P : PI K) : ℕ := Ideal.absNorm (Ideal.under ℤ P.1)

lemma resChar_prime (P : PI K) : (resChar P).Prime := by
  have := P.2.1
  have : NeZero P.1 := ⟨P.2.2⟩
  exact Nat.absNorm_under_prime P.1

lemma resChar_pow (P : PI K) :
    resChar P ^ (P.1.inertiaDeg ℤ) = Ideal.absNorm P.1 ∧ 0 < P.1.inertiaDeg ℤ := by
  have := P.2.1
  have : P.1.LiesOver (Ideal.span {((resChar P : ℕ) : ℤ)}) := Int.liesOver_span_absNorm P.1
  exact ⟨Ideal.pow_inertiaDeg _ P.1, Ideal.inertiaDeg_pos P.1 ℤ⟩

lemma resChar_le_absNorm (P : PI K) : resChar P ≤ Ideal.absNorm P.1 := by
  obtain ⟨h1, h2⟩ := resChar_pow P
  rw [← h1]
  exact Nat.le_self_pow h2.ne' _

/-- At most `[K : ℚ]` primes of a finite set lie over a given rational prime. -/
lemma card_filter_resChar_le (p : ℕ) (hp : p.Prime) (T : Finset (PI K)) :
    (T.filter (fun P => resChar P = p)).card ≤ Module.finrank ℚ K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfin := IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) (𝓞 K)
  let : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := hfin.fintype
  have key := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank] at key
  have hmaps : ∀ P ∈ T.filter (fun P => resChar P = p),
      P.1 ∈ hfin.toFinset := by
    intro P hP
    have hr := (Finset.mem_filter.mp hP).2
    have := P.2.1
    have hl : P.1.LiesOver (Ideal.span {((Ideal.absNorm (Ideal.under ℤ P.1) : ℕ) : ℤ)}) :=
      Int.liesOver_span_absNorm P.1
    rw [Set.Finite.mem_toFinset]
    refine ⟨P.2.1, ?_⟩
    unfold resChar at hr
    rw [hr] at hl
    exact hl
  have h1 := Finset.card_le_card_of_injOn (fun P : PI K => P.1) hmaps
    (fun P _ Q _ h => Subtype.ext h)
  refine le_trans h1 ?_
  rw [Set.Finite.card_toFinset, ← key]
  calc Fintype.card ↑((Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
      = ∑ _q : ↑((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)), 1 := by simp
    _ ≤ _ := by
      refine Finset.sum_le_sum fun q _ => ?_
      have := q.2.1
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne'
        (Ideal.inertiaDeg_pos q.1 ℤ).ne')

/-- Fiberwise bound: `∑_{P ∈ T} g (p_P) ≤ n ∑_{p ∈ image} g p`. -/
lemma sum_resChar_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (T : Finset (PI K)) :
    ∑ P ∈ T, g (resChar P) ≤
      Module.finrank ℚ K * ∑ p ∈ T.image resChar, g p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := resChar) (t := T.image resChar)
    (fun P hP => Finset.mem_image_of_mem _ hP), Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨P₀, -, rfl⟩ := Finset.mem_image.mp hp
  rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]),
    Finset.sum_const, nsmul_eq_mul]
  gcongr
  · exact hg _
  · exact_mod_cast card_filter_resChar_le _ (resChar_prime P₀) T

/-- `∑_P N P ^ (-σ) < ∞` for `σ > 1`. -/
lemma summable_absNorm_rpow (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun P : PI K => (Ideal.absNorm P.1 : ℝ) ^ (-σ)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using
      Real.summable_nat_rpow_inv.mpr hσ
  refine summable_of_sum_le (c := Module.finrank ℚ K * ∑' n : ℕ, (n : ℝ) ^ (-σ))
    (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _) fun T => ?_
  calc ∑ P ∈ T, (Ideal.absNorm P.1 : ℝ) ^ (-σ)
      ≤ ∑ P ∈ T, ((resChar P : ℕ) : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun P _ => ?_
        refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by linarith)
        · exact_mod_cast (resChar_prime P).pos
        · exact_mod_cast resChar_le_absNorm P
    _ ≤ Module.finrank ℚ K * ∑ p ∈ T.image resChar, ((p : ℕ) : ℝ) ^ (-σ) :=
        sum_resChar_le (fun p => ((p : ℕ) : ℝ) ^ (-σ))
          (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _) T
    _ ≤ Module.finrank ℚ K * ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
        gcongr
        exact hs.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

end ArtinPrimitiveRoots.L92M
end

section
/-! # L92M_Small: the trivial bound `Θ(x) ≤ C n x` (M4)

Group the prime ideals by residue characteristic `p`: each `P | p` with `N P = p^e` contributes
at most `‖f‖_∞ · ⌊L/e⌋ · e log p ≤ ‖f‖_∞ L log p`, `L = log_p ⌊B x⌋`, at most `n` primes lie
over `p`, and `∑_{p ≤ m} log_p(m) log p = ψ(m) ≤ (log 4 + 4) m`.
-/

namespace ArtinPrimitiveRoots.L92M

open NumberField Ideal Chebyshev

lemma inner_le {K : Type} [Field K] [NumberField K] (f : ℝ → ℝ) (M B x : ℝ) (hM : ∀ t, f t ≤ M)
    (hM0 : 0 ≤ M) (hB : ∀ t, B < t → f t = 0) (hx : 0 < x) (P : PI K) :
    ∑' j : ℕ, Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) ≤
      M * ((Nat.log (resChar P) ⌊B * x⌋₊ : ℕ) * Real.log (resChar P)) := by
  obtain ⟨hpow, hepos⟩ := resChar_pow P
  set p := resChar P
  set e := P.1.inertiaDeg ℤ
  set N := Ideal.absNorm P.1
  set L := Nat.log p ⌊B * x⌋₊
  have hp := resChar_prime P
  have hterm : ∀ j ∉ Finset.range (L / e),
      Real.log N * f ((N : ℝ) ^ (j + 1) / x) = 0 := by
    intro j hj
    by_contra hne
    have hfne : f ((N : ℝ) ^ (j + 1) / x) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hle : (N : ℝ) ^ (j + 1) / x ≤ B := by
      by_contra hcon
      exact hfne (hB _ (not_le.mp hcon))
    have hle2 : N ^ (j + 1) ≤ ⌊B * x⌋₊ := by
      apply Nat.le_floor
      rw [div_le_iff₀ hx] at hle
      exact_mod_cast hle
    rw [← hpow, ← pow_mul] at hle2
    have h3 := Nat.le_log_of_pow_le hp.one_lt hle2
    have h4 : j + 1 ≤ L / e := (Nat.le_div_iff_mul_le hepos).mpr (by rw [mul_comm]; exact h3)
    exact hj (Finset.mem_range.mpr (by omega))
  rw [tsum_eq_sum hterm]
  have hlogN : Real.log N = e * Real.log p := by
    rw [← hpow]; push_cast; rw [Real.log_pow]
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
  calc ∑ j ∈ Finset.range (L / e), Real.log N * f ((N : ℝ) ^ (j + 1) / x)
      ≤ ∑ _j ∈ Finset.range (L / e), Real.log N * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (hM _) (by rw [hlogN]; positivity)
    _ = M * ((((L / e : ℕ) * e : ℕ) : ℝ) * Real.log p) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hlogN]; push_cast; ring
    _ ≤ M * ((L : ℝ) * Real.log p) := by
        gcongr
        exact_mod_cast Nat.div_mul_le_self L e

/-- M4 -/
theorem theta_le (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
    (hab : tsupport f ⊆ Set.Icc a b) (hf0 : ∀ t, 0 ≤ f t) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K], ∀ x : ℝ, 0 < x →
      ∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
          Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) ≤
        C * Module.finrank ℚ K * x := by
  classical
  obtain ⟨M₀, hM₀⟩ := hf.continuous.bounded_above_of_compact_support
    (hasCompactSupport_of_tsupport hab)
  set M := max M₀ 0
  set B := max b 1
  have hM : ∀ t, f t ≤ M := fun t =>
    le_trans (le_trans (le_abs_self _) (by simpa using hM₀ t)) (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hB : ∀ t, B < t → f t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := (hab h).2
      linarith [le_max_left b 1]
  have hB1 : 1 ≤ B := le_max_right _ _
  refine ⟨M * (Real.log 4 + 4) * B, fun K _ _ x hx => ?_⟩
  set m := ⌊B * x⌋₊
  set g : ℕ → ℝ := fun p => M * ((Nat.log p m : ℕ) * Real.log p) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => by
    simp only [hg]; have := Real.log_natCast_nonneg p; positivity
  have hpsi : ∑ p ∈ Nat.primesLE m, g p = M * ψ m := by
    rw [psi_eq_sum_mul_log_prime, Finset.mul_sum]
  have hpsi2 : ψ (m : ℝ) ≤ (Real.log 4 + 4) * (B * x) := by
    rw [← psi_eq_psi_coe_floor]
    exact psi_le_const_mul_self (by positivity)
  have hnn : ∀ P : PI K, 0 ≤ ∑' j : ℕ,
      Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) :=
    fun P => tsum_nonneg fun j => mul_nonneg (Real.log_natCast_nonneg _) (hf0 _)
  refine Real.tsum_le_of_sum_le hnn fun T => ?_
  calc ∑ P ∈ T, ∑' j : ℕ,
        Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x)
      ≤ ∑ P ∈ T, g (resChar P) :=
        Finset.sum_le_sum fun P _ => inner_le f M B x hM hM0 hB hx P
    _ ≤ Module.finrank ℚ K * ∑ p ∈ T.image resChar, g p := sum_resChar_le g hg0 T
    _ ≤ Module.finrank ℚ K * ∑ p ∈ Nat.primesLE m, g p := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [← Finset.sum_filter_of_ne (p := fun p => p ≤ m)]
        · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hg0 p)
          intro p hp
          obtain ⟨hpT, hpm⟩ := Finset.mem_filter.mp hp
          obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hpT
          exact Nat.mem_primesLE.mpr ⟨hpm, resChar_prime P⟩
        · intro p _ hne
          by_contra hpm
          apply hne
          simp only [hg, Nat.log_of_lt (not_le.mp hpm), Nat.cast_zero, zero_mul, mul_zero]
    _ = Module.finrank ℚ K * (M * ψ m) := by rw [hpsi]
    _ ≤ Module.finrank ℚ K * (M * ((Real.log 4 + 4) * (B * x))) := by gcongr
    _ = M * (Real.log 4 + 4) * B * Module.finrank ℚ K * x := by ring

end ArtinPrimitiveRoots.L92M
end

section
/-! # L92M_Euler: `-ζ_K'/ζ_K(s) = ∑_P log N P · N P^{-s} / (1 - N P^{-s})` for `Re s > 1`

From the library's Euler product for `ζ_K` (over `HeightOneSpectrum`) and its log-derivative
theorem for absolutely convergent Euler products.
-/

namespace ArtinPrimitiveRoots.L92M

open NumberField Complex Filter Topology

variable {K : Type} [Field K] [NumberField K]

/-- `PI K ≃ HeightOneSpectrum (𝓞 K)`. -/
def piEquiv : PI K ≃ IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  toFun P := ⟨P.1, P.2.1, P.2.2⟩
  invFun v := ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma dedekindZeta_eq_tprod (z : ℂ) (hz : 1 < z.re) :
    dedekindZeta K z = ∏' P : PI K, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-z))⁻¹ := by
  have h := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K z hz
  rw [← (piEquiv (K := K)).hasProd_iff] at h
  exact h.tprod_eq.symm

lemma neg_logDeriv_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun P : PI K => (Real.log (Ideal.absNorm P.1) : ℂ) *
        ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s) / (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)))
      (-logDeriv (dedekindZeta K) s) := by
  obtain ⟨-, -, h⟩ :=
    EulerProduct.differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
      (fun P : PI K => Ideal.absNorm P.1) two_le_absNorm (fun _ => 1) (fun _ => by simp)
      (fun σ hσ => summable_absNorm_rpow σ hσ) s hs
  simp only [one_mul] at h
  have heq : (fun z => ∏' P : PI K, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-z))⁻¹) =ᶠ[𝓝 s]
      dedekindZeta K := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact (dedekindZeta_eq_tprod z hz).symm
  rw [logDeriv_apply, ← heq.deriv_eq, dedekindZeta_eq_tprod s hs]
  exact h

lemma hasSum_geom_succ {ξ : ℂ} (h : ‖ξ‖ < 1) :
    HasSum (fun j : ℕ => ξ ^ (j + 1)) (ξ / (1 - ξ)) := by
  have := (hasSum_geometric_of_norm_lt_one h).mul_left ξ
  simpa [pow_succ', div_eq_mul_inv] using this

end ArtinPrimitiveRoots.L92M
end

section
/-! # L92M_Theta: `Θ(x) = (1/2π) ∫ (-ζ_K'/ζ_K)(2+it) x^{2+it} Φ(2+it) dt` (M1)

Mellin inversion on `Re s = 2` for each term `f(N P^{j+1}/x)`, then the sums over `j` and over
`P` are moved inside the integral (absolute convergence: `‖(N P)^{-s}‖ = N P^{-2}`), and the
Euler-product identity `∑_P log N P · N P^{-s}/(1 - N P^{-s}) = -ζ_K'/ζ_K(s)` closes it.
-/

namespace ArtinPrimitiveRoots.L92M

open NumberField Complex MeasureTheory Filter Topology

lemma natCast_div_cpow_neg {N : ℕ} (j : ℕ) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((((N : ℝ) ^ (j + 1) / x : ℝ)) : ℂ) ^ (-s) = ((N : ℂ) ^ (-s)) ^ (j + 1) * (x : ℂ) ^ s := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    ofReal_inv_cpow_neg hx]
  congr 1
  push_cast
  rw [← natCast_cpow_natCast_mul, ← cpow_nat_mul]

lemma continuous_cpow_line {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I)) :=
  continuous_iff_continuousAt.mpr fun _ =>
    ContinuousAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx.ne'))

lemma norm_cpow_line {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ ((2 : ℂ) + t * I)‖ = x ^ (2 : ℝ) := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]
  simp

section Defs

variable (f : ℝ → ℝ) (x : ℝ)

/-- `x^s Φ(s)` on `s = 2 + it`. -/
noncomputable def Xf (t : ℝ) : ℂ :=
  (x : ℂ) ^ ((2 : ℂ) + t * I) * mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)

/-- `n^{-s}` on `s = 2 + it`. -/
noncomputable def ξf (n : ℕ) (t : ℝ) : ℂ := (n : ℂ) ^ (-((2 : ℂ) + t * I))

/-- The `(P, j)` integrand. -/
noncomputable def gf (n j : ℕ) (t : ℝ) : ℂ := (Real.log n : ℂ) * ξf n t ^ (j + 1) * Xf f x t

/-- The `P` integrand (summed over `j`). -/
noncomputable def Ff (n : ℕ) (t : ℝ) : ℂ :=
  (Real.log n : ℂ) * (ξf n t / (1 - ξf n t)) * Xf f x t

end Defs

section Lemmas

variable {n : ℕ}

lemma norm_ξf (hn : 0 < n) (t : ℝ) : ‖ξf n t‖ = (n : ℝ) ^ (-2 : ℝ) := by
  rw [ξf, norm_natCast_cpow_of_pos hn]
  simp

lemma rpow_neg_two_le (hn : 2 ≤ n) : (n : ℝ) ^ (-2 : ℝ) ≤ 1 / 4 := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  exact inv_anti₀ (by norm_num) (by nlinarith)

lemma norm_ξf_lt (hn : 2 ≤ n) (t : ℝ) : ‖ξf n t‖ < 1 := by
  rw [norm_ξf (by omega)]; linarith [rpow_neg_two_le hn]

lemma continuous_ξf (hn : 0 < n) : Continuous (ξf n) :=
  continuous_iff_continuousAt.mpr fun _ =>
    ContinuousAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn.ne'))

end Lemmas

section Main

variable (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
  (hab : tsupport f ⊆ Set.Icc a b) {x : ℝ} (hx : 0 < x)

include hf ha hab hx

omit hx in
lemma line_integrable :
    Integrable (fun t : ℝ => mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)) := by
  simpa using mellin_integrable_line f hf a b ha hab 2

omit hx in
lemma line_continuous :
    Continuous (fun t : ℝ => mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)) :=
  (mellin_differentiable f hf a b ha hab).continuous.comp (by fun_prop)

lemma Xf_continuous : Continuous (Xf f x) :=
  (continuous_cpow_line hx).mul (line_continuous f hf a b ha hab)

omit hf ha hab in
lemma norm_Xf (t : ℝ) :
    ‖Xf f x t‖ = x ^ (2 : ℝ) * ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖ := by
  rw [Xf, norm_mul, norm_cpow_line hx]

omit hf ha hab in
lemma norm_gf {n : ℕ} (hn : 0 < n) (j : ℕ) (t : ℝ) :
    ‖gf f x n j t‖ = Real.log n * ((n : ℝ) ^ (-2 : ℝ)) ^ (j + 1) * x ^ (2 : ℝ) *
      ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖ := by
  rw [gf, norm_mul, norm_mul, norm_pow, norm_ξf hn, norm_Xf f hx, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg n)]
  ring

lemma gf_integrable {n : ℕ} (hn : 0 < n) (j : ℕ) : Integrable (gf f x n j) := by
  refine Integrable.mono' ((line_integrable f hf a b ha hab).norm.const_mul
    (Real.log n * ((n : ℝ) ^ (-2 : ℝ)) ^ (j + 1) * x ^ (2 : ℝ)))
    (((continuous_const.mul ((continuous_ξf hn).pow _)).mul
      (Xf_continuous f hf a b ha hab hx))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_gf f hx hn]

omit hf ha hab hx in
lemma integral_norm_gf {n : ℕ} (hn : 0 < n) (hx : 0 < x) (j : ℕ) :
    ∫ t, ‖gf f x n j t‖ = Real.log n * ((n : ℝ) ^ (-2 : ℝ)) ^ (j + 1) * x ^ (2 : ℝ) *
      ∫ t : ℝ, ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖ := by
  simp_rw [norm_gf f hx hn]
  rw [integral_const_mul]

omit hf ha hab hx in
lemma hasSum_gf {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    HasSum (fun j => gf f x n j t) (Ff f x n t) := by
  have := ((hasSum_geom_succ (norm_ξf_lt hn t)).mul_left (Real.log n : ℂ)).mul_right (Xf f x t)
  simpa only [gf, Ff, mul_assoc] using this

/-- The inner sum over `j` commutes with the integral. -/
lemma tsum_integral_gf {n : ℕ} (hn : 2 ≤ n) :
    ∑' j, ∫ t, gf f x n j t = ∫ t, Ff f x n t := by
  have hn0 : 0 < n := by omega
  rw [integral_tsum_of_summable_integral_norm (gf_integrable f hf a b ha hab hx hn0)]
  · exact integral_congr_ae (Eventually.of_forall fun t => (hasSum_gf f hn t).tsum_eq)
  · simp_rw [integral_norm_gf f hn0 hx]
    refine Summable.mul_right _ (Summable.mul_right _ (Summable.mul_left _ ?_))
    have := summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (-2 : ℝ))
      (by linarith [rpow_neg_two_le hn])
    exact (summable_nat_add_iff 1).mpr this

omit hf ha hab in
lemma norm_Ff_le {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    ‖Ff f x n t‖ ≤ 2 * Real.log n * (n : ℝ) ^ (-2 : ℝ) * x ^ (2 : ℝ) *
      ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖ := by
  have hn0 : 0 < n := by omega
  have hr := rpow_neg_two_le hn
  have hr0 : 0 ≤ (n : ℝ) ^ (-2 : ℝ) := by positivity
  have hlog := Real.log_natCast_nonneg n
  have h1ξ : 3 / 4 ≤ ‖1 - ξf n t‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ξf n t)
    rw [norm_one, norm_ξf hn0] at this
    linarith
  rw [Ff, norm_mul, norm_mul, norm_div, norm_Xf f hx, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, norm_ξf hn0]
  have hd : (n : ℝ) ^ (-2 : ℝ) / ‖1 - ξf n t‖ ≤ 2 * (n : ℝ) ^ (-2 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 ≤ x ^ (2 : ℝ) * ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖ := by
    positivity
  calc Real.log n * ((n : ℝ) ^ (-2 : ℝ) / ‖1 - ξf n t‖) *
        (x ^ (2 : ℝ) * ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖)
      ≤ Real.log n * (2 * (n : ℝ) ^ (-2 : ℝ)) *
        (x ^ (2 : ℝ) * ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖) := by gcongr
    _ = _ := by ring

lemma Ff_integrable {n : ℕ} (hn : 2 ≤ n) : Integrable (Ff f x n) := by
  have hn0 : 0 < n := by omega
  have hc : Continuous (Ff f x n) := by
    refine (continuous_const.mul ((continuous_ξf hn0).div
      (continuous_const.sub (continuous_ξf hn0)) fun t h0 => ?_)).mul
      (Xf_continuous f hf a b ha hab hx)
    have := norm_ξf_lt hn t
    rw [← sub_eq_zero.mp h0, norm_one] at this
    exact lt_irrefl _ this
  exact Integrable.mono' ((line_integrable f hf a b ha hab).norm.const_mul
    (2 * Real.log n * (n : ℝ) ^ (-2 : ℝ) * x ^ (2 : ℝ)))
    hc.aestronglyMeasurable (Eventually.of_forall fun t => norm_Ff_le f hx hn t)

lemma integral_norm_Ff_le {n : ℕ} (hn : 2 ≤ n) :
    ∫ t, ‖Ff f x n t‖ ≤ 4 * x ^ (2 : ℝ) *
      (∫ t : ℝ, ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖) *
        (n : ℝ) ^ (-(3 / 2) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set L := ∫ t : ℝ, ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖
  have hL0 : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  have h1 : ∫ t, ‖Ff f x n t‖ ≤ 2 * Real.log n * (n : ℝ) ^ (-2 : ℝ) * x ^ (2 : ℝ) * L := by
    rw [← integral_const_mul]
    exact integral_mono (Ff_integrable f hf a b ha hab hx hn).norm
      ((line_integrable f hf a b ha hab).norm.const_mul _) fun t => norm_Ff_le f hx hn t
  refine le_trans h1 ?_
  have hlog : Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have e : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-2 : ℝ) = (n : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  have hx2 : 0 ≤ x ^ (2 : ℝ) * L := by positivity
  calc 2 * Real.log n * (n : ℝ) ^ (-2 : ℝ) * x ^ (2 : ℝ) * L
      = 2 * Real.log n * (n : ℝ) ^ (-2 : ℝ) * (x ^ (2 : ℝ) * L) := by ring
    _ ≤ 2 * ((n : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2)) * (n : ℝ) ^ (-2 : ℝ) * (x ^ (2 : ℝ) * L) := by
        gcongr
    _ = 4 * x ^ (2 : ℝ) * L * (n : ℝ) ^ (-(3 / 2) : ℝ) := by rw [← e]; ring

/-- Mellin inversion for one term. -/
lemma term_eq {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (((Real.log n * f ((n : ℝ) ^ (j + 1) / x) : ℝ)) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ t, gf f x n j t := by
  have hy : 0 < (n : ℝ) ^ (j + 1) / x := by positivity
  have hinv := mellinInv_eq f hf a b ha hab 2 hy
  rw [mellinInv, real_smul] at hinv
  have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
  rw [ofReal_mul, ← hinv, hc, mul_left_comm, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [gf, ξf, Xf, smul_eq_mul, ofReal_ofNat]
  rw [natCast_div_cpow_neg j hx]
  ring

lemma theta_eq_integral_aux (K : Type) [Field K] [NumberField K] :
    ((∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
        Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) : ℝ) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, -logDeriv (dedekindZeta K) (2 + t * I) *
        (x : ℂ) ^ (2 + t * I) * mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) := by
  set L := ∫ t : ℝ, ‖mellin (fun u : ℝ => (f u : ℂ)) ((2 : ℂ) + t * I)‖
  have hFs : Summable (fun P : PI K => ∫ t, ‖Ff f x (Ideal.absNorm P.1) t‖) := by
    refine Summable.of_nonneg_of_le (fun P => integral_nonneg fun _ => norm_nonneg _)
      (fun P => integral_norm_Ff_le f hf a b ha hab hx (two_le_absNorm P))
      ((summable_absNorm_rpow (K := K) (3 / 2) (by norm_num)).mul_left (4 * x ^ (2 : ℝ) * L))
  have hsumF : ∀ t : ℝ, ∑' P : PI K, Ff f x (Ideal.absNorm P.1) t =
      -logDeriv (dedekindZeta K) ((2 : ℂ) + t * I) * Xf f x t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    refine HasSum.tsum_eq (((neg_logDeriv_hasSum ((2 : ℂ) + t * I) hs).mul_right
      (Xf f x t)).congr_fun fun P => ?_)
    simp only [Ff, ξf, mul_div_assoc]
  have e1 : ∀ P : PI K, ∑' j : ℕ, (((Real.log (Ideal.absNorm P.1) *
      f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) : ℝ)) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ t, Ff f x (Ideal.absNorm P.1) t := by
    intro P
    have hn := two_le_absNorm P
    simp_rw [term_eq f hf a b ha hab hx (n := Ideal.absNorm P.1) (by omega)]
    rw [tsum_mul_left, tsum_integral_gf f hf a b ha hab hx hn]
  rw [ofReal_tsum]
  simp_rw [ofReal_tsum, e1]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
    (fun P => Ff_integrable f hf a b ha hab hx (two_le_absNorm P)) hFs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [hsumF t, Xf]
  ring

end Main

/-- M1 -/
theorem theta_eq_integral (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
    (hab : tsupport f ⊆ Set.Icc a b) (K : Type) [Field K] [NumberField K] (x : ℝ) (hx : 0 < x) :
    ((∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
        Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) : ℝ) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, -logDeriv (dedekindZeta K) (2 + t * I) *
        (x : ℂ) ^ (2 + t * I) * mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) :=
  theta_eq_integral_aux f hf a b ha hab hx K

end ArtinPrimitiveRoots.L92M
end

section
/-! # L92Z: the Hadamard series `∑ ((s - ρ_j)⁻¹ + ρ_j⁻¹)`

General facts about a sequence `ρ : ℕ → ℂ` of nonzero points with `∑ |ρ_j|⁻² < ∞`: finitely many
`ρ_j` in each disc, isolation of each value, summability of the Hadamard series, and the fact that
every `ρ_j` is a zero of `Λ` when `logDeriv (z(z-1)Λ) = B + ∑ ((s - ρ_j)⁻¹ + ρ_j⁻¹)`. -/

open Filter Topology

namespace ArtinPrimitiveRoots.L92Z

theorem finite_norm_le (ρ : ℕ → ℂ) (hρ0 : ∀ j, ρ j ≠ 0)
    (hρsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹)) (R : ℝ) :
    {k | ‖ρ k‖ ≤ R}.Finite := by
  have ht : (0 : ℝ) < (R ^ 2 + 1)⁻¹ := by positivity
  have h := (hρsum.tendsto_cofinite_zero).eventually (gt_mem_nhds ht)
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun k hk => ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hk ⊢
  have hpos : 0 < Complex.normSq (ρ k) := Complex.normSq_pos.2 (hρ0 k)
  have : Complex.normSq (ρ k) ≤ R ^ 2 + 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have h0 := norm_nonneg (ρ k)
    nlinarith
  exact inv_anti₀ hpos this

theorem norm_inv_sub_add_inv_le {w r : ℂ} {c : ℝ} (hc : 0 < c) (hr : r ≠ 0)
    (h : c * ‖r‖ ≤ ‖w - r‖) :
    ‖(w - r)⁻¹ + r⁻¹‖ ≤ ‖w‖ / c * (Complex.normSq r)⁻¹ := by
  have hr' : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hcr : 0 < c * ‖r‖ := mul_pos hc hr'
  have hwr : 0 < ‖w - r‖ := lt_of_lt_of_le hcr h
  have hwr0 : w - r ≠ 0 := norm_pos_iff.1 hwr
  have e : (w - r)⁻¹ + r⁻¹ = w / ((w - r) * r) := by field_simp; ring
  rw [e, norm_div, norm_mul, Complex.normSq_eq_norm_sq]
  have e2 : ‖w‖ / c * (‖r‖ ^ 2)⁻¹ = ‖w‖ / (c * ‖r‖ * ‖r‖) := by
    field_simp
  rw [e2]
  exact div_le_div_of_nonneg_left (norm_nonneg w) (mul_pos hcr hr')
    (mul_le_mul_of_nonneg_right h hr'.le)

theorem le_norm_sub_of_le {w r : ℂ} {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hw : ‖w‖ ≤ R)
    (hwr : ε ≤ ‖w - r‖) : min (1 / 2) (ε / (2 * R + 1)) * ‖r‖ ≤ ‖w - r‖ := by
  by_cases h : 2 * R ≤ ‖r‖
  · calc min (1 / 2) (ε / (2 * R + 1)) * ‖r‖ ≤ (1 / 2) * ‖r‖ := by
          gcongr; exact min_le_left _ _
      _ ≤ ‖r‖ - ‖w‖ := by linarith
      _ ≤ ‖w - r‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le r w
  · push Not at h
    calc min (1 / 2) (ε / (2 * R + 1)) * ‖r‖ ≤ (ε / (2 * R + 1)) * (2 * R + 1) := by
          gcongr
          · exact min_le_right _ _
          · linarith
      _ = ε := by field_simp
      _ ≤ ‖w - r‖ := hwr

/-- Summability of the Hadamard series at any point. -/
theorem summable_hadamard (ρ : ℕ → ℂ) (hρ0 : ∀ j, ρ j ≠ 0)
    (hρsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹)) (s : ℂ) :
    Summable (fun j => (s - ρ j)⁻¹ + (ρ j)⁻¹) := by
  refine Summable.of_norm_bounded_eventually (hρsum.mul_left (‖s‖ / (1 / 2))) ?_
  have hfin := finite_norm_le ρ hρ0 hρsum (2 * ‖s‖)
  rw [Filter.eventually_cofinite]
  refine hfin.subset fun k hk => ?_
  simp only [Set.mem_ofPred_eq] at hk ⊢
  by_contra hlt
  push Not at hlt
  refine hk (norm_inv_sub_add_inv_le (by norm_num) (hρ0 k) ?_)
  have := norm_sub_norm_le (ρ k) s
  rw [norm_sub_rev] at this
  linarith

/-- Each value of `ρ` is isolated among the values of `ρ`. -/
theorem exists_sep (ρ : ℕ → ℂ) (hρ0 : ∀ j, ρ j ≠ 0)
    (hρsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹)) (z : ℂ) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ k, ρ k ≠ z → ε ≤ ‖ρ k - z‖ := by
  set T := {k | ‖ρ k‖ ≤ ‖z‖ + 1} with hTdef
  have hT : T.Finite := finite_norm_le ρ hρ0 hρsum _
  set P := ρ '' (T ∩ {k | ρ k ≠ z}) with hPdef
  have hP : P.Finite := (hT.subset Set.inter_subset_left).image ρ
  have hzP : z ∉ P := by rintro ⟨k, ⟨_, hk⟩, hkz⟩; exact hk hkz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hP.isClosed.isOpen_compl.mem_nhds hzP)
  refine ⟨min 1 r, lt_min one_pos hr, min_le_left _ _, fun k hk => ?_⟩
  by_cases hkT : k ∈ T
  · have hmem : ρ k ∈ P := ⟨k, ⟨hkT, hk⟩, rfl⟩
    have : ρ k ∉ Metric.ball z r := fun h => hball h hmem
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at this
    exact (min_le_right _ _).trans this
  · simp only [hTdef, Set.mem_ofPred_eq, not_le] at hkT
    have := norm_sub_norm_le (ρ k) z
    exact (min_le_left _ _).trans (by linarith)

/-- Every `ρ_j` is a zero of `Λ`: the Hadamard expansion has a pole at `ρ_j`. -/
theorem lambda_rho_eq_zero (Λ : ℂ → ℂ) (hΛdiff : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (B : ℂ) (ρ : ℕ → ℂ) (hρ : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hρsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv (fun z => z * (z - 1) * Λ z) s = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
    (j : ℕ) : Λ (ρ j) = 0 := by
  by_contra hΛz
  have hρ0 : ∀ k, ρ k ≠ 0 := fun k h => by
    have := (hρ k).1; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
  set z := ρ j with hz
  have hz0 : z ≠ 0 := hρ0 j
  have hz1 : z ≠ 1 := fun h => by
    have := (hρ j).2; rw [← hz, h, Complex.one_re] at this; exact lt_irrefl _ this
  set F : ℂ → ℂ := fun w => w * (w - 1) * Λ w with hF
  have hO : IsOpen ({(0 : ℂ), 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
  have hzO : z ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by simp [hz0, hz1]
  have hFd : DifferentiableOn ℂ F ({(0 : ℂ), 1}ᶜ) := fun w hw =>
    (differentiableWithinAt_id.mul (differentiableWithinAt_id.sub_const 1)).mul (hΛdiff w hw)
  have hFa : AnalyticAt ℂ F z := (hFd.analyticOnNhd hO) z hzO
  have hFz : F z ≠ 0 := by
    simp only [hF]
    exact mul_ne_zero (mul_ne_zero hz0 (sub_ne_zero.2 hz1)) hΛz
  have hcont : ContinuousAt (logDeriv F) z := by
    have e : logDeriv F = fun w => deriv F w / F w := rfl
    rw [e]
    exact hFa.deriv.continuousAt.div hFa.continuousAt hFz
  -- the left side, times `w - z`, tends to `0`
  have hL : Tendsto (fun w => (w - z) * logDeriv F w) (𝓝[≠] z) (𝓝 0) := by
    have hc : ContinuousAt (fun w => (w - z) * logDeriv F w) z :=
      (continuousAt_id.sub continuousAt_const).mul hcont
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- the right side, times `w - z`, tends to `#{k | ρ k = z}`
  obtain ⟨ε, hε, hε1, hsep⟩ := exists_sep ρ hρ0 hρsum z
  set R := ‖z‖ + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set c := min (1 / 2) ((ε / 2) / (2 * R + 1)) with hcdef
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  set C := max (R / c) ((1 + ‖z‖⁻¹) * Complex.normSq z) with hCdef
  set g : ℕ → ℂ := fun k => if ρ k = z then 1 else 0 with hgdef
  have hRt : Tendsto (fun w => ∑' k, (w - z) * ((w - ρ k)⁻¹ + (ρ k)⁻¹)) (𝓝[≠] z)
      (𝓝 (∑' k, g k)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun k => C * (Complex.normSq (ρ k))⁻¹) (hρsum.mul_left C) ?_ ?_
    · intro k
      by_cases hk : ρ k = z
      · simp only [hgdef, hk, if_true]
        have hev : ∀ᶠ w in 𝓝[≠] z, 1 + (w - z) * z⁻¹ = (w - z) * ((w - z)⁻¹ + z⁻¹) := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          have : w - z ≠ 0 := sub_ne_zero.2 hw
          field_simp
        refine Tendsto.congr' hev ?_
        have hc' : ContinuousAt (fun w => 1 + (w - z) * z⁻¹) z := by fun_prop
        have := hc'.tendsto
        simp only [sub_self, zero_mul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · simp only [hgdef, hk, if_false]
        have hk' : z - ρ k ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
        have hc' : ContinuousAt (fun w => (w - z) * ((w - ρ k)⁻¹ + (ρ k)⁻¹)) z :=
          (continuousAt_id.sub continuousAt_const).mul
            (((continuousAt_id.sub continuousAt_const).inv₀ hk').add continuousAt_const)
        have := hc'.tendsto
        simp only [sub_self, zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
    · have hball : Metric.ball z (ε / 2) ∈ 𝓝 z := Metric.ball_mem_nhds z (by positivity)
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with w hw hwz k
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hwz1 : ‖w - z‖ ≤ 1 := by linarith
      have hwR : ‖w‖ ≤ R := by
        have := norm_le_insert' w z
        have h2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
          calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
            _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        linarith
      by_cases hk : ρ k = z
      · rw [hk]
        have hwz' : w - z ≠ 0 := sub_ne_zero.2 hwz
        have e : (w - z) * ((w - z)⁻¹ + z⁻¹) = 1 + (w - z) * z⁻¹ := by field_simp
        rw [e]
        have hzpos : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
        calc ‖1 + (w - z) * z⁻¹‖ ≤ 1 + ‖w - z‖ * ‖z‖⁻¹ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_one, norm_mul, norm_inv]
          _ ≤ 1 + 1 * ‖z‖⁻¹ := by gcongr
          _ = (1 + ‖z‖⁻¹) * Complex.normSq z * (Complex.normSq z)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one, one_mul]
          _ ≤ C * (Complex.normSq z)⁻¹ := by
              gcongr
              exact le_max_right _ _
      · have hsepk : ε ≤ ‖ρ k - z‖ := hsep k hk
        have hwk : ε / 2 ≤ ‖w - ρ k‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (ρ k) w z
          rw [norm_sub_rev (ρ k) w] at this
          linarith
        have hcr := le_norm_sub_of_le hR0 (by positivity : (0 : ℝ) < ε / 2) hwR hwk
        have hb := norm_inv_sub_add_inv_le hc (hρ0 k) hcr
        have hn : 0 ≤ (Complex.normSq (ρ k))⁻¹ := inv_nonneg.2 (Complex.normSq_nonneg _)
        rw [norm_mul]
        calc ‖w - z‖ * ‖(w - ρ k)⁻¹ + (ρ k)⁻¹‖ ≤ 1 * (‖w‖ / c * (Complex.normSq (ρ k))⁻¹) :=
              mul_le_mul hwz1 hb (norm_nonneg _) zero_le_one
          _ ≤ R / c * (Complex.normSq (ρ k))⁻¹ := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hwR hc.le) hn
          _ ≤ C * (Complex.normSq (ρ k))⁻¹ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hn
  -- equality of the two sides near `z`
  have hev : ∀ᶠ w in 𝓝[≠] z, (w - z) * B + ∑' k, (w - z) * ((w - ρ k)⁻¹ + (ρ k)⁻¹) =
      (w - z) * logDeriv F w := by
    have hball : Metric.ball z (ε / 2) ∈ 𝓝 z := Metric.ball_mem_nhds z (by positivity)
    filter_upwards [nhdsWithin_le_nhds hball, nhdsWithin_le_nhds (hO.mem_nhds hzO),
      self_mem_nhdsWithin] with w hw hwO hwz
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw0 : w ≠ 0 := fun h => hwO (by simp [h])
    have hw1 : w ≠ 1 := fun h => hwO (by simp [h])
    have hwρ : ∀ k, w ≠ ρ k := by
      intro k hk
      by_cases hkz : ρ k = z
      · exact hwz (hk.trans hkz)
      · have := hsep k hkz
        rw [← hk] at this
        linarith
    rw [hexp w hw0 hw1 hwρ, mul_add, tsum_mul_left]
  have hRt' : Tendsto (fun w => (w - z) * logDeriv F w) (𝓝[≠] z) (𝓝 (0 * B + ∑' k, g k)) := by
    refine Tendsto.congr' hev (Tendsto.add ?_ hRt)
    have hc' : ContinuousAt (fun w => (w - z) * B) z := by fun_prop
    have := hc'.tendsto
    simp only [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have huniq := tendsto_nhds_unique hRt' hL
  rw [zero_mul, zero_add] at huniq
  -- but `∑' k, g k ≥ 1`
  set gr : ℕ → ℝ := fun k => if ρ k = z then 1 else 0 with hgrdef
  have hgr : ∀ k, g k = (gr k : ℂ) := fun k => by
    simp only [hgdef, hgrdef]; split_ifs <;> simp
  have hgrs : Summable gr := by
    apply summable_of_ne_finset_zero (s := (finite_norm_le ρ hρ0 hρsum ‖z‖).toFinset)
    intro k hk
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hk
    simp only [hgrdef]
    rw [if_neg]
    intro h; rw [h] at hk; exact lt_irrefl _ hk
  have h1 : (1 : ℝ) ≤ ∑' k, gr k := by
    have := hgrs.le_tsum j (fun k _ => by simp only [hgrdef]; split_ifs <;> norm_num)
    simp only [hgrdef] at this
    rwa [if_pos hz.symm] at this
  have : (∑' k, g k) = ((∑' k, gr k : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact tsum_congr hgr
  rw [this, Complex.ofReal_eq_zero] at huniq
  linarith

end ArtinPrimitiveRoots.L92Z
end

section
/-! # L92Z core: the logarithmic derivative of `z(z-1)Λ(z)` on `Re s > 1`

`logDeriv (z(z-1)Λ) s = 1/s + 1/(s-1) + ½ log D + r₁ ψℝ(s) + r₂ ψℂ(s) + ζ_K'/ζ_K(s)`, and at
`s = 2` its real part is at most `3/2 + ½ log D`. -/

open Filter Topology NumberField Complex Ideal

namespace ArtinPrimitiveRoots.L92Z

/-- `ζ_K` converges absolutely on `Re s > 1`. -/
theorem abscissa_dedekindZeta_le (K : Type) [Field K] [NumberField K] :
    LSeries.abscissaOfAbsConv
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

theorem differentiableAt_dedekindZeta (K : Type) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) : DifferentiableAt ℂ (dedekindZeta K) s :=
  (LSeries_hasDerivAt ((abscissa_dedekindZeta_le K).trans_lt
    (by exact_mod_cast hs))).differentiableAt

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have e : Gammaℝ = fun z => ((Gammaℝ z)⁻¹)⁻¹ := by funext z; rw [inv_inv]
  rw [e]
  exact (differentiable_Gammaℝ_inv s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))

theorem Gammaℂ_ne_zero_of_re_pos' {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  rw [Ne, cpow_eq_zero_iff]
  intro h
  exact mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) h.1

theorem differentiableAt_Gammaℂ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℂ s := by
  have e : Gammaℂ = fun z => ((Gammaℂ z)⁻¹)⁻¹ := by funext z; rw [inv_inv]
  rw [e]
  exact (differentiable_Gammaℂ_inv s).inv (inv_ne_zero (Gammaℂ_ne_zero_of_re_pos' hs))

theorem logDeriv_const_cpow {c : ℂ} (hc : c ≠ 0) (a s : ℂ) :
    logDeriv (fun z => c ^ (a * z)) s = Complex.log c * a := by
  have h : HasDerivAt (fun z => c ^ (a * z)) (c ^ (a * s) * Complex.log c * a) s := by
    have := ((hasDerivAt_id' s).const_mul a).const_cpow (c := c) (Or.inl hc)
    simpa using this
  rw [logDeriv_apply, h.deriv]
  have : c ^ (a * s) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hc h.1
  field_simp

/-- **Z0.** The logarithmic derivative of `ξ = z(z-1)Λ` on `Re s > 1`. -/
theorem logDeriv_xi_eq (K : Type) [Field K] [NumberField K] (Λ : ℂ → ℂ)
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s)
    (s : ℂ) (hs : 1 < s.re) :
    logDeriv (fun z => z * (z - 1) * Λ z) s =
      1 / s + 1 / (s - 1) + (1 / 2 : ℂ) * (Real.log |(discr K : ℝ)| : ℂ)
        + (InfinitePlace.nrRealPlaces K : ℂ) * logDeriv Complex.Gammaℝ s
        + (InfinitePlace.nrComplexPlaces K : ℂ) * logDeriv Complex.Gammaℂ s
        + logDeriv (dedekindZeta K) s := by
  set D : ℂ := (((|NumberField.discr K| : ℤ) : ℂ)) with hDdef
  set r1 := InfinitePlace.nrRealPlaces K
  set r2 := InfinitePlace.nrComplexPlaces K
  have hU : {z : ℂ | 1 < z.re} ∈ 𝓝 s := (isOpen_lt continuous_const continuous_re).mem_nhds hs
  have hEq : (fun z => z * (z - 1) * Λ z) =ᶠ[𝓝 s]
      (fun z => (z * (z - 1)) *
        (((D ^ ((1 / 2 : ℂ) * z) * Gammaℝ z ^ r1) * Gammaℂ z ^ r2) * dedekindZeta K z)) := by
    filter_upwards [hU] with z hz
    rw [hΛeq z hz, mul_comm (1 / 2 : ℂ) z, ← div_eq_mul_one_div]
  have hlog : logDeriv (fun z => z * (z - 1) * Λ z) s = logDeriv (fun z => (z * (z - 1)) *
        (((D ^ ((1 / 2 : ℂ) * z) * Gammaℝ z ^ r1) * Gammaℂ z ^ r2) * dedekindZeta K z)) s := by
    simp only [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
  rw [hlog]
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; rw [h, one_re] at hs; exact lt_irrefl _ hs
  have hres : 0 < s.re := by linarith
  have hD : D ≠ 0 := by
    rw [hDdef, Int.cast_ne_zero, abs_ne_zero]; exact discr_ne_zero K
  have nD : D ^ ((1 / 2 : ℂ) * s) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hD h.1
  have nR : Gammaℝ s ^ r1 ≠ 0 := pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hres)
  have nC : Gammaℂ s ^ r2 ≠ 0 := pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos' hres)
  have nZ : dedekindZeta K s ≠ 0 := NumberField.dedekindZeta_ne_zero_of_one_lt_re K hs
  have dD : DifferentiableAt ℂ (fun z => D ^ ((1 / 2 : ℂ) * z)) s :=
    (differentiableAt_id.const_mul _).const_cpow (Or.inl hD)
  have dR : DifferentiableAt ℂ (fun z => Gammaℝ z ^ r1) s := (differentiableAt_Gammaℝ hres).pow r1
  have dC : DifferentiableAt ℂ (fun z => Gammaℂ z ^ r2) s := (differentiableAt_Gammaℂ hres).pow r2
  have dZ := differentiableAt_dedekindZeta K hs
  rw [logDeriv_mul (f := fun z => z * (z - 1))
      (g := fun z => ((D ^ ((1 / 2 : ℂ) * z) * Gammaℝ z ^ r1) * Gammaℂ z ^ r2) * dedekindZeta K z)
      s (mul_ne_zero hs0 hs1)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero nD nR) nC) nZ) (by fun_prop)
      (((dD.mul dR).mul dC).mul dZ),
    logDeriv_mul (f := fun z => z) (g := fun z => z - 1) s hs0 hs1 (by fun_prop) (by fun_prop),
    logDeriv_mul (f := fun z => (D ^ ((1 / 2 : ℂ) * z) * Gammaℝ z ^ r1) * Gammaℂ z ^ r2)
      (g := dedekindZeta K) s (mul_ne_zero (mul_ne_zero nD nR) nC) nZ ((dD.mul dR).mul dC) dZ,
    logDeriv_mul (f := fun z => D ^ ((1 / 2 : ℂ) * z) * Gammaℝ z ^ r1)
      (g := fun z => Gammaℂ z ^ r2) s (mul_ne_zero nD nR) nC (dD.mul dR) dC,
    logDeriv_mul (f := fun z => D ^ ((1 / 2 : ℂ) * z)) (g := fun z => Gammaℝ z ^ r1) s nD nR dD dR,
    logDeriv_const_cpow hD, logDeriv_fun_pow (differentiableAt_Gammaℝ hres),
    logDeriv_fun_pow (differentiableAt_Gammaℂ hres)]
  have hl1 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  have hDlog : Complex.log D = (Real.log |(discr K : ℝ)| : ℂ) := by
    rw [ofReal_log (abs_nonneg _), hDdef]
    congr 1
    rw [← Int.cast_abs, ofReal_intCast]
  rw [hl1, logDeriv_id', hDlog]
  ring

/-- `ψℝ(2) = -½ log π - γ/2`. -/
theorem logDeriv_Gammaℝ_two :
    logDeriv Gammaℝ 2 = -(Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2 := by
  have e : Gammaℝ = fun z => (Real.pi : ℂ) ^ ((-1 / 2 : ℂ) * z) * Gamma (z / 2) := by
    funext z; rw [Gammaℝ_def]; congr 2; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have nA : (Real.pi : ℂ) ^ ((-1 / 2 : ℂ) * 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hπ h.1
  have nG : Gamma ((2 : ℂ) / 2) ≠ 0 := by norm_num
  have dA : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ ((-1 / 2 : ℂ) * z)) 2 :=
    (differentiableAt_id.const_mul _).const_cpow (Or.inl hπ)
  have dG : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) 2 := by
    refine (differentiableAt_Gamma _ ?_).comp (2 : ℂ) (differentiableAt_id.div_const 2)
    intro m h
    norm_num at h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  rw [e, logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ ((-1 / 2 : ℂ) * z))
    (g := fun z : ℂ => Gamma (z / 2)) 2 nA nG dA dG, logDeriv_const_cpow hπ]
  have hG : logDeriv (fun z : ℂ => Gamma (z / 2)) 2 = digamma 1 * (1 / 2) := by
    have := logDeriv_comp (f := Gamma) (g := fun z : ℂ => z / 2) (x := 2)
      (by
        refine differentiableAt_Gamma _ ?_
        intro m h; norm_num at h
        have := congrArg Complex.re h
        simp at this
        linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
      (differentiableAt_id.div_const 2)
    simp only [Function.comp_def] at this
    rw [this, deriv_div_const, deriv_id'']
    norm_num [digamma_def]
  rw [hG, digamma_one, ← ofReal_log Real.pi_pos.le]
  ring

/-- `ψℂ(2) = -log 2π + 1 - γ`. -/
theorem logDeriv_Gammaℂ_two :
    logDeriv Gammaℂ 2 =
      -(Real.log (2 * Real.pi) : ℂ) + 1 - (Real.eulerMascheroniConstant : ℂ) := by
  have e : Gammaℂ = fun z => 2 * ((2 * (Real.pi : ℂ)) ^ ((-1 : ℂ) * z) * Gamma z) := by
    funext z; rw [Gammaℂ_def, mul_assoc]; congr 3; ring
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  have nA : (2 * (Real.pi : ℂ)) ^ ((-1 : ℂ) * 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => h2π h.1
  have nG : Gamma (2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have dA : DifferentiableAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ ((-1 : ℂ) * z)) 2 :=
    (differentiableAt_id.const_mul _).const_cpow (Or.inl h2π)
  have dG : DifferentiableAt ℂ Gamma 2 := by
    refine differentiableAt_Gamma _ ?_
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  rw [e, logDeriv_const_mul _ _ two_ne_zero,
    logDeriv_mul (f := fun z : ℂ => (2 * (Real.pi : ℂ)) ^ ((-1 : ℂ) * z)) (g := Gamma) 2 nA nG dA dG,
    logDeriv_const_cpow h2π]
  have hd : logDeriv Gamma 2 = 1 - (Real.eulerMascheroniConstant : ℂ) := by
    have := digamma_apply_add_one 1 (by
      intro m h
      have := congrArg Complex.re h
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    rw [digamma_one] at this
    rw [← digamma_def, show (2 : ℂ) = 1 + 1 by norm_num, this]
    ring
  have hl : Complex.log (2 * (Real.pi : ℂ)) = (Real.log (2 * Real.pi) : ℂ) := by
    rw [ofReal_log (by positivity)]; push_cast; rfl
  rw [hd, hl]
  ring

theorem re_logDeriv_Gammaℝ_two_nonpos : (logDeriv Gammaℝ 2).re ≤ 0 := by
  rw [logDeriv_Gammaℝ_two]
  have h1 : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have h2 : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  simp
  linarith

theorem re_logDeriv_Gammaℂ_two_nonpos : (logDeriv Gammaℂ 2).re ≤ 0 := by
  rw [logDeriv_Gammaℂ_two]
  have h1 : 1 ≤ Real.log (2 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith [Real.pi_gt_three]
  have h2 : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  simp
  linarith

open scoped ComplexOrder in
/-- `ζ_K'/ζ_K(2) ≤ 0`. -/
theorem re_logDeriv_dedekindZeta_two_nonpos (K : Type) [Field K] [NumberField K] :
    (logDeriv (dedekindZeta K) 2).re ≤ 0 := by
  set a : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ) with ha
  have hab : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) :=
    (abscissa_dedekindZeta_le K).trans_lt (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have ha0 : 0 ≤ a := fun n => by simp [ha]
  have h0 := LSeries.iteratedDeriv_alternating ha0 hab 0
  have h1 := LSeries.iteratedDeriv_alternating ha0 hab 1
  have hZ : dedekindZeta K = LSeries a := rfl
  simp only [pow_zero, one_mul, iteratedDeriv_zero, pow_one, neg_one_mul, iteratedDeriv_one,
    ofReal_ofNat] at h0 h1
  rw [← hZ] at h0 h1
  rw [logDeriv_apply]
  set Z := dedekindZeta K 2
  set D' := deriv (dedekindZeta K) 2
  obtain ⟨hZre, hZim⟩ := Complex.nonneg_iff.1 h0
  have h1' : 0 ≤ -D' := by simpa using h1
  obtain ⟨hDre, hDim⟩ := Complex.nonneg_iff.1 h1'
  have eZ : Z = (Z.re : ℂ) := Complex.ext (by simp) (by simp [← hZim])
  have eD : D' = (D'.re : ℂ) := Complex.ext (by simp) (by simp at hDim; simp [hDim])
  have : D' / Z = ((D'.re / Z.re : ℝ) : ℂ) := by
    rw [ofReal_div, ← eD, ← eZ]
  rw [this, ofReal_re]
  have := div_nonneg hDre hZre
  rw [neg_re, neg_div] at this
  linarith

end ArtinPrimitiveRoots.L92Z
end

section
/-! # L92Z: the zero side of Lemma 9.2 (Z1, Z2, Z3)

For `Λ` from `NumberField.exists_completedDedekindZeta_package` and `(B, ρ)` from
`NumberField.exists_hadamard_logDeriv_expansion_of_completedZeta_package`:
* Z1 `sum_re_inv_two_sub_le`: `∑ Re 1/(2 - ρ_j) ≤ log |d_K| + 3`;
* Z2 `re_le_of_dedekindZeroFreeRight`: a zero-free region `Re s > σ` contains no `ρ_j`;
* Z3 `neg_logDeriv_dedekindZeta_eq`: the explicit formula for `-ζ_K'/ζ_K` on `Re s > 1`. -/

open Filter Topology NumberField Complex

namespace ArtinPrimitiveRoots.L92Z

/-- **Z3.** The explicit formula for `-ζ_K'/ζ_K` on `Re s > 1`. -/
theorem neg_logDeriv_dedekindZeta_eq (K : Type) [Field K] [NumberField K] (Λ : ℂ → ℂ)
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s)
    (B : ℂ) (ρ : ℕ → ℂ) (hρ : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv (fun z => z * (z - 1) * Λ z) s = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
    (s : ℂ) (hs : 1 < s.re) :
    -logDeriv (NumberField.dedekindZeta K) s =
      -B - ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹) + 1 / s + 1 / (s - 1)
        + (1 / 2 : ℂ) * (Real.log |(discr K : ℝ)| : ℂ)
        + (InfinitePlace.nrRealPlaces K : ℂ) * logDeriv Complex.Gammaℝ s
        + (InfinitePlace.nrComplexPlaces K : ℂ) * logDeriv Complex.Gammaℂ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl _ hs
  have hsρ : ∀ j, s ≠ ρ j := fun j h => by
    have := (hρ j).2; rw [← h] at this; linarith
  have h2 := logDeriv_xi_eq K Λ hΛeq s hs
  rw [hexp s hs0 hs1 hsρ] at h2
  linear_combination h2

/-- **Z1.** `∑_j Re 1/(2 - ρ_j) ≤ log |d_K| + 3`, summably. -/
theorem sum_re_inv_two_sub_le (K : Type) [Field K] [NumberField K] (Λ : ℂ → ℂ)
    (hΛFE : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s)
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s)
    (B : ℂ) (ρ : ℕ → ℂ) (hρ : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hρsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv (fun z => z * (z - 1) * Λ z) s = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)) :
    Summable (fun j => (1 / (2 - ρ j)).re) ∧
      ∑' j, (1 / (2 - ρ j)).re ≤ Real.log |(discr K : ℝ)| + 3 := by
  have hρ0 : ∀ k, ρ k ≠ 0 := fun k h => by
    have := (hρ k).1; rw [h, zero_re] at this; exact lt_irrefl _ this
  set F : ℂ → ℂ := fun w => w * (w - 1) * Λ w with hF
  -- the functional equation: `logDeriv F (-1) = - logDeriv F 2`
  have hFE : logDeriv F (-1) = -logDeriv F 2 := by
    have hO : IsOpen ({(0 : ℂ), 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
    have hev : (fun w => F (1 - w)) =ᶠ[𝓝 2] F := by
      have : ({(0 : ℂ), 1}ᶜ : Set ℂ) ∈ 𝓝 (2 : ℂ) := hO.mem_nhds (by norm_num)
      filter_upwards [this] with w hw
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
      simp only [hF]
      rw [hΛFE w hw.1 hw.2]; ring
    have hd : deriv F 2 = -deriv F (-1) := by
      rw [← hev.deriv_eq, deriv_comp_const_sub]; norm_num
    have hv : F (-1) = F 2 := by
      have := hev.eq_of_nhds; norm_num at this; exact this
    rw [logDeriv_apply, logDeriv_apply, hd, hv]; ring
  have h2ρ : ∀ j, (2 : ℂ) ≠ ρ j := fun j h => by
    have := (hρ j).2; rw [← h] at this; norm_num at this
  have hm1ρ : ∀ j, (-1 : ℂ) ≠ ρ j := fun j h => by
    have := (hρ j).1; rw [← h] at this; norm_num at this
  have hA := hexp 2 two_ne_zero (by norm_num) h2ρ
  have hB := hexp (-1) (by norm_num) (by norm_num) hm1ρ
  have hsa := summable_hadamard ρ hρ0 hρsum 2
  have hsb := summable_hadamard ρ hρ0 hρsum (-1)
  set u : ℕ → ℂ := fun j => (2 - ρ j)⁻¹ + (1 + ρ j)⁻¹ with hu
  have hue : u = fun j => ((2 - ρ j)⁻¹ + (ρ j)⁻¹) - ((-1 - ρ j)⁻¹ + (ρ j)⁻¹) := by
    funext j
    simp only [hu]
    have : (-1 - ρ j) = -(1 + ρ j) := by ring
    rw [this, inv_neg]; ring
  have hsu : HasSum u (2 * logDeriv F 2) := by
    have hA' : logDeriv F 2 = B + ∑' j, ((2 - ρ j)⁻¹ + (ρ j)⁻¹) := hA
    have hB' : logDeriv F (-1) = B + ∑' j, ((-1 - ρ j)⁻¹ + (ρ j)⁻¹) := hB
    rw [hFE] at hB'
    have e : 2 * logDeriv F 2 =
        (∑' j, ((2 - ρ j)⁻¹ + (ρ j)⁻¹)) - ∑' j, ((-1 - ρ j)⁻¹ + (ρ j)⁻¹) := by
      linear_combination hA' - hB'
    rw [hue, e]
    exact hsa.hasSum.sub hsb.hasSum
  have hsur : HasSum (fun j => (u j).re) (2 * logDeriv F 2).re := Complex.hasSum_re hsu
  -- real parts
  have hre1 : ∀ j, 0 ≤ (1 / (2 - ρ j)).re := fun j => by
    rw [one_div, inv_re]
    exact div_nonneg (by simp; linarith [(hρ j).2]) (normSq_nonneg _)
  have hre2 : ∀ j, (1 / (2 - ρ j)).re ≤ (u j).re := fun j => by
    simp only [hu, add_re, one_div]
    have : 0 ≤ ((1 + ρ j)⁻¹).re := by
      rw [inv_re]
      exact div_nonneg (by simp; linarith [(hρ j).1]) (normSq_nonneg _)
    linarith
  have hsum1 : Summable (fun j => (1 / (2 - ρ j)).re) :=
    Summable.of_nonneg_of_le hre1 hre2 hsur.summable
  refine ⟨hsum1, ?_⟩
  have hle : ∑' j, (1 / (2 - ρ j)).re ≤ (2 * logDeriv F 2).re := by
    rw [← hsur.tsum_eq]; exact hsum1.tsum_le_tsum hre2 hsur.summable
  -- `Re logDeriv F 2 ≤ 3/2 + ½ log D`
  have h0 := logDeriv_xi_eq K Λ hΛeq 2 (by norm_num)
  have hR := re_logDeriv_Gammaℝ_two_nonpos
  have hC := re_logDeriv_Gammaℂ_two_nonpos
  have hZ := re_logDeriv_dedekindZeta_two_nonpos K
  have hre : (logDeriv F 2).re ≤ 3 / 2 + Real.log |(discr K : ℝ)| / 2 := by
    have e : logDeriv F 2 = _ := h0
    rw [e]
    simp only [add_re, mul_re, div_re, one_re, ofReal_re, ofReal_im, natCast_re, natCast_im]
    norm_num
    have hr1 : (0 : ℝ) ≤ (InfinitePlace.nrRealPlaces K : ℝ) := Nat.cast_nonneg _
    have hr2 : (0 : ℝ) ≤ (InfinitePlace.nrComplexPlaces K : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hr1 hR, mul_nonpos_of_nonneg_of_nonpos hr2 hC]
  have : (2 * logDeriv F 2).re = 2 * (logDeriv F 2).re := by simp
  linarith

/-- The union of four convex pieces: `{Re s > m} ∖ {1}` is preconnected for `m < 1`. -/
theorem isPreconnected_halfPlane_diff_one {m : ℝ} (hm : m < 1) :
    IsPreconnected ({z : ℂ | m < z.re} \ {1}) := by
  set A := {z : ℂ | m < z.re ∧ 0 < z.im}
  set C := {z : ℂ | m < z.re ∧ z.im < 0}
  set S1 := {z : ℂ | m < z.re ∧ z.re < 1}
  set S2 := {z : ℂ | 1 < z.re}
  have cA : Convex ℝ A := (convex_halfSpace_re_gt m).inter (convex_halfSpace_im_gt 0)
  have cC : Convex ℝ C := (convex_halfSpace_re_gt m).inter (convex_halfSpace_im_lt 0)
  have cS1 : Convex ℝ S1 := (convex_halfSpace_re_gt m).inter (convex_halfSpace_re_lt 1)
  have cS2 : Convex ℝ S2 := convex_halfSpace_re_gt 1
  set p : ℂ := ⟨(m + 1) / 2, 1⟩
  set q : ℂ := ⟨(m + 1) / 2, -1⟩
  set t : ℂ := ⟨2, 1⟩
  have h1 : IsPreconnected (A ∪ S1) :=
    IsPreconnected.union p (by simp [A, p]; linarith) (by simp [S1, p]; constructor <;> linarith)
      cA.isPreconnected cS1.isPreconnected
  have h2 : IsPreconnected ((A ∪ S1) ∪ S2) :=
    IsPreconnected.union t (Or.inl (by simp [A, t]; linarith)) (by simp [S2, t]) h1
      cS2.isPreconnected
  have h3 : IsPreconnected (((A ∪ S1) ∪ S2) ∪ C) :=
    IsPreconnected.union q (Or.inl (Or.inr (by simp [S1, q]; constructor <;> linarith)))
      (by simp [C, q]; linarith) h2 cC.isPreconnected
  convert h3 using 1
  ext z
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_union, A, C, S1, S2]
  constructor
  · rintro ⟨hz, hz1⟩
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact Or.inr ⟨hz, h⟩
    · rcases lt_trichotomy z.re 1 with h' | h' | h'
      · exact Or.inl (Or.inl (Or.inr ⟨hz, h'⟩))
      · exact absurd (Complex.ext (by simpa using h') (by simpa using h)) hz1
      · exact Or.inl (Or.inr h')
    · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
  · rintro (((⟨hz, h⟩ | ⟨hz, h⟩) | h) | ⟨hz, h⟩)
    · exact ⟨hz, fun e => by rw [e] at h; simp at h⟩
    · exact ⟨hz, fun e => by rw [e] at h; simp at h⟩
    · exact ⟨by linarith, fun e => by rw [e] at h; simp at h⟩
    · exact ⟨hz, fun e => by rw [e] at h; simp at h⟩

/-- On a zero-free region, `Λ` does not vanish. -/
theorem lambda_ne_zero_of_dedekindZeroFreeRight (K : Type) [Field K] [NumberField K]
    (Λ : ℂ → ℂ) (hΛdiff : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s)
    (σ : ℝ) (hσ : σ < 1) (hZ : DedekindZeroFreeRight K σ) (z : ℂ) (hz : max σ 0 < z.re)
    (hz1 : z ≠ 1) : Λ z ≠ 0 := by
  obtain ⟨g, hgd, hgζ, hg0⟩ := hZ
  set m := max σ 0 with hm
  have hm1 : m < 1 := max_lt hσ one_pos
  set U := {w : ℂ | m < w.re} \ {1} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hUc : IsPreconnected U := isPreconnected_halfPlane_diff_one hm1
  set D : ℂ := (((|NumberField.discr K| : ℤ) : ℂ)) with hDdef
  set h : ℂ → ℂ := fun w => D ^ (w / 2) * Gammaℝ w ^ InfinitePlace.nrRealPlaces K
      * Gammaℂ w ^ InfinitePlace.nrComplexPlaces K * g w with hh
  have hD : D ≠ 0 := by
    rw [hDdef, Int.cast_ne_zero, abs_ne_zero]; exact discr_ne_zero K
  have hmemU : ∀ w ∈ U, 0 < w.re ∧ σ < w.re ∧ w ≠ 1 := fun w hw =>
    ⟨lt_of_le_of_lt (le_max_right _ _) hw.1, lt_of_le_of_lt (le_max_left _ _) hw.1, hw.2⟩
  have hΛa : AnalyticOnNhd ℂ Λ U := by
    refine (hΛdiff.mono fun w hw => ?_).analyticOnNhd hUo
    obtain ⟨h0, -, h1⟩ := hmemU w hw
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun e => by rw [e, zero_re] at h0; exact lt_irrefl _ h0, h1⟩
  have hha : AnalyticOnNhd ℂ h U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    obtain ⟨h0, hσw, h1⟩ := hmemU w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    have hopen : IsOpen {s : ℂ | σ < s.re ∧ s ≠ 1} :=
      (isOpen_lt continuous_const continuous_re).inter isOpen_ne
    have dg : DifferentiableAt ℂ g w :=
      (hgd w ⟨hσw, h1⟩).differentiableAt (hopen.mem_nhds ⟨hσw, h1⟩)
    exact ((((differentiableAt_id.div_const 2).const_cpow (Or.inl hD)).mul
      ((differentiableAt_Gammaℝ h0).pow _)).mul ((differentiableAt_Gammaℂ h0).pow _)).mul dg
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; linarith, by norm_num⟩
  have hev : Λ =ᶠ[𝓝 2] h := by
    have : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with w hw
    rw [hΛeq w hw]; simp only [hh]; rw [hgζ w hw]
  have hEq := hΛa.eqOn_of_preconnected_of_eventuallyEq hha hUc h2U hev
  have hzU : z ∈ U := ⟨hz, hz1⟩
  rw [hEq hzU]
  obtain ⟨h0, hσz, -⟩ := hmemU z hzU
  simp only [hh]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (hg0 z hσz hz1)
  · rw [Ne, cpow_eq_zero_iff]; exact fun e => hD e.1
  · exact pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos h0)
  · exact pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos' h0)

/-- **Z2.** A zero-free region `Re s > σ` for `ζ_K` contains no `ρ_j`. -/
theorem re_le_of_dedekindZeroFreeRight (K : Type) [Field K] [NumberField K] (Λ : ℂ → ℂ)
    (hΛdiff : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s)
    (B : ℂ) (ρ : ℕ → ℂ) (hρ : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hρsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv (fun z => z * (z - 1) * Λ z) s = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
    (σ : ℝ) (hZ : DedekindZeroFreeRight K σ) (j : ℕ) : (ρ j).re ≤ σ := by
  by_contra hlt
  push Not at hlt
  have hσ : σ < 1 := lt_trans hlt (hρ j).2
  have hz1 : ρ j ≠ 1 := fun e => by
    have := (hρ j).2; rw [e, one_re] at this; exact lt_irrefl _ this
  exact lambda_ne_zero_of_dedekindZeroFreeRight K Λ hΛdiff hΛeq σ hσ hZ (ρ j)
    (max_lt hlt (hρ j).1) hz1 (lambda_rho_eq_zero Λ hΛdiff B ρ hρ hρsum hexp j)

end ArtinPrimitiveRoots.L92Z
end

section
/-! # L92A: the digamma series and the log-derivatives of `Γℝ`, `Γℂ`

`ψ(z) = -γ + ∑_{k ≥ 0} (1/(k+1) - 1/(z+k))` for `Re z > 0`: on the positive reals from the
convexity of `log Γ` (as in Mathlib's `Real.deriv_Gamma_nat`), then by the identity theorem. -/

namespace ArtinPrimitiveRoots

open Filter Topology

/-- The digamma series on the positive reals, with `deriv (log ∘ Γ)`. -/
theorem L92A_real_hasSum_digamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / (x + k))
      (deriv (Real.log ∘ Real.Gamma) x + Real.eulerMascheroniConstant) := by
  set f := Real.log ∘ Real.Gamma with hf
  have hc : ConvexOn ℝ (Set.Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (y : ℝ) (hy : 0 < y) : f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  have hder_rec (y : ℝ) (hy : 0 < y) : deriv f (y + 1) = deriv f y + 1 / y := by
    rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
      ← deriv_add (hder hy) (Real.differentiableAt_log hy.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hy] using h_rec
  have hiter (N : ℕ) :
      deriv f (x + N) = deriv f x + ∑ k ∈ Finset.range N, 1 / (x + k) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc, hder_rec _ (by positivity), ih]
      ring
  have hLB (N : ℕ) (hN : 1 ≤ N) : Real.log (x + N - 1) ≤ deriv f (x + N) := by
    have h1 : (0 : ℝ) < x + N - 1 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    refine (le_of_eq ?_).trans <| hc.slope_le_deriv (Set.mem_Ioi.mpr h1)
      (Set.mem_Ioi.mpr (by positivity)) (by linarith) (hder (by positivity))
    have := h_rec _ h1
    rw [show x + N - 1 + 1 = x + (N : ℝ) by ring] at this
    rw [slope_def_field, show x + N - (x + N - 1) = (1 : ℝ) by ring, div_one, this]
    ring
  have hUB (N : ℕ) : deriv f (x + N) ≤ Real.log (x + N) := by
    refine (hc.deriv_le_slope (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < x + N + 1)) (by linarith)
      (hder (by positivity))).trans (le_of_eq ?_)
    rw [slope_def_field, show x + N + 1 - (x + N) = (1 : ℝ) by ring, div_one,
      h_rec _ (by positivity), add_sub_cancel_left]
  -- summability
  have hm : 0 < min x 1 := lt_min hx one_pos
  have hbound (k : ℕ) : ‖1 / ((k : ℝ) + 1) - 1 / (x + k)‖ ≤
      |x - 1| / min x 1 * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have hxk : min x 1 * ((k : ℝ) + 1) ≤ x + k := by
      rcases le_total x 1 with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; linarith
    have hxk0 : 0 < x + k := by positivity
    rw [Real.norm_eq_abs, show 1 / ((k : ℝ) + 1) - 1 / (x + k) = (x - 1) / ((k + 1) * (x + k))
      by field_simp; ring, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k + 1) * (x + k))]
    rw [div_le_iff₀ (by positivity)]
    calc |x - 1| = |x - 1| / min x 1 * (1 / ((k : ℝ) + 1) ^ 2) *
          (min x 1 * ((k : ℝ) + 1) * ((k : ℝ) + 1)) := by field_simp
      _ ≤ |x - 1| / min x 1 * (1 / ((k : ℝ) + 1) ^ 2) * ((x + k) * ((k : ℝ) + 1)) := by
          gcongr
      _ = _ := by ring
  have hsum2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  have hS : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / (x + k)) :=
    Summable.of_norm_bounded (hsum2.mul_left _) hbound
  rw [hS.hasSum_iff_tendsto_nat]
  -- partial sums
  have hpart (N : ℕ) : ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) - 1 / (x + k)) =
      deriv f x + ((harmonic N : ℝ) - Real.log N) - (deriv f (x + N) - Real.log N) := by
    rw [Finset.sum_sub_distrib, hiter N]
    simp only [harmonic, one_div]
    push_cast
    ring
  simp_rw [hpart]
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun N : ℕ => deriv f (x + N) - Real.log N) atTop (𝓝 0) := by
    have hu := (Real.tendsto_log_comp_add_sub_log x).comp tendsto_natCast_atTop_atTop
    have hl := (Real.tendsto_log_comp_add_sub_log (x - 1)).comp tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      simp only [Function.comp_apply]
      have := hLB N hN
      rw [show (N : ℝ) + (x - 1) = x + N - 1 by ring]
      linarith
    · filter_upwards with N
      simp only [Function.comp_apply]
      have := hUB N
      rw [add_comm (N : ℝ) x]
      linarith
  have := (tendsto_const_nhds (x := deriv f x)).add h1 |>.sub h2
  simpa using this

/-- Summability of `1/(k+1)^2`. -/
theorem L92A_summable_inv_sq : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

/-- The term bound of the digamma series. -/
theorem L92A_norm_digamma_term_le {w : ℂ} {c : ℝ} (hc : 0 < c) (hw : c ≤ w.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (w + k)‖ ≤ ‖w - 1‖ / min c 1 * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hm : 0 < min c 1 := lt_min hc one_pos
  have hwk : min c 1 * ((k : ℝ) + 1) ≤ ‖w + k‖ := by
    calc min c 1 * ((k : ℝ) + 1) ≤ w.re + k := by
          rcases le_total c 1 with h | h
          · rw [min_eq_left h]; nlinarith
          · rw [min_eq_right h]; linarith
      _ = (w + k).re := by simp
      _ ≤ ‖w + k‖ := Complex.re_le_norm _
  have hwk0 : w + k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hk1n : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [show 1 / ((k : ℂ) + 1) - 1 / (w + k) = (w - 1) / ((k + 1) * (w + k)) by
    field_simp; ring, norm_div, norm_mul, hk1n]
  calc ‖w - 1‖ / (((k : ℝ) + 1) * ‖w + k‖)
      ≤ ‖w - 1‖ / (((k : ℝ) + 1) * (min c 1 * ((k : ℝ) + 1))) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hwk (by positivity)
    _ = _ := by field_simp

/-- The digamma series: `ψ(z) + γ = ∑_{k ≥ 0} (1/(k+1) - 1/(z+k))` for `Re z > 0`. -/
theorem L92A_hasSum_digamma {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / (z + k))
      (Complex.digamma z + Real.eulerMascheroniConstant) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsumm (w : ℂ) (hw : 0 < w.re) :
      Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / (w + k)) :=
    Summable.of_norm_bounded (L92A_summable_inv_sq.mul_left _)
      (L92A_norm_digamma_term_le hw le_rfl)
  have hSd : DifferentiableOn ℂ (fun w => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (w + k))) U := by
    intro w₀ hw₀
    have hw₀' : 0 < w₀.re := hw₀
    set V : Set ℂ := {w | w₀.re / 2 < w.re ∧ ‖w‖ < ‖w₀‖ + 1} with hV
    have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
    have hw₀V : w₀ ∈ V := ⟨by linarith, by linarith⟩
    have hd : DifferentiableOn ℂ
        (fun w => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (w + k))) V := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k : ℕ => (‖w₀‖ + 2) / min (w₀.re / 2) 1 * (1 / ((k : ℝ) + 1) ^ 2))
        (L92A_summable_inv_sq.mul_left _) ?_ hVo ?_
      · intro k w hw
        have hwre : 0 < w.re := by linarith [hw.1]
        have hne : w + k ≠ 0 := by
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
        have : DifferentiableAt ℂ (fun w : ℂ => 1 / ((k : ℂ) + 1) - 1 / (w + k)) w := by
          apply DifferentiableAt.sub (differentiableAt_const _)
          exact (differentiableAt_const _).div
            (differentiableAt_id.add (differentiableAt_const _)) hne
        exact this.differentiableWithinAt
      · intro k w hw
        refine (L92A_norm_digamma_term_le (c := w₀.re / 2) (by linarith) hw.1.le k).trans ?_
        gcongr
        calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖w₀‖ + 2 := by rw [norm_one]; linarith [hw.2]
    exact (hd.differentiableAt (hVo.mem_nhds hw₀V)).differentiableWithinAt
  have hΓ : DifferentiableOn ℂ Complex.Gamma U := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w (fun m h => ?_)).differentiableWithinAt
    have := congrArg Complex.re h
    have hw' : 0 < w.re := hw
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hψd : DifferentiableOn ℂ
      (fun w => Complex.digamma w + Real.eulerMascheroniConstant) U := by
    have : DifferentiableOn ℂ Complex.digamma U := by
      have h := (hΓ.deriv hUo).div hΓ (fun w hw => Complex.Gamma_ne_zero_of_re_pos hw)
      refine h.congr (fun w hw => ?_)
      rw [Complex.digamma_def, logDeriv_apply]
      rfl
    exact this.add_const _
  have hreal (x : ℝ) (hx : 0 < x) : Complex.digamma x + Real.eulerMascheroniConstant =
      ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((x : ℂ) + k)) := by
    have h := Complex.hasSum_ofReal.mpr (L92A_real_hasSum_digamma hx)
    have hx' : ∀ m : ℕ, (x : ℝ) ≠ -m := fun m h => by
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hdR := Real.differentiableAt_Gamma hx'
    have hdC : DifferentiableAt ℂ Complex.Gamma x := Complex.differentiableAt_Gamma _ (by
      intro m h
      have := congrArg Complex.re h
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    have hderiv : deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
      have h1 := hdC.hasDerivAt.comp_ofReal
      have h2 := hdR.hasDerivAt.ofReal_comp
      have h3 : (fun y : ℝ => Complex.Gamma (y : ℂ)) = (fun y : ℝ => (Real.Gamma y : ℂ)) := by
        funext y; exact Complex.Gamma_ofReal y
      rw [h3] at h1
      exact h1.unique h2
    have hψ : Complex.digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
      rw [Complex.digamma_def, logDeriv_apply, hderiv, Complex.Gamma_ofReal]
      have : deriv (Real.log ∘ Real.Gamma) x = deriv Real.Gamma x / Real.Gamma x :=
        deriv.log hdR (Real.Gamma_pos_of_pos hx).ne'
      rw [this]
      push_cast
      ring
    rw [hψ, ← Complex.ofReal_add, ← h.tsum_eq]
    congr 1
    funext k
    push_cast
    ring
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), Complex.digamma w + Real.eulerMascheroniConstant =
      ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (w + k)) := by
    have ht : Tendsto (fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
        (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (1 : ℝ)
        have h1 := (Complex.continuous_ofReal.tendsto _).comp h0
        convert h1 using 2 <;> simp
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have h' : ((1 : ℝ) + 1 / ((n : ℝ) + 1)) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    exact ht.frequently (Frequently.of_forall (fun n => hreal _ (by positivity)))
  have heq := (hψd.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    (hSd.analyticOnNhd hUo) (convex_halfSpace_re_gt 0).isPreconnected
    (show (1 : ℂ) ∈ U by simp [U]) hfreq
  have h := heq hz
  simp only at h
  rw [h]
  exact (hsumm z hz).hasSum

/-- `Γℝ'/Γℝ(s) = -log π / 2 + ψ(s/2)/2` for `Re s > 0`. -/
theorem L92A_logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (s / 2) := by
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ (by
    intro m h
    have := congrArg Complex.re h
    simp at this hs2
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  have hΓ0 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun s : ℂ => ((Real.pi : ℝ) : ℂ) ^ (-s / 2))
      (((Real.pi : ℝ) : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := ((Real.pi : ℝ) : ℂ))
      (Or.inl hpi)
    simpa using this
  have h2 : HasDerivAt (fun s : ℂ => Complex.Gamma (s / 2)) (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
    exact hΓ.hasDerivAt.comp s ((hasDerivAt_id s).div_const 2)
  have h := h1.fun_mul h2
  have hfun : Complex.Gammaℝ = fun s : ℂ => ((Real.pi : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hpow : ((Real.pi : ℝ) : ℂ) ^ (-s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  rw [logDeriv_apply, hfun, h.deriv, Complex.digamma_def, logDeriv_apply,
    ← Complex.ofReal_log Real.pi_pos.le]
  field_simp

/-- `Γℂ'/Γℂ(s) = -log (2π) + ψ(s)` for `Re s > 0`. -/
theorem L92A_logDeriv_Gammaℂ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℂ s = -((Real.log (2 * Real.pi) : ℝ) : ℂ) + Complex.digamma s := by
  have hΓ : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma _ (by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  have hΓ0 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have h1 : HasDerivAt (fun s : ℂ => 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-s))
      (2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.log ((2 * Real.pi : ℝ) : ℂ) * (-1))) s := by
    have := ((hasDerivAt_id s).neg).const_cpow (c := ((2 * Real.pi : ℝ) : ℂ)) (Or.inl hpi)
    simpa using this.const_mul 2
  have h := h1.fun_mul hΓ.hasDerivAt
  have hfun : Complex.Gammaℂ = fun s : ℂ => 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := by
    funext s; rw [Complex.Gammaℂ_def]; push_cast; ring
  have hpow : ((2 * Real.pi : ℝ) : ℂ) ^ (-s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  rw [logDeriv_apply, hfun, h.deriv, Complex.digamma_def, logDeriv_apply,
    ← Complex.ofReal_log Real.two_pi_pos.le]
  field_simp

end ArtinPrimitiveRoots
end

section
/-! # L92A: line integrals on `Re s = 2` — the Γ-terms (A1) and the zero sum (A2)

Throughout, `Φ : ℂ → ℂ` is continuous on the line `Re s = 2` with `‖Φ(2+it)‖ ≤ CΦ (1+|t|)^{-4}`,
and for one `x > 0` we are given the Mellin-side evaluations (M2):
`(1/2π) ∫ x^s Φ(s)/(s - w) dt = x^w Φ(w)` for `Re w < 2`, and `∫ x^s Φ(s) dt = 0`. -/

namespace ArtinPrimitiveRoots

open Complex MeasureTheory Filter Topology

theorem L92A_integrable_one_add_abs_rpow_neg_two :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  simpa [Real.norm_eq_abs] using this

theorem L92A_norm_line_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ ((2 : ℂ) + t * I)‖ = x ^ 2 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem L92A_continuous_line {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) := by
  refine Continuous.mul ?_ hΦc
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  exact_mod_cast hx.ne'

/-- The line integrand against a measurable factor of growth `≤ K (1+|t|)^2` is integrable. -/
theorem L92A_integrable_line_mul {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) {CΦ : ℝ}
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ))
    {h : ℝ → ℂ} (hh : AEStronglyMeasurable h volume) {K : ℝ}
    (hK : ∀ t : ℝ, ‖h t‖ ≤ K * (1 + |t|) ^ 2) :
    Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) * h t) := by
  refine Integrable.mono' (L92A_integrable_one_add_abs_rpow_neg_two.const_mul (x ^ 2 * CΦ * K))
    ((L92A_continuous_line hx hΦc).aestronglyMeasurable.mul hh)
    (Eventually.of_forall fun t => ?_)
  have h1 : 0 < 1 + |t| := by positivity
  rw [norm_mul, norm_mul, L92A_norm_line_cpow hx]
  have e : (1 + |t|) ^ (-2 : ℝ) = (1 + |t|) ^ (-4 : ℝ) * (1 + |t|) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add h1]
    norm_num
  rw [e]
  have hb := hΦd t
  have hCΦ : 0 ≤ CΦ * (1 + |t|) ^ (-4 : ℝ) := (norm_nonneg _).trans hb
  calc x ^ 2 * ‖Φ (2 + t * I)‖ * ‖h t‖
      ≤ x ^ 2 * (CΦ * (1 + |t|) ^ (-4 : ℝ)) * (K * (1 + |t|) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) (hK t) (norm_nonneg _)
          (mul_nonneg (by positivity) hCΦ)
    _ = _ := by ring

theorem L92A_integrable_line {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) {CΦ : ℝ}
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ)) :
    Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I)) := by
  have := L92A_integrable_line_mul hx hΦc hΦd (h := fun _ => 1) aestronglyMeasurable_const
    (K := 1) (fun t => by
      have : (1 : ℝ) ≤ (1 + |t|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg t])
      simpa using this)
  simpa using this

/-- `‖s - w‖ ≥ 1` on the line when `Re w ≤ 1`, so `1/(s - w)` is a bounded factor. -/
theorem L92A_integrable_line_div {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) {CΦ : ℝ}
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ)) {w : ℂ} (hw : w.re ≤ 1) :
    Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) / (2 + t * I - w)) := by
  have hne : ∀ t : ℝ, (2 + t * I - w) ≠ 0 := fun t h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have := L92A_integrable_line_mul hx hΦc hΦd (h := fun t => (2 + t * I - w)⁻¹)
    (Continuous.aestronglyMeasurable (by
      exact Continuous.inv₀ (by fun_prop) hne)) (K := 1) (fun t => by
      have h1 : 1 ≤ ‖(2 : ℂ) + t * I - w‖ := by
        calc (1 : ℝ) ≤ (2 + t * I - w).re := by simp; linarith
          _ ≤ _ := Complex.re_le_norm _
      rw [norm_inv]
      calc ‖(2 : ℂ) + t * I - w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
        _ ≤ 1 * (1 + |t|) ^ 2 := by
          rw [one_mul]; exact one_le_pow₀ (by linarith [abs_nonneg t]))
  simpa [div_eq_mul_inv] using this

/-! ### The digamma function on the line -/

theorem L92A_differentiableOn_digamma : DifferentiableOn ℂ Complex.digamma {w : ℂ | 0 < w.re} := by
  have hUo : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓ : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w (fun m h => ?_)).differentiableWithinAt
    have := congrArg Complex.re h
    have hw' : 0 < w.re := hw
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h := (hΓ.deriv hUo).div hΓ (fun w hw => Complex.Gamma_ne_zero_of_re_pos hw)
  refine h.congr (fun w hw => ?_)
  rw [Complex.digamma_def, logDeriv_apply]
  rfl

theorem L92A_norm_digamma_le {z : ℂ} (hz : 1 ≤ z.re) :
    ‖Complex.digamma z‖ ≤
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z - 1‖ * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
  have hS := L92A_hasSum_digamma (by linarith : 0 < z.re)
  have h1 : Complex.digamma z =
      (Complex.digamma z + Real.eulerMascheroniConstant) - Real.eulerMascheroniConstant := by ring
  rw [h1, ← hS.tsum_eq]
  have hb : ‖∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (z + k))‖ ≤
      ‖z - 1‖ * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
    refine tsum_of_norm_bounded (L92A_summable_inv_sq.hasSum.mul_left ‖z - 1‖) (fun k => ?_)
    simpa using L92A_norm_digamma_term_le one_pos hz k
  have := norm_sub_le (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (z + k)))
    (Real.eulerMascheroniConstant : ℂ)
  linarith

/-- The line integral of `x^s Φ(s) ψ(s/m)` (`m = 1, 2`): term-by-term integration of the digamma
series, each pole term evaluated by (M2). -/
theorem L92A_digamma_line (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) {x : ℝ} (hx : 0 < x)
    {Φ : ℂ → ℂ} (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) {CΦ : ℝ}
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ))
    (hM2 : ∀ w : ℂ, w.re < 2 → (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) / (2 + t * I - w) = (x : ℂ) ^ w * Φ w)
    (hM2' : ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) = 0) :
    Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        Complex.digamma ((2 + t * I) / m)) ∧
      Summable (fun k : ℕ => (x : ℂ) ^ (-((m * k : ℕ) : ℂ)) * Φ (-((m * k : ℕ) : ℂ))) ∧
      (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        Complex.digamma ((2 + t * I) / m) =
        -(m : ℂ) * ∑' k : ℕ, (x : ℂ) ^ (-((m * k : ℕ) : ℂ)) * Φ (-((m * k : ℕ) : ℂ)) := by
  set g : ℝ → ℂ := fun t => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) with hg
  set z : ℝ → ℂ := fun t => (2 + t * I) / (m : ℂ) with hz
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hzre (t : ℝ) : (z t).re = 2 / m := by
    simp only [hz, Complex.div_natCast_re]
    simp
  have hzre1 (t : ℝ) : 1 ≤ (z t).re := by
    rw [hzre, le_div_iff₀ hm0]
    have : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
    linarith
  have hz1 (t : ℝ) : ‖z t - 1‖ ≤ 3 * (1 + |t|) := by
    have h2 : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h3 : ‖z t‖ ≤ 2 + |t| := by
      simp only [hz, norm_div, Complex.norm_natCast]
      rw [div_le_iff₀ hm0]
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      nlinarith [abs_nonneg t]
    calc ‖z t - 1‖ ≤ ‖z t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * (1 + |t|) := by rw [norm_one]; linarith [abs_nonneg t]
  have hzc : Continuous z := by
    simp only [hz]
    fun_prop
  set term : ℕ → ℝ → ℂ := fun k t => 1 / ((k : ℂ) + 1) - 1 / (z t + k) with hterm
  have hterm_le (k : ℕ) (t : ℝ) :
      ‖term k t‖ ≤ 3 * (1 + |t|) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have := L92A_norm_digamma_term_le one_pos (hzre1 t) k
    simp only [min_self, div_one] at this
    refine this.trans ?_
    gcongr
    exact hz1 t
  have hzk (k : ℕ) (t : ℝ) : z t + k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    linarith [hzre1 t, (k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hterm_c (k : ℕ) : Continuous (term k) := by
    simp only [hterm]
    exact continuous_const.sub (continuous_const.div (hzc.add continuous_const) (hzk k))
  set F : ℕ → ℝ → ℂ := fun k t => g t * term k t with hF
  have hFint (k : ℕ) : Integrable (F k) := by
    refine L92A_integrable_line_mul hx hΦc hΦd (hterm_c k).aestronglyMeasurable
      (K := 3 * (1 / ((k : ℝ) + 1) ^ 2)) (fun t => (hterm_le k t).trans ?_)
    have h1 : 1 + |t| ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
    have : 0 ≤ 1 / ((k : ℝ) + 1) ^ 2 := by positivity
    nlinarith
  -- the dominating integral
  have hG : Integrable (fun t : ℝ => g t * ((3 * (1 + |t|) : ℝ) : ℂ)) := by
    refine L92A_integrable_line_mul hx hΦc hΦd (by fun_prop) (K := 3) (fun t => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : 1 + |t| ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
    linarith
  have hFsum : Summable (fun k : ℕ => ∫ t, ‖F k t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => ?_) (L92A_summable_inv_sq.mul_left (∫ t, ‖g t * ((3 * (1 + |t|) : ℝ) : ℂ)‖))
    rw [mul_comm, ← integral_const_mul]
    refine integral_mono (hFint k).norm (hG.norm.const_mul _) (fun t => ?_)
    show ‖g t * term k t‖ ≤ 1 / ((k : ℝ) + 1) ^ 2 * ‖g t * ((3 * (1 + |t|) : ℝ) : ℂ)‖
    rw [norm_mul (g t) (term k t), norm_mul (g t), Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * (1 + |t|))]
    have := hterm_le k t
    have h0 : 0 ≤ ‖g t‖ := norm_nonneg _
    calc ‖g t‖ * ‖term k t‖ ≤ ‖g t‖ * (3 * (1 + |t|) * (1 / ((k : ℝ) + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  -- each term integral
  have hFk (k : ℕ) : ∫ t, F k t = -(2 * (Real.pi : ℂ) * m) *
      ((x : ℂ) ^ (-((m * k : ℕ) : ℂ)) * Φ (-((m * k : ℕ) : ℂ))) := by
    set w : ℂ := -((m * k : ℕ) : ℂ) with hw
    have hwre : w.re ≤ 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) * k := by positivity
      simp [hw]
      linarith
    have hpt : ∀ t : ℝ, F k t = (1 / ((k : ℂ) + 1)) * g t -
        (m : ℂ) * (g t / (2 + t * I - w)) := by
      intro t
      have hne : (2 + t * I - w) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hw] at this
        linarith [(by positivity : (0 : ℝ) ≤ (m : ℝ) * k)]
      have e : z t + k = (2 + t * I - w) / m := by
        simp only [hz, hw]
        push_cast
        field_simp
        ring
      simp only [hF, hterm, e]
      field_simp
    rw [integral_congr_ae (Eventually.of_forall hpt)]
    rw [integral_sub ((L92A_integrable_line hx hΦc hΦd).const_mul _)
      ((L92A_integrable_line_div hx hΦc hΦd hwre).const_mul _), integral_const_mul,
      integral_const_mul]
    have h2 := hM2 w (by linarith)
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h3 : ∫ t : ℝ, g t / (2 + t * I - w) = 2 * (Real.pi : ℂ) * ((x : ℂ) ^ w * Φ w) := by
      rw [← h2, ← mul_assoc, mul_one_div_cancel (mul_ne_zero two_ne_zero hpi), one_mul]
    simp only [hg] at h3 ⊢
    rw [hM2', h3]
    ring
  -- pointwise identity for the tsum
  have hpt : ∀ t : ℝ, ∑' k, F k t =
      g t * Complex.digamma (z t) + Real.eulerMascheroniConstant * g t := by
    intro t
    have hS := L92A_hasSum_digamma (by linarith [hzre1 t] : 0 < (z t).re)
    simp only [hF, hterm]
    rw [tsum_mul_left, hS.tsum_eq]
    ring
  have hHS := hasSum_integral_of_summable_integral_norm hFint hFsum
  rw [integral_congr_ae (Eventually.of_forall hpt)] at hHS
  have hint1 : Integrable (fun t : ℝ => g t * Complex.digamma (z t)) := by
    have hψc : Continuous (fun t => Complex.digamma (z t)) := by
      refine L92A_differentiableOn_digamma.continuousOn.comp_continuous hzc (fun t => ?_)
      show 0 < (z t).re
      linarith [hzre1 t]
    refine L92A_integrable_line_mul hx hΦc hΦd hψc.aestronglyMeasurable
      (K := ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)
      (fun t => ?_)
    have h1 := L92A_norm_digamma_le (hzre1 t)
    have hS2 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := tsum_nonneg (fun k => by positivity)
    have h2 : 1 ≤ (1 + |t|) := by linarith [abs_nonneg t]
    have h3 : 1 + |t| ≤ (1 + |t|) ^ 2 := by nlinarith
    have h4 := hz1 t
    have h5 : ‖z t - 1‖ * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 ≤
        3 * (1 + |t|) * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_right h4 hS2
    have h6 : 0 ≤ ‖(Real.eulerMascheroniConstant : ℂ)‖ := norm_nonneg _
    nlinarith
  rw [integral_add hint1 ((L92A_integrable_line hx hΦc hΦd).const_mul _), integral_const_mul,
    hM2', mul_zero, add_zero] at hHS
  have hpi : (2 * (Real.pi : ℂ) * m) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) hmC
  simp only [hFk] at hHS
  have hsum : Summable (fun k : ℕ => (x : ℂ) ^ (-((m * k : ℕ) : ℂ)) * Φ (-((m * k : ℕ) : ℂ))) :=
    (summable_mul_left_iff (neg_ne_zero.mpr hpi)).mp hHS.summable
  refine ⟨hint1, hsum, ?_⟩
  rw [← hHS.tsum_eq, tsum_mul_left]
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The pole sum `∑_k x^{-mk} Φ(-mk)` is bounded by `2c` once `x a ≥ 2`. -/
theorem L92A_norm_neg_sum_le (m : ℕ) (hm1 : 1 ≤ m) {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    {a c : ℝ} (ha : 0 < a) (hxa : 2 / a ≤ x) (hneg : ∀ k : ℕ, ‖Φ (-(k : ℂ))‖ ≤ c * (1 / a) ^ k) :
    ‖∑' k : ℕ, (x : ℂ) ^ (-((m * k : ℕ) : ℂ)) * Φ (-((m * k : ℕ) : ℂ))‖ ≤ 2 * c := by
  have hc : 0 ≤ c := by
    have := (norm_nonneg _).trans (hneg 0)
    simpa using this
  have hxa' : 2 ≤ x * a := by rwa [div_le_iff₀ ha] at hxa
  have hq : 1 / x * (1 / a) ≤ 1 / 2 := by
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) two_pos]
    linarith
  rw [show 2 * c = c * 2 by ring]
  refine tsum_of_norm_bounded (hasSum_geometric_two.mul_left c) (fun k => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-((m * k : ℕ) : ℂ)).re = -((m * k : ℕ) : ℝ) := by simp
  rw [hre, Real.rpow_neg hx.le, Real.rpow_natCast, ← one_div, ← one_div_pow]
  have h1 := hneg (m * k)
  calc (1 / x) ^ (m * k) * ‖Φ (-((m * k : ℕ) : ℂ))‖ ≤ (1 / x) ^ (m * k) * (c * (1 / a) ^ (m * k)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c * (1 / x * (1 / a)) ^ (m * k) := by rw [mul_pow]; ring
    _ ≤ c * (1 / 2) ^ (m * k) := by
        gcongr
    _ ≤ c * (1 / 2) ^ k := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_) hc
        exact Nat.le_mul_of_pos_left k hm1

/-- **A1.** The `Γℝ` and `Γℂ` line integrals are bounded by `2c` for `x ≥ 2/a`. -/
theorem L92A_gamma_lines {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) {CΦ : ℝ}
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ))
    (hM2 : ∀ w : ℂ, w.re < 2 → (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) / (2 + t * I - w) = (x : ℂ) ^ w * Φ w)
    (hM2' : ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) = 0)
    {a c : ℝ} (ha : 0 < a) (hxa : 2 / a ≤ x) (hneg : ∀ k : ℕ, ‖Φ (-(k : ℂ))‖ ≤ c * (1 / a) ^ k) :
    (Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        logDeriv Complex.Gammaℝ (2 + t * I)) ∧
      ‖(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        logDeriv Complex.Gammaℝ (2 + t * I)‖ ≤ 2 * c) ∧
    (Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        logDeriv Complex.Gammaℂ (2 + t * I)) ∧
      ‖(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        logDeriv Complex.Gammaℂ (2 + t * I)‖ ≤ 2 * c) := by
  have hre (t : ℝ) : 0 < ((2 : ℂ) + t * I).re := by simp
  have hI := L92A_integrable_line hx hΦc hΦd
  obtain ⟨hi2, -, he2⟩ := L92A_digamma_line 2 (by norm_num) le_rfl hx hΦc hΦd hM2 hM2'
  obtain ⟨hi1, -, he1⟩ := L92A_digamma_line 1 le_rfl (by norm_num) hx hΦc hΦd hM2 hM2'
  simp only [Nat.cast_ofNat, Nat.cast_one, div_one] at hi2 he2 hi1 he1
  have hb2 := L92A_norm_neg_sum_le 2 (by norm_num) hx ha hxa hneg
  have hb1 := L92A_norm_neg_sum_le 1 le_rfl hx ha hxa hneg
  simp only [one_mul] at hb1
  simp only [one_mul] at he1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := (hI.const_mul (-((Real.log Real.pi : ℝ) : ℂ) / 2)).add (hi2.const_mul (1 / 2))
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, L92A_logDeriv_Gammaℝ (hre t)]
    ring
  · have hpt : ∀ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        logDeriv Complex.Gammaℝ (2 + t * I) =
        (-((Real.log Real.pi : ℝ) : ℂ) / 2) * ((x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I)) +
        (1 / 2) * ((x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
          Complex.digamma ((2 + t * I) / 2)) := by
      intro t
      rw [L92A_logDeriv_Gammaℝ (hre t)]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (hI.const_mul _)
      (hi2.const_mul _), integral_const_mul, integral_const_mul, hM2', mul_zero, zero_add,
      mul_left_comm, he2]
    calc ‖1 / 2 * (-((2 : ℕ) : ℂ) * ∑' k : ℕ, (x : ℂ) ^ (-((2 * k : ℕ) : ℂ)) *
          Φ (-((2 * k : ℕ) : ℂ)))‖
        = ‖∑' k : ℕ, (x : ℂ) ^ (-((2 * k : ℕ) : ℂ)) * Φ (-((2 * k : ℕ) : ℂ))‖ := by
          rw [← mul_assoc]
          norm_num
      _ ≤ 2 * c := hb2
  · have := (hI.const_mul (-((Real.log (2 * Real.pi) : ℝ) : ℂ))).add hi1
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, L92A_logDeriv_Gammaℂ (hre t)]
    ring
  · have hpt : ∀ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        logDeriv Complex.Gammaℂ (2 + t * I) =
        (-((Real.log (2 * Real.pi) : ℝ) : ℂ)) * ((x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I)) +
        (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) * Complex.digamma (2 + t * I) := by
      intro t
      rw [L92A_logDeriv_Gammaℂ (hre t)]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (hI.const_mul _) hi1,
      integral_const_mul, hM2', mul_zero, zero_add, he1, neg_one_mul, norm_neg]
    exact hb1

/-! ### A2: the zero sum -/

/-- `‖1/(s-ρ) + 1/ρ‖ ≤ 2‖s‖²/|ρ|²` for `Re s = 2`, `0 < Re ρ ≤ 1`. -/
theorem L92A_norm_hadamard_term_le {s ρ : ℂ} (hs : s.re = 2) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) :
    ‖(s - ρ)⁻¹ + ρ⁻¹‖ ≤ 2 * ‖s‖ ^ 2 * (Complex.normSq ρ)⁻¹ := by
  have hρ : ρ ≠ 0 := fun h => by simp [h] at hρ0
  have h2 : 1 ≤ ‖s - ρ‖ := by
    calc (1 : ℝ) ≤ (s - ρ).re := by simp; linarith
      _ ≤ _ := Complex.re_le_norm _
  have hsρ : s - ρ ≠ 0 := fun h => by rw [h, norm_zero] at h2; linarith
  have h1 : 1 ≤ ‖s‖ := by
    calc (1 : ℝ) ≤ s.re := by linarith
      _ ≤ _ := Complex.re_le_norm _
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have h3 : ‖ρ‖ ≤ ‖s‖ + ‖s - ρ‖ := by
    calc ‖ρ‖ = ‖s - (s - ρ)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have h4 : ‖s‖ + ‖s - ρ‖ ≤ 2 * ‖s‖ * ‖s - ρ‖ := by nlinarith
  have e : (s - ρ)⁻¹ + ρ⁻¹ = s / ((s - ρ) * ρ) := by field_simp; ring
  rw [e, norm_div, norm_mul, Complex.normSq_eq_norm_sq, div_le_iff₀ (by positivity)]
  have h5 : ‖s‖ * ‖ρ‖ * ‖ρ‖ ≤ ‖s‖ * ‖ρ‖ * (2 * ‖s‖ * ‖s - ρ‖) :=
    mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
  have e2 : 2 * ‖s‖ ^ 2 * (‖ρ‖ ^ 2)⁻¹ * (‖s - ρ‖ * ‖ρ‖) =
      ‖s‖ * ‖ρ‖ * (2 * ‖s‖ * ‖s - ρ‖) / ‖ρ‖ ^ 2 := by
    field_simp
  rw [e2, le_div_iff₀ (by positivity)]
  nlinarith

/-- **A2.** Term-by-term integration of the Hadamard sum against `x^s Φ(s)` on `Re s = 2`. -/
theorem L92A_zero_line {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) {CΦ : ℝ}
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ))
    (hM2 : ∀ w : ℂ, w.re < 2 → (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) / (2 + t * I - w) = (x : ℂ) ^ w * Φ w)
    (hM2' : ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) = 0)
    (ρ : ℕ → ℂ) (hρ : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hρs : Summable (fun j => (Complex.normSq (ρ j))⁻¹)) :
    Integrable (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        ∑' j, ((2 + t * I - ρ j)⁻¹ + (ρ j)⁻¹)) ∧
      (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) *
        ∑' j, ((2 + t * I - ρ j)⁻¹ + (ρ j)⁻¹) = ∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j) := by
  set g : ℝ → ℂ := fun t => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) with hg
  set h : ℕ → ℝ → ℂ := fun j t => (2 + t * I - ρ j)⁻¹ + (ρ j)⁻¹ with hh
  have hs2 (t : ℝ) : ‖(2 : ℂ) + t * I‖ ^ 2 ≤ 4 * (1 + |t|) ^ 2 := by
    have : ‖(2 : ℂ) + t * I‖ ≤ 2 * (1 + |t|) := by
      refine (norm_add_le _ _).trans ?_
      simp
      linarith [abs_nonneg t]
    nlinarith [norm_nonneg ((2 : ℂ) + t * I)]
  have hhle (j : ℕ) (t : ℝ) : ‖h j t‖ ≤ 8 * (1 + |t|) ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
    refine (L92A_norm_hadamard_term_le (by simp) (hρ j).1 (hρ j).2.le).trans ?_
    have : 0 ≤ (Complex.normSq (ρ j))⁻¹ := inv_nonneg.mpr (Complex.normSq_nonneg _)
    nlinarith [hs2 t]
  have hne (j : ℕ) (t : ℝ) : (2 + t * I - ρ j) ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith [(hρ j).2]
  have hhc (j : ℕ) : Continuous (h j) := by
    simp only [hh]
    exact (Continuous.inv₀ (by fun_prop) (hne j)).add continuous_const
  have hsumt (t : ℝ) : Summable (fun j => h j t) :=
    Summable.of_norm_bounded (hρs.mul_left (8 * (1 + |t|) ^ 2)) (hhle · t)
  have hSle (t : ℝ) : ‖∑' j, h j t‖ ≤ 8 * (∑' j, (Complex.normSq (ρ j))⁻¹) * (1 + |t|) ^ 2 := by
    have := tsum_of_norm_bounded (hρs.hasSum.mul_left (8 * (1 + |t|) ^ 2)) (hhle · t)
    linarith
  have hSm : AEStronglyMeasurable (fun t => ∑' j, h j t) volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => ∑ j ∈ Finset.range n, h j t) (fun n => ?_)
      (Eventually.of_forall fun t => (hsumt t).hasSum.tendsto_sum_nat)
    exact (continuous_finsetSum _ (fun j _ => hhc j)).aestronglyMeasurable
  have hint : Integrable (fun t => g t * ∑' j, h j t) :=
    L92A_integrable_line_mul hx hΦc hΦd hSm hSle
  set F : ℕ → ℝ → ℂ := fun j t => g t * h j t with hF
  have hFint (j : ℕ) : Integrable (F j) :=
    L92A_integrable_line_mul hx hΦc hΦd (hhc j).aestronglyMeasurable
      (K := 8 * (Complex.normSq (ρ j))⁻¹) (fun t => (hhle j t).trans (le_of_eq (by ring)))
  have hG : Integrable (fun t : ℝ => g t * ((8 * (1 + |t|) ^ 2 : ℝ) : ℂ)) := by
    refine L92A_integrable_line_mul hx hΦc hΦd (by fun_prop) (K := 8) (fun t => ?_)
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hFsum : Summable (fun j : ℕ => ∫ t, ‖F j t‖) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg (fun t => norm_nonneg _))
      (fun j => ?_) (hρs.mul_left (∫ t, ‖g t * ((8 * (1 + |t|) ^ 2 : ℝ) : ℂ)‖))
    rw [mul_comm, ← integral_const_mul]
    refine integral_mono (hFint j).norm (hG.norm.const_mul _) (fun t => ?_)
    show ‖g t * h j t‖ ≤ (Complex.normSq (ρ j))⁻¹ * ‖g t * ((8 * (1 + |t|) ^ 2 : ℝ) : ℂ)‖
    rw [norm_mul (g t) (h j t), norm_mul (g t), Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * (1 + |t|) ^ 2)]
    have := mul_le_mul_of_nonneg_left (hhle j t) (norm_nonneg (g t))
    linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hFk (j : ℕ) : ∫ t, F j t = 2 * (Real.pi : ℂ) * ((x : ℂ) ^ (ρ j) * Φ (ρ j)) := by
    have hpt : ∀ t : ℝ, F j t = g t / (2 + t * I - ρ j) + (ρ j)⁻¹ * g t := by
      intro t
      simp only [hF, hh]
      rw [div_eq_mul_inv]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add
      (L92A_integrable_line_div hx hΦc hΦd (hρ j).2.le)
      ((L92A_integrable_line hx hΦc hΦd).const_mul _), integral_const_mul]
    have h2 := hM2 (ρ j) (by linarith [(hρ j).2])
    have h3 : ∫ t : ℝ, g t / (2 + t * I - ρ j) =
        2 * (Real.pi : ℂ) * ((x : ℂ) ^ (ρ j) * Φ (ρ j)) := by
      rw [← h2, ← mul_assoc, mul_one_div_cancel (mul_ne_zero two_ne_zero hpi), one_mul]
    rw [h3, hM2', mul_zero, add_zero]
  have hHS := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hpt2 : ∀ t : ℝ, ∑' j, F j t = g t * ∑' j, h j t := fun t => by
    simp only [hF]
    rw [tsum_mul_left]
  rw [integral_congr_ae (Eventually.of_forall hpt2)] at hHS
  simp only [hFk] at hHS
  refine ⟨hint, ?_⟩
  rw [← hHS.tsum_eq, tsum_mul_left, ← mul_assoc, one_div_mul_cancel (mul_ne_zero two_ne_zero hpi),
    one_mul]

end ArtinPrimitiveRoots
end

section
/-! # L92A: the line bound for `-ζ_K'/ζ_K` and the zero-sum bound (field-free) -/

namespace ArtinPrimitiveRoots

open Complex MeasureTheory Filter Topology

/-- The line integral of `L(s) x^s Φ(s)` where `L` is given on `Re s > 1` by the explicit formula
(Z3), bounded termwise: zeros by A2, poles by (M2), Γ-terms by A1. -/
theorem L92A_theta_line_bound {x : ℝ} (hx : 0 < x) {Φ : ℂ → ℂ}
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) {CΦ : ℝ}
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ))
    (hM2 : ∀ w : ℂ, w.re < 2 → (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) / (2 + t * I - w) = (x : ℂ) ^ w * Φ w)
    (hM2' : ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) = 0)
    {a c : ℝ} (ha : 0 < a) (hxa : 2 / a ≤ x) (hneg : ∀ k : ℕ, ‖Φ (-(k : ℂ))‖ ≤ c * (1 / a) ^ k)
    (B : ℂ) (ρ : ℕ → ℂ) (hρ : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hρs : Summable (fun j => (Complex.normSq (ρ j))⁻¹)) (D : ℝ) (r₁ r₂ : ℕ)
    (L : ℂ → ℂ) (hL : ∀ s : ℂ, 1 < s.re → L s =
      -B - ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹) + 1 / s + 1 / (s - 1)
        + (1 / 2 : ℂ) * (D : ℂ)
        + (r₁ : ℂ) * logDeriv Complex.Gammaℝ s
        + (r₂ : ℂ) * logDeriv Complex.Gammaℂ s) :
    ‖(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, L (2 + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I) *
        Φ (2 + t * I)‖ ≤
      ‖∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j)‖ + ‖Φ 0‖ + x * ‖Φ 1‖ + ((r₁ : ℝ) + r₂) * (2 * c) := by
  set g : ℝ → ℂ := fun t => (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) with hg
  set S : ℝ → ℂ := fun t => ∑' j, ((2 + t * I - ρ j)⁻¹ + (ρ j)⁻¹) with hS
  have hI : Integrable g := L92A_integrable_line hx hΦc hΦd
  have hM2'' : ∫ t, g t = 0 := hM2'
  obtain ⟨⟨hiR', hbR'⟩, ⟨hiC', hbC'⟩⟩ := L92A_gamma_lines hx hΦc hΦd hM2 hM2' ha hxa hneg
  obtain ⟨hiZ', heZ'⟩ := L92A_zero_line hx hΦc hΦd hM2 hM2' ρ hρ hρs
  have hiR : Integrable (fun t => g t * logDeriv Complex.Gammaℝ (2 + t * I)) := hiR'
  have hiC : Integrable (fun t => g t * logDeriv Complex.Gammaℂ (2 + t * I)) := hiC'
  have hiZ : Integrable (fun t => g t * S t) := hiZ'
  set GR := (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, g t * logDeriv Complex.Gammaℝ (2 + t * I)
    with hGR
  set GC := (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, g t * logDeriv Complex.Gammaℂ (2 + t * I)
    with hGC
  have hbR : ‖GR‖ ≤ 2 * c := hbR'
  have hbC : ‖GC‖ ≤ 2 * c := hbC'
  have heZ : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, g t * S t = ∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j) :=
    heZ'
  have hi0 : Integrable (fun t => g t / (2 + t * I - 0)) :=
    L92A_integrable_line_div hx hΦc hΦd (w := 0) (by simp)
  have hi1 : Integrable (fun t => g t / (2 + t * I - 1)) :=
    L92A_integrable_line_div hx hΦc hΦd (w := 1) (by simp)
  have e0 : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, g t / (2 + t * I - 0) = Φ 0 := by
    have := hM2 0 (by simp)
    rw [Complex.cpow_zero, one_mul] at this
    exact this
  have e1 : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, g t / (2 + t * I - 1) = (x : ℂ) * Φ 1 := by
    have := hM2 1 (by simp)
    rw [Complex.cpow_one] at this
    exact this
  set c0 : ℂ := -B + (1 / 2 : ℂ) * (D : ℂ) with hc0
  have hpt : ∀ t : ℝ, L (2 + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) =
      c0 * g t - g t * S t + g t / (2 + t * I - 0) + g t / (2 + t * I - 1)
        + (r₁ : ℂ) * (g t * logDeriv Complex.Gammaℝ (2 + t * I))
        + (r₂ : ℂ) * (g t * logDeriv Complex.Gammaℂ (2 + t * I)) := by
    intro t
    rw [hL _ (by simp)]
    simp only [hg, hS, hc0]
    ring
  have j0 : Integrable (fun t => c0 * g t) := hI.const_mul c0
  have j01 : Integrable (fun t => c0 * g t - g t * S t) := j0.sub hiZ
  have j012 : Integrable (fun t => c0 * g t - g t * S t + g t / (2 + t * I - 0)) := j01.add hi0
  have j0123 : Integrable (fun t => c0 * g t - g t * S t + g t / (2 + t * I - 0) +
      g t / (2 + t * I - 1)) := j012.add hi1
  have j4 : Integrable (fun t => (r₁ : ℂ) * (g t * logDeriv Complex.Gammaℝ (2 + t * I))) :=
    hiR.const_mul _
  have j5 : Integrable (fun t => (r₂ : ℂ) * (g t * logDeriv Complex.Gammaℂ (2 + t * I))) :=
    hiC.const_mul _
  have j01234 : Integrable (fun t => c0 * g t - g t * S t + g t / (2 + t * I - 0) +
      g t / (2 + t * I - 1) + (r₁ : ℂ) * (g t * logDeriv Complex.Gammaℝ (2 + t * I))) :=
    j0123.add j4
  have hval : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, L (2 + t * I) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) =
      -(∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j)) + Φ 0 + (x : ℂ) * Φ 1 + (r₁ : ℂ) * GR +
        (r₂ : ℂ) * GC := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add j01234 j5,
      integral_add j0123 j4, integral_add j012 hi1, integral_add j01 hi0, integral_sub j0 hiZ,
      integral_const_mul, integral_const_mul, integral_const_mul, hM2'', ← heZ, ← e0, ← e1,
      hGR, hGC]
    ring
  rw [hval]
  have hn1 : ‖(r₁ : ℂ) * GR‖ ≤ (r₁ : ℝ) * (2 * c) := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg _)
  have hn2 : ‖(r₂ : ℂ) * GC‖ ≤ (r₂ : ℝ) * (2 * c) := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbC (Nat.cast_nonneg _)
  have hn3 : ‖(x : ℂ) * Φ 1‖ = x * ‖Φ 1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]
  have t1 := norm_add_le (-(∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j)) + Φ 0 + (x : ℂ) * Φ 1 +
    (r₁ : ℂ) * GR) ((r₂ : ℂ) * GC)
  have t2 := norm_add_le (-(∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j)) + Φ 0 + (x : ℂ) * Φ 1)
    ((r₁ : ℂ) * GR)
  have t3 := norm_add_le (-(∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j)) + Φ 0) ((x : ℂ) * Φ 1)
  have t4 := norm_add_le (-(∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j))) (Φ 0)
  rw [norm_neg] at t4
  linarith

/-- `1/(4 + γ²) ≤ Re 1/(2 - ρ)` for `0 < Re ρ < 1`. -/
theorem L92A_inv_four_add_sq_le_re {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    1 / (4 + ρ.im ^ 2) ≤ (1 / (2 - ρ)).re := by
  rw [one_div (2 - ρ), Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat]
  set u := 2 - ρ.re with hu
  have hu1 : 1 < u := by linarith
  have hu2 : u < 2 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [sq_nonneg ρ.im]

/-- The zero sum: `‖Σ_j x^{ρ_j} Φ(ρ_j)‖ ≤ C₃ x^σ Σ_j Re 1/(2 - ρ_j)` when `Re ρ_j ≤ σ`. -/
theorem L92A_zero_sum_le {x : ℝ} (hx : 1 ≤ x) {Φ : ℂ → ℂ} {C₃ : ℝ}
    (hΦs : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Φ w‖ ≤ C₃ / (4 + w.im ^ 2))
    (ρ : ℕ → ℂ) (hρ : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) (σ : ℝ) (hσ : ∀ j, (ρ j).re ≤ σ)
    (hS : Summable (fun j => (1 / (2 - ρ j)).re)) :
    ‖∑' j, (x : ℂ) ^ (ρ j) * Φ (ρ j)‖ ≤ C₃ * x ^ σ * ∑' j, (1 / (2 - ρ j)).re := by
  have hC₃ : 0 ≤ C₃ := by
    have := (norm_nonneg _).trans (hΦs 0 le_rfl zero_le_one)
    simp at this
    linarith
  have hx0 : 0 < x := by linarith
  refine tsum_of_norm_bounded (hS.hasSum.mul_left (C₃ * x ^ σ)) (fun j => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have h1 : x ^ (ρ j).re ≤ x ^ σ := Real.rpow_le_rpow_of_exponent_le hx (hσ j)
  have h2 := hΦs (ρ j) (hρ j).1.le (hρ j).2.le
  have h3 := L92A_inv_four_add_sq_le_re (hρ j).1 (hρ j).2
  have h4 : ‖Φ (ρ j)‖ ≤ C₃ * (1 / (2 - ρ j)).re := by
    refine h2.trans ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h3 hC₃
  calc x ^ (ρ j).re * ‖Φ (ρ j)‖ ≤ x ^ σ * (C₃ * (1 / (2 - ρ j)).re) :=
        mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ArtinPrimitiveRoots
end

section
/-! # L92A: assembly of Lemma 9.2 from the Mellin-side facts (as hypotheses) and Z1–Z3 -/

namespace ArtinPrimitiveRoots

open Complex MeasureTheory NumberField

/-- The zero data of `ζ_K` (package 7f1aa5b8, Hadamard 31f2c017, Z1–Z3). -/
theorem L92A_zero_data (K : Type) [Field K] [NumberField K] (σ : ℝ)
    (hZ : DedekindZeroFreeRight K σ) :
    ∃ (B : ℂ) (ρ : ℕ → ℂ), (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧ (∀ j, (ρ j).re ≤ σ) ∧
      Summable (fun j => (1 / (2 - ρ j)).re) ∧
      ∑' j, (1 / (2 - ρ j)).re ≤ Real.log |(discr K : ℝ)| + 3 ∧
      ∀ s : ℂ, 1 < s.re → -logDeriv (NumberField.dedekindZeta K) s =
        -B - ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹) + 1 / s + 1 / (s - 1)
          + (1 / 2 : ℂ) * (Real.log |(discr K : ℝ)| : ℂ)
          + (InfinitePlace.nrRealPlaces K : ℂ) * logDeriv Complex.Gammaℝ s
          + (InfinitePlace.nrComplexPlaces K : ℂ) * logDeriv Complex.Gammaℂ s := by
  obtain ⟨Λ, hΛdiff, hΛFE, hΛeq, hB1, hEnd, hSL⟩ :=
    NumberField.exists_completedDedekindZeta_package K
  obtain ⟨B, ρ, hρ, hρsum, hexp⟩ :=
    NumberField.exists_hadamard_logDeriv_expansion_of_completedZeta_package K Λ hΛdiff hΛFE hΛeq
      hB1 hEnd hSL
  have hZ1 := L92Z.sum_re_inv_two_sub_le K Λ hΛFE hΛeq B ρ hρ hρsum hexp
  exact ⟨B, ρ, hρ, hρsum,
    fun j => L92Z.re_le_of_dedekindZeroFreeRight K Λ hΛdiff hΛeq B ρ hρ hρsum hexp σ hZ j,
    hZ1.1, hZ1.2, fun s hs => L92Z.neg_logDeriv_dedekindZeta_eq K Λ hΛeq B ρ hρ hexp s hs⟩

/-- **Lemma 9.2 from parts.** The Mellin-side facts for `Φ` (M1, M2, M3, M4) are hypotheses;
the zero side is Z1–Z3. -/
theorem L92A_estimate_of_parts (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (f : ℝ → ℝ) (Φ : ℂ → ℂ)
    (a : ℝ) (ha : 0 < a)
    (hΦc : Continuous fun t : ℝ => Φ (2 + t * I)) (CΦ : ℝ)
    (hΦd : ∀ t : ℝ, ‖Φ (2 + t * I)‖ ≤ CΦ * (1 + |t|) ^ (-4 : ℝ))
    (C₃ : ℝ) (hΦs : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Φ w‖ ≤ C₃ / (4 + w.im ^ 2))
    (c : ℝ) (hneg : ∀ k : ℕ, ‖Φ (-(k : ℂ))‖ ≤ c * (1 / a) ^ k)
    (hM2 : ∀ x : ℝ, 2 / a ≤ x → ∀ w : ℂ, w.re < 2 → (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) / (2 + t * I - w) = (x : ℂ) ^ w * Φ w)
    (hM2' : ∀ x : ℝ, 2 / a ≤ x → ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I) = 0)
    (hM1 : ∀ (K : Type) [Field K] [NumberField K] (x : ℝ), 0 < x →
      ((∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
        Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, -logDeriv (dedekindZeta K) (2 + t * I) *
        (x : ℂ) ^ ((2 : ℂ) + t * I) * Φ (2 + t * I))
    (C₄ : ℝ) (hM4 : ∀ (K : Type) [Field K] [NumberField K], ∀ x : ℝ, 0 < x →
      ∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
          Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) ≤
        C₄ * Module.finrank ℚ K * x) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K], DedekindZeroFreeRight K (1 - δ) →
      ∀ x : ℝ, 2 ≤ x →
        ∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
            Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) ≤
          C * (x + x ^ (1 - δ) * (Real.log |(discr K : ℝ)| + Module.finrank ℚ K)) := by
  have hC₃ : 0 ≤ C₃ := by
    have := (norm_nonneg _).trans (hΦs 0 le_rfl zero_le_one)
    simp at this
    linarith
  have hc : 0 ≤ c := by
    have := (norm_nonneg _).trans (hneg 0)
    simpa using this
  set M := max C₄ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hA0 : 0 ≤ ‖Φ 0‖ := norm_nonneg _
  have hA1 : 0 ≤ ‖Φ 1‖ := norm_nonneg _
  have h2a : 0 ≤ M * (2 / a) := mul_nonneg hM0 (by positivity)
  refine ⟨‖Φ 0‖ + ‖Φ 1‖ + 3 * C₃ + 2 * c + M * (2 / a), ?_⟩
  intro K _ _ hZ x hx2
  set Θ := ∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
    Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) with hΘ
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn
  set LD : ℝ := Real.log |(discr K : ℝ)| with hLD
  have hn1 : 1 ≤ n := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hn]
    exact_mod_cast this
  have hLD0 : 0 ≤ LD := by
    apply Real.log_nonneg
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hxp : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx1 (by linarith)
  set y := x ^ (1 - δ) * (LD + n) with hy
  have hyn : n ≤ y := by
    have : 1 * (LD + n) ≤ x ^ (1 - δ) * (LD + n) :=
      mul_le_mul_of_nonneg_right hxp (by linarith)
    linarith
  have expand : (‖Φ 0‖ + ‖Φ 1‖ + 3 * C₃ + 2 * c + M * (2 / a)) * (x + y) =
      (‖Φ 0‖ + ‖Φ 1‖) * x + (‖Φ 0‖ + ‖Φ 1‖) * y + (3 * C₃ + 2 * c) * x +
        (3 * C₃ + 2 * c) * y + M * (2 / a) * (x + y) := by ring
  have hy0 : 0 ≤ y := by linarith
  have p1 : 0 ≤ (‖Φ 0‖ + ‖Φ 1‖) * y := by positivity
  have p2 : 0 ≤ (3 * C₃ + 2 * c) * x := by positivity
  have p3 : 0 ≤ M * (2 / a) * (x + y) := by positivity
  have p4 : 0 ≤ (‖Φ 0‖ + ‖Φ 1‖) * x := by positivity
  have p5 : 0 ≤ (3 * C₃ + 2 * c) * y := by positivity
  by_cases hxa : 2 / a ≤ x
  · obtain ⟨B, ρ, hρ, hρs, hσ, hS1, hS2, hZ3⟩ := L92A_zero_data K (1 - δ) hZ
    have hb := L92A_theta_line_bound hx0 hΦc hΦd (hM2 x hxa) (hM2' x hxa) ha hxa hneg B ρ hρ hρs
      LD (InfinitePlace.nrRealPlaces K) (InfinitePlace.nrComplexPlaces K)
      (fun s => -logDeriv (dedekindZeta K) s) hZ3
    have hz := L92A_zero_sum_le hx1 hΦs ρ hρ (1 - δ) hσ hS1
    have hΘle : Θ ≤ ‖((Θ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    rw [hM1 K x hx0] at hΘle
    have hr : ((InfinitePlace.nrRealPlaces K : ℕ) : ℝ) + (InfinitePlace.nrComplexPlaces K : ℕ)
        ≤ n := by
      have h := InfinitePlace.card_add_two_mul_card_eq_rank K
      have : InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K ≤
          Module.finrank ℚ K := by omega
      rw [hn]
      exact_mod_cast this
    have hz2 : C₃ * x ^ (1 - δ) * ∑' j, (1 / (2 - ρ j)).re ≤ 3 * C₃ * y := by
      have h1 : ∑' j, (1 / (2 - ρ j)).re ≤ 3 * (LD + n) := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC₃ (by positivity : 0 ≤ x ^ (1 - δ)))
      rw [hy]
      linarith
    have hr2 : (((InfinitePlace.nrRealPlaces K : ℕ) : ℝ) +
        (InfinitePlace.nrComplexPlaces K : ℕ)) * (2 * c) ≤ 2 * c * y := by
      have := mul_le_mul_of_nonneg_right (hr.trans hyn) (by positivity : 0 ≤ 2 * c)
      linarith
    have hA0x : ‖Φ 0‖ ≤ ‖Φ 0‖ * x := le_mul_of_one_le_right hA0 hx1
    linarith
  · rw [not_le] at hxa
    have h4 := hM4 K x hx0
    have h5 : C₄ * n * x ≤ M * n * x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        hx0.le
    have h6 : M * n * x ≤ M * n * (2 / a) :=
      mul_le_mul_of_nonneg_left hxa.le (mul_nonneg hM0 (by linarith))
    have h7 : M * n * (2 / a) ≤ M * (2 / a) * y := by
      have := mul_le_mul_of_nonneg_left hyn h2a
      linarith
    have h8 : M * (2 / a) * y ≤ M * (2 / a) * (x + y) :=
      mul_le_mul_of_nonneg_left (by linarith) h2a
    linarith

end ArtinPrimitiveRoots
end

section
/-! # Check: Lemma 9.2 `smooth_prime_ideal_estimate` (A assembly of Z and M) -/

namespace ArtinPrimitiveRoots

open NumberField Complex

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField Complex
theorem solution (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Set.Ioi 0)
    (hf0 : ∀ t, 0 ≤ f t) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K], DedekindZeroFreeRight K (1 - δ) →
      ∀ x : ℝ, 2 ≤ x →
        ∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
            Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) ≤
          C * (x + x ^ (1 - δ) * (Real.log |(discr K : ℝ)| + Module.finrank ℚ K)) := by
  obtain ⟨a, b, ha, hab⟩ := L92M.exists_tsupport_subset_Icc f hfc hfs
  have hΦdiff := L92M.mellin_differentiable f hf a b ha hab
  have hΦc : Continuous fun t : ℝ => mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I) :=
    hΦdiff.continuous.comp (by fun_prop)
  obtain ⟨CΦ, hCΦ⟩ := L92M.mellin_decay_rpow f hf a b ha hab 4 2 2
  have hΦd : ∀ t : ℝ, ‖mellin (fun u : ℝ => (f u : ℂ)) (2 + t * I)‖ ≤
      CΦ * (1 + |t|) ^ (-4 : ℝ) := fun t => by
    simpa using hCΦ (2 + t * I) (by simp) (by simp)
  obtain ⟨C₃, hC₃⟩ := L92M.mellin_le_strip f hf a b ha hab
  have hneg : ∀ k : ℕ, ‖mellin (fun u : ℝ => (f u : ℂ)) (-(k : ℂ))‖ ≤
      ((∫ t, |f t|) / a) * (1 / a) ^ k := fun k => by
    refine (L92M.mellin_neg_nat_le f hf a b ha hab k).trans (le_of_eq ?_)
    rw [pow_succ, one_div_pow]
    field_simp
  obtain ⟨C₄, hC₄⟩ := L92M.theta_le f hf a b ha hab hf0
  exact L92A_estimate_of_parts δ hδ (by linarith) f (mellin (fun u : ℝ => (f u : ℂ))) a ha hΦc CΦ
    hΦd C₃ hC₃ _ hneg (fun x hx w hw => (L92M.line_integral_div f hf a b ha hab x hx w hw).2)
    (fun x hx => (L92M.line_integral_eq_zero f hf a b ha hab x hx).2)
    (fun K _ _ x hx => L92M.theta_eq_integral f hf a b ha hab K x hx) C₄ hC₄
end
