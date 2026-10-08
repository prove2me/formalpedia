-- Prove2me | solution 1 for AhlforsComplexAnalysis.riemann_mapping_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T11:45:29.739968+00:00
-- url     : https://prove2.me/submissions/91668889-15cd-437b-8d4f-348241783e76

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs
import Theorems.Thm_AhlforsComplexAnalysis_hurwitz
import Theorems.Thm_AhlforsComplexAnalysis_normal_iff_locally_bounded
import Theorems.Thm_AhlforsComplexAnalysis_exists_log_and_root
import Theorems.Thm_AhlforsComplexAnalysis_schwarz_lemma


open Complex Set Metric Filter Topology

namespace RMB

/-- A logarithm exists on any region on which every holomorphic function has a primitive. -/
theorem exists_log_of_prim {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hprim : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g Ω → ∃ F : ℂ → ℂ, ∀ z ∈ Ω, HasDerivAt F (g z) z)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L Ω ∧ ∀ z ∈ Ω, exp (L z) = f z := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, differentiableOn_empty, fun z hz => hz.elim⟩
  have hg : DifferentiableOn ℂ (fun z => deriv f z / f z) Ω :=
    (hf.deriv hΩ).div hf hf0
  obtain ⟨F, hF⟩ := hprim _ hg
  have hfd : ∀ z ∈ Ω, HasDerivAt f (deriv f z) z := fun z hz =>
    ((hf z hz).differentiableAt (hΩ.mem_nhds hz)).hasDerivAt
  set u : ℂ → ℂ := fun z => f z * exp (-F z) with hu
  have hud : ∀ z ∈ Ω, HasDerivAt u 0 z := by
    intro z hz
    have := (hfd z hz).mul ((hF z hz).neg.cexp)
    refine this.congr_deriv ?_
    have h : f z * (deriv f z / f z) = deriv f z := mul_div_cancel₀ _ (hf0 z hz)
    linear_combination (-exp (-F z)) * h
  have hconst : ∀ z ∈ Ω, u z = u a := by
    intro z hz
    exact hΩ.is_const_of_deriv_eq_zero hc (fun w hw => (hud w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hud w hw).deriv) hz ha
  have hua : u a ≠ 0 := mul_ne_zero (hf0 a ha) (exp_ne_zero _)
  refine ⟨fun z => F z + log (u a), ?_, fun z hz => ?_⟩
  · exact (fun z hz => ((hF z hz).differentiableAt.add_const _).differentiableWithinAt)
  · rw [exp_add, exp_log hua, ← hconst z hz, hu]
    simp only
    rw [mul_comm (f z), ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- Roots of nonvanishing holomorphic functions on a disk. -/
theorem exists_root_ball {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c r))
    (hf0 : ∀ z ∈ ball c r, f z ≠ 0) {n : ℕ} (hn : 0 < n) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (ball c r) ∧ ∀ z ∈ ball c r, R z ^ n = f z := by
  obtain ⟨L, hLd, hL⟩ := exists_log_of_prim isOpen_ball (convex_ball c r).isPreconnected
    (fun g hg => hg.isExactOn_ball) hf hf0
  refine ⟨fun z => exp (L z / n), (hLd.div_const (n : ℂ)).cexp, fun z hz => ?_⟩
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn.ne'), hL z hz]



/-! ## Injective holomorphic maps -/

/-- An injective holomorphic map has nonvanishing derivative. -/
theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hinj : InjOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    deriv f z₀ ≠ 0 := by
  intro hd
  set g : ℂ → ℂ := fun z => f z - f z₀ with hg
  have hga : AnalyticAt ℂ g z₀ := (hf z₀ hz₀).sub analyticAt_const
  -- `g` does not vanish identically near `z₀`
  have hnz : ¬ ∀ᶠ z in 𝓝 z₀, g z = 0 := by
    intro h
    have h2 : ∀ᶠ z in 𝓝[≠] z₀, z ∈ U ∧ g z = 0 :=
      nhdsWithin_le_nhds ((hU.eventually_mem hz₀).and h)
    obtain ⟨z, ⟨hzU, hz0⟩, hne⟩ := (h2.and self_mem_nhdsWithin).exists
    apply hne
    apply hinj hzU hz₀
    simpa [hg, sub_eq_zero] using hz0
  obtain ⟨n, u, hu, hu0, hfac⟩ := (hga.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnz
  replace hfac : ∀ᶠ z in 𝓝 z₀, g z = (z - z₀) ^ n * u z :=
    hfac.mono fun z hz => by rw [hz, smul_eq_mul]
  -- the order is at least two
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n
    · have := hfac.self_of_nhds
      simp [hg] at this
      exact hu0 this.symm
    · have h1 : deriv g z₀ = deriv (fun z => (z - z₀) ^ 1 * u z) z₀ :=
        Filter.EventuallyEq.deriv_eq hfac
      have h2 : HasDerivAt (fun z => (z - z₀) ^ 1 * u z) (u z₀) z₀ := by
        have := ((hasDerivAt_id z₀).sub_const z₀).mul hu.differentiableAt.hasDerivAt
        exact (this.congr_deriv (by simp)).congr_of_eventuallyEq
          (Eventually.of_forall fun z => by simp)
      have h3 : deriv g z₀ = deriv f z₀ := by
        simp only [hg]; rw [deriv_sub_const]
      rw [h3, hd, h2.deriv] at h1
      apply hu0; simpa using h1.symm
  -- a ball on which everything holds
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ g z = (z - z₀) ^ n * u z ∧ u z ≠ 0 ∧ AnalyticAt ℂ u z :=
    (hU.eventually_mem hz₀).and (hfac.and ((hu.continuousAt.eventually_ne hu0).and hu.eventually_analyticAt))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- an `n`-th root of `u` on the ball
  obtain ⟨w, hwd, hw⟩ := exists_root_ball (c := z₀) (r := r) (f := u)
    (fun z hz => (hball z hz).2.2.2.differentiableAt.differentiableWithinAt)
    (fun z hz => (hball z hz).2.2.1) (by omega : 0 < n)
  set h : ℂ → ℂ := fun z => (z - z₀) * w z with hh
  have hpow : ∀ z ∈ ball z₀ r, g z = h z ^ n := by
    intro z hz
    rw [(hball z hz).2.1, hh, mul_pow, hw z hz]
  have hw0 : w z₀ ≠ 0 := by
    intro h0
    apply hu0
    rw [← hw z₀ (mem_ball_self hr), h0, zero_pow (by omega)]
  have hwa : AnalyticAt ℂ w z₀ := (hwd.analyticOnNhd isOpen_ball) z₀ (mem_ball_self hr)
  have hhd : HasDerivAt h (w z₀) z₀ := by
    have := ((hasDerivAt_id z₀).sub_const z₀).mul hwa.differentiableAt.hasDerivAt
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp [hh])
  have hha : AnalyticAt ℂ h z₀ := (analyticAt_id.sub analyticAt_const).mul hwa
  have hhs : HasStrictDerivAt h (w z₀) z₀ := by
    have := hha.hasStrictDerivAt
    rwa [hhd.deriv] at this
  have hmap := hhs.map_nhds_eq hw0
  have himg : h '' ball z₀ r ∈ 𝓝 (0 : ℂ) := by
    have := Filter.image_mem_map (m := h) (ball_mem_nhds z₀ hr)
    rw [hmap] at this
    simpa [hh] using this
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.1 himg
  set ζ : ℂ := exp (2 * Real.pi * I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := isPrimitiveRoot_exp n (by omega)
  have hζ1 : ζ ≠ 1 := hprim.ne_one (by omega)
  have hζn : ‖ζ‖ = 1 := by
    have := hprim.norm'_eq_one (by omega)
    exact this
  set e : ℂ := ((ε / 2 : ℝ) : ℂ) with he
  have hen : ‖e‖ = ε / 2 := by simp [he, abs_of_pos hε]
  obtain ⟨z₁, hz₁, hz₁e⟩ := hεb (by simp [hen]; linarith : e ∈ ball (0:ℂ) ε)
  obtain ⟨z₂, hz₂, hz₂e⟩ := hεb (by simp [norm_mul, hen, hζn]; linarith : e * ζ ∈ ball (0:ℂ) ε)
  have he0 : e ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hen; linarith
  have hne : z₁ ≠ z₂ := by
    intro h12
    rw [h12, hz₂e] at hz₁e
    apply hζ1
    have := mul_left_cancel₀ he0 (hz₁e.trans (mul_one e).symm)
    exact this
  apply hne
  apply hinj (hball z₁ hz₁).1 (hball z₂ hz₂).1
  have h1 := hpow z₁ hz₁
  have h2 := hpow z₂ hz₂
  rw [hz₁e] at h1
  rw [hz₂e, mul_pow, hprim.pow_eq_one, mul_one] at h2
  simp only [hg] at h1 h2
  linear_combination h1 - h2

/-- The inverse of an injective holomorphic map on a region is holomorphic on the image. -/
theorem analyticOnNhd_invFunOn {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (hne : U.Nonempty) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hinj : InjOn f U) :
    IsOpen (f '' U) ∧ AnalyticOnNhd ℂ (Function.invFunOn f U) (f '' U) := by
  -- `f` is an open map on `U`
  have hnc : ¬ ∃ w, ∀ z ∈ U, f z = w := by
    rintro ⟨w, hw⟩
    obtain ⟨z, hz⟩ := hne
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
    have hz' : z + (r / 2 : ℝ) ∈ U := hrU (by
      rw [mem_ball, dist_eq_norm]; simp [abs_of_pos hr]; linarith)
    have := hinj hz hz' ((hw z hz).trans (hw _ hz').symm)
    have h2 : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -this
    have : r / 2 = 0 := by exact_mod_cast h2
    linarith
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) :=
    (hf.is_constant_or_isOpen hc).resolve_left hnc
  refine ⟨hopen U subset_rfl hU, ?_⟩
  set G := Function.invFunOn f U with hG
  have hleft : ∀ z ∈ U, G (f z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hdpt : ∀ z ∈ U, HasDerivAt G (deriv f z)⁻¹ (f z) := by
   intro z hz
   have hcont : ContinuousAt G (f z) := by
    rw [ContinuousAt, hleft z hz, (nhds_basis_opens z).tendsto_right_iff]
    rintro t ⟨hzt, ht⟩
    have hmem : f '' (t ∩ U) ∈ 𝓝 (f z) :=
      (hopen _ inter_subset_right (ht.inter hU)).mem_nhds ⟨z, ⟨hzt, hz⟩, rfl⟩
    filter_upwards [hmem] with y hy
    obtain ⟨x, ⟨hxt, hxU⟩, rfl⟩ := hy
    rw [hleft x hxU]; exact hxt
   apply HasDerivAt.of_local_left_inverse hcont
   · rw [hleft z hz]; exact (hf z hz).differentiableAt.hasDerivAt
   · exact deriv_ne_zero_of_injOn hU hf hinj hz
   · filter_upwards [(hopen U subset_rfl hU).mem_nhds ⟨z, hz, rfl⟩] with y hy
     obtain ⟨x, hx, rfl⟩ := hy
     rw [hleft x hx]
  have hdiff : DifferentiableOn ℂ G (f '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hdpt x hx).differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd (hopen U subset_rfl hU)

end RMB


open Complex Set Metric Filter Topology ComplexConjugate

namespace RMB

/-! ## Möbius transformations of the unit disk -/

/-- `φ_a(ζ) = (ζ - a) / (1 - ā ζ)`. -/
noncomputable def mob (a ζ : ℂ) : ℂ := (ζ - a) / (1 - conj a * ζ)

lemma mob_den_ne {a ζ : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ ≤ 1) : 1 - conj a * ζ ≠ 0 := by
  intro h
  have h1 : conj a * ζ = 1 := by linear_combination -h
  have : ‖conj a * ζ‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖ζ‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by linarith
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

lemma normSq_identity (a ζ : ℂ) :
    normSq (1 - conj a * ζ) - normSq (ζ - a) = (1 - normSq a) * (1 - normSq ζ) := by
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, mul_re, mul_im, conj_re, conj_im]
  ring

lemma norm_mob_lt {a ζ : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ < 1) : ‖mob a ζ‖ < 1 := by
  have hd := mob_den_ne ha hζ.le
  rw [mob, norm_div, div_lt_one (norm_pos_iff.2 hd)]
  have h1 : normSq (ζ - a) < normSq (1 - conj a * ζ) := by
    have := normSq_identity a ζ
    have ha' : normSq a < 1 := by
      rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
    have hζ' : normSq ζ < 1 := by
      rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
    nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (ζ - a), norm_nonneg (1 - conj a * ζ)]

lemma mob_self (a : ℂ) : mob a a = 0 := by simp [mob]

lemma mob_zero (a : ℂ) : mob a 0 = -a := by simp [mob]

lemma conj_mul_self (a : ℂ) : conj a * a = (normSq a : ℂ) := by
  rw [mul_comm, mul_conj]

lemma mob_inv {a ζ : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ < 1) : mob (-a) (mob a ζ) = ζ := by
  have hd := mob_den_ne ha hζ.le
  have hna : (1 : ℂ) - normSq a ≠ 0 := by
    have : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
    intro h
    have h2 : ((1 - normSq a : ℝ) : ℂ) = 0 := by push_cast; exact h
    have : (1 - normSq a : ℝ) = 0 := by exact_mod_cast h2
    linarith
  have hN : 1 - conj a * a ≠ 0 := by rw [conj_mul_self]; exact hna
  unfold mob
  rw [map_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
  have h1 : (ζ - a) / (1 - conj a * ζ) + a = ζ * (1 - conj a * a) / (1 - conj a * ζ) := by
    rw [div_add' _ _ _ hd]; congr 1; ring
  have h2 : 1 + conj a * ((ζ - a) / (1 - conj a * ζ)) = (1 - conj a * a) / (1 - conj a * ζ) := by
    rw [mul_div_assoc', one_add_div hd]; congr 1; ring
  rw [h1, h2, div_div_div_cancel_right₀ hd, mul_div_cancel_right₀ ζ hN]

lemma mob_injOn {a : ℂ} (ha : ‖a‖ < 1) : InjOn (mob a) (ball 0 1) := by
  intro x hx y hy hxy
  rw [mem_ball_zero_iff] at hx hy
  rw [← mob_inv ha hx, ← mob_inv ha hy, hxy]

lemma hasDerivAt_mob {a ζ : ℂ} (hd : 1 - conj a * ζ ≠ 0) :
    HasDerivAt (mob a) ((1 - normSq a) / (1 - conj a * ζ) ^ 2) ζ := by
  have h := ((hasDerivAt_id ζ).sub_const a).div
    (((hasDerivAt_id ζ).const_mul (conj a)).const_sub 1) hd
  refine h.congr_deriv ?_
  have hcs := conj_mul_self a
  simp only [id]
  rw [← hcs]
  field_simp
  ring

lemma analyticOnNhd_mob {a : ℂ} (ha : ‖a‖ < 1) : AnalyticOnNhd ℂ (mob a) (ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro ζ hζ
  rw [mem_ball_zero_iff] at hζ
  exact (hasDerivAt_mob (mob_den_ne ha hζ.le)).differentiableAt.differentiableWithinAt

/-! ## Normalization -/

/-- The normalized class of maps used in the extremal problem. -/
def Fam (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f Ω ∧ InjOn f Ω ∧ (∀ z ∈ Ω, ‖f z‖ < 1) ∧ f z₀ = 0 ∧
    0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0

/-- Any injective holomorphic map of `Ω` into the disk can be normalized, with the explicit
value `|F'(z₀)| / (1 - |F(z₀)|²)` of the new derivative. -/
theorem normalize {Ω : Set ℂ} (hΩ : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Ω) (hinj : InjOn F Ω) (hb : ∀ z ∈ Ω, ‖F z‖ < 1) :
    ∃ G : ℂ → ℂ, Fam Ω z₀ G ∧
      deriv G z₀ = ((‖deriv F z₀‖ / (1 - ‖F z₀‖ ^ 2) : ℝ) : ℂ) := by
  set a := F z₀ with ha
  have ha1 : ‖a‖ < 1 := hb z₀ hz₀
  have hden : (1 : ℝ) - ‖a‖ ^ 2 > 0 := by nlinarith [norm_nonneg a]
  set M : ℂ → ℂ := fun z => mob a (F z) with hM
  have hMa : AnalyticOnNhd ℂ M Ω := (analyticOnNhd_mob ha1).comp hF
    (fun z hz => mem_ball_zero_iff.2 (hb z hz))
  have hMd : HasDerivAt M ((1 - normSq a) / (1 - conj a * a) ^ 2 * deriv F z₀) z₀ :=
    (hasDerivAt_mob (mob_den_ne ha1 ha1.le)).comp z₀
      ((hF z₀ hz₀).differentiableAt.hasDerivAt)
  have hF0 : deriv F z₀ ≠ 0 := deriv_ne_zero_of_injOn hΩ hF hinj hz₀
  set c := (1 - normSq a) / (1 - conj a * a) ^ 2 * deriv F z₀ with hc
  have hcs := conj_mul_self a
  have hnsq : normSq a = ‖a‖ ^ 2 := normSq_eq_norm_sq a
  have hc' : c = deriv F z₀ / (1 - (‖a‖ ^ 2 : ℝ)) := by
    rw [hc, hcs, hnsq]
    have : (1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      intro h
      have h2 : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast at h ⊢; exact h
      have : (1 - ‖a‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h2
      linarith
    field_simp
  have hc0 : c ≠ 0 := by
    rw [hc']
    refine div_ne_zero hF0 ?_
    intro h
    have h2 : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast at h ⊢; exact h
    have : (1 - ‖a‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h2
    linarith
  have hcn : ‖c‖ = ‖deriv F z₀‖ / (1 - ‖a‖ ^ 2) := by
    rw [hc', norm_div]
    congr 1
    rw [show (1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  set u : ℂ := conj c / (‖c‖ : ℂ) with hu
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcpos, div_self hcpos.ne']
  have huc : u * c = (‖c‖ : ℂ) := by
    rw [hu, div_mul_eq_mul_div, mul_comm (conj c), mul_conj, normSq_eq_norm_sq]
    have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    field_simp
    push_cast; ring
  refine ⟨fun z => u * M z, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact analyticOnNhd_const.mul hMa
  · intro x hx y hy hxy
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hun; exact zero_ne_one hun
    have h1 : M x = M y := mul_left_cancel₀ hu0 hxy
    exact hinj hx hy (mob_injOn ha1 (mem_ball_zero_iff.2 (hb x hx))
      (mem_ball_zero_iff.2 (hb y hy)) h1)
  · intro z hz
    rw [norm_mul, hun, one_mul]
    exact norm_mob_lt ha1 (hb z hz)
  · simp [hM, ← ha, mob_self]
  · rw [(hMd.const_mul u).deriv, huc]; simp [hcpos]
  · rw [(hMd.const_mul u).deriv, huc]; simp
  · rw [(hMd.const_mul u).deriv, huc, hcn]

end RMB


open Complex Set Metric Filter Topology ComplexConjugate

namespace RMB

open AhlforsComplexAnalysis

section Existence

variable {Ω : Set ℂ} (hΩ : IsSimplyConnectedRegion Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)

include hΩ hz₀ in
/-- Step 1: an injective holomorphic map of `Ω` into the unit disk (via `√(z - a)`). -/
lemma exists_inj_into_disk (hne : Ω ≠ univ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F Ω ∧ InjOn F Ω ∧ ∀ z ∈ Ω, ‖F z‖ < 1 := by
  obtain ⟨a, ha⟩ := (ne_univ_iff_exists_notMem Ω).1 hne
  have hΩo : IsOpen Ω := hΩ.1.1
  have hfa : AnalyticOnNhd ℂ (fun z => z - a) Ω := fun z _ => analyticAt_id.sub analyticAt_const
  have hf0 : ∀ z ∈ Ω, z - a ≠ 0 := fun z hz h => ha (by rw [sub_eq_zero] at h; exact h ▸ hz)
  obtain ⟨h, hha, hh⟩ := (exists_log_and_root hΩ hfa hf0).2 2 two_pos
  have hinj : InjOn h Ω := by
    intro x hx y hy hxy
    have := (hh x hx).symm.trans (hxy ▸ hh y hy)
    linear_combination this
  have hneg : ∀ x ∈ Ω, ∀ y ∈ Ω, h x ≠ -h y := by
    intro x hx y hy hxy
    have h1 : x - a = y - a := by rw [← hh x hx, ← hh y hy, hxy]; ring
    have hxy' : x = y := by linear_combination h1
    subst hxy'
    have h0 : h x = 0 := by linear_combination hxy / 2
    exact hf0 x hx (by rw [← hh x hx, h0]; ring)
  obtain ⟨hopen, -⟩ := analyticOnNhd_invFunOn hΩo hΩ.1.2.isPreconnected ⟨z₀, hz₀⟩ hha hinj
  set b := h z₀ with hb
  obtain ⟨ρ, hρ, hρb⟩ := Metric.isOpen_iff.1 hopen b ⟨z₀, hz₀, rfl⟩
  have hfar : ∀ z ∈ Ω, ρ ≤ ‖h z + b‖ := by
    intro z hz
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hyz⟩ := hρb (show -h z ∈ ball b ρ by
      rw [mem_ball, dist_eq_norm, show -h z - b = -(h z + b) by ring, norm_neg]; exact hlt)
    exact hneg y hy z hz hyz
  have hne0 : ∀ z ∈ Ω, h z + b ≠ 0 := fun z hz h0 => by
    have := hfar z hz; rw [h0, norm_zero] at this; linarith
  refine ⟨fun z => (ρ : ℂ) / (2 * (h z + b)), ?_, ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.div (analyticAt_const.mul ((hha z hz).add analyticAt_const))
      (mul_ne_zero two_ne_zero (hne0 z hz))
  · intro x hx y hy hxy
    have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    have h1 : 2 * (h x + b) = 2 * (h y + b) := by
      have := hxy
      simp only at this
      rw [div_eq_div_iff (mul_ne_zero two_ne_zero (hne0 x hx))
        (mul_ne_zero two_ne_zero (hne0 y hy))] at this
      exact (mul_left_cancel₀ hρ0 this).symm
    exact hinj hx hy (by linear_combination h1 / 2)
  · intro z hz
    have hpos : 0 < ‖h z + b‖ := norm_pos_iff.2 (hne0 z hz)
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      Complex.norm_two, div_lt_one (by positivity)]
    linarith [hfar z hz]

include hΩ hz₀ in
/-- Cauchy estimate: derivatives at `z₀` of maps into the disk are bounded. -/
lemma deriv_bound : ∃ C : ℝ, ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω → (∀ z ∈ Ω, ‖f z‖ < 1) →
    ‖deriv f z₀‖ ≤ C := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 hΩ.1.1 z₀ hz₀
  refine ⟨1 / (R / 2), fun f hf hb => ?_⟩
  have hsub : closedBall z₀ (R / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hRΩ
  apply norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith)
    (hf.differentiableOn.diffContOnCl_ball hsub)
  intro z hz
  exact (hb z (hsub (sphere_subset_closedBall hz))).le

include hΩ hz₀ in
/-- Step 2: the extremal problem has a solution. -/
lemma exists_extremal (hne : Ω ≠ univ) :
    ∃ g : ℂ → ℂ, Fam Ω z₀ g ∧ ∀ f, Fam Ω z₀ f → (deriv f z₀).re ≤ (deriv g z₀).re := by
  have hΩo : IsOpen Ω := hΩ.1.1
  have hΩc : IsPreconnected Ω := hΩ.1.2.isPreconnected
  set A : Set ℝ := {x | ∃ f, Fam Ω z₀ f ∧ (deriv f z₀).re = x} with hA
  have hAne : A.Nonempty := by
    obtain ⟨F, hF, hFi, hFb⟩ := exists_inj_into_disk hΩ hz₀ hne
    obtain ⟨G, hG, -⟩ := normalize hΩo hz₀ hF hFi hFb
    exact ⟨_, G, hG, rfl⟩
  obtain ⟨C, hC⟩ := deriv_bound hΩ hz₀
  have hAbdd : BddAbove A := by
    refine ⟨C, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact (Complex.re_le_norm _).trans (hC f hf.1 hf.2.2.1)
  set B := sSup A with hB
  have hBpos : 0 < B := by
    obtain ⟨_, f, hf, rfl⟩ := hAne
    exact hf.2.2.2.2.1.trans_le (le_csSup hAbdd ⟨f, hf, rfl⟩)
  have hseq : ∀ n : ℕ, ∃ f, Fam Ω z₀ f ∧ B - 1 / ((n : ℝ) + 1) < (deriv f z₀).re := by
    intro n
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨f, hf, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hAne
      (show B - 1 / ((n : ℝ) + 1) < B by linarith)
    exact ⟨f, hf, hlt⟩
  choose fs hfs hfsB using hseq
  have hle : ∀ n, (deriv (fs n) z₀).re ≤ B := fun n => le_csSup hAbdd ⟨fs n, hfs n, rfl⟩
  -- normality
  have hnorm : IsNormalFamily (range fs) Ω := by
    rw [normal_iff_locally_bounded hΩ.1 (by rintro _ ⟨n, rfl⟩; exact (hfs n).1)]
    intro K hKΩ _
    exact ⟨1, by rintro _ ⟨n, rfl⟩ z hz; exact ((hfs n).2.2.1 z (hKΩ hz)).le⟩
  obtain ⟨φ, hφ, g, hconv⟩ := hnorm fs (fun n => mem_range_self n)
  have hloc : TendstoLocallyUniformlyOn (fun n => fs (φ n)) g atTop Ω :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩo).2 hconv
  have hdF : ∀ᶠ n in atTop, DifferentiableOn ℂ (fs (φ n)) Ω :=
    Eventually.of_forall fun n => (hfs (φ n)).1.differentiableOn
  have hgd : DifferentiableOn ℂ g Ω := hloc.differentiableOn hdF hΩo
  have hga : AnalyticOnNhd ℂ g Ω := hgd.analyticOnNhd hΩo
  have hval : ∀ z ∈ Ω, Tendsto (fun n => fs (φ n) z) atTop (𝓝 (g z)) :=
    fun z hz => hloc.tendsto_at hz
  have hder : Tendsto (fun n => deriv (fs (φ n)) z₀) atTop (𝓝 (deriv g z₀)) :=
    (hloc.deriv hdF hΩo).tendsto_at hz₀
  -- the derivative at `z₀` is `B`
  have hre : (deriv g z₀).re = B := by
    have h1 : Tendsto (fun n => (deriv (fs (φ n)) z₀).re) atTop (𝓝 (deriv g z₀).re) :=
      (Complex.continuous_re.tendsto _).comp hder
    have h0 : Tendsto (fun n => B - 1 / ((φ n : ℝ) + 1)) atTop (𝓝 B) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds (x := B)).sub this
    have h2 : Tendsto (fun n => (deriv (fs (φ n)) z₀).re) atTop (𝓝 B) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds
        (fun n => (hfsB (φ n)).le) (fun n => hle (φ n))
    exact tendsto_nhds_unique h1 h2
  have him : (deriv g z₀).im = 0 := by
    have h1 : Tendsto (fun n => (deriv (fs (φ n)) z₀).im) atTop (𝓝 (deriv g z₀).im) :=
      (Complex.continuous_im.tendsto _).comp hder
    have h2 : (fun n => (deriv (fs (φ n)) z₀).im) = fun _ => 0 :=
      funext fun n => (hfs (φ n)).2.2.2.2.2
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hg0 : g z₀ = 0 := by
    have := hval z₀ hz₀
    have h2 : (fun n => fs (φ n) z₀) = fun _ => 0 := funext fun n => (hfs (φ n)).2.2.2.1
    rw [h2] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hgle : ∀ z ∈ Ω, ‖g z‖ ≤ 1 := by
    intro z hz
    exact le_of_tendsto ((continuous_norm.tendsto _).comp (hval z hz))
      (Eventually.of_forall fun n => ((hfs (φ n)).2.2.1 z hz).le)
  have hglt : ∀ z ∈ Ω, ‖g z‖ < 1 := by
    intro z₁ hz₁
    by_contra hge
    push Not at hge
    have heq : ‖g z₁‖ = 1 := le_antisymm (hgle z₁ hz₁) hge
    have hmax : IsMaxOn (norm ∘ g) Ω z₁ := fun z hz => by
      simp only [Set.mem_ofPred_eq, Function.comp_apply, heq]; exact hgle z hz
    have := eqOn_of_isPreconnected_of_isMaxOn_norm hΩc hΩo hgd hz₁ hmax hz₀
    simp only [Function.const_apply] at this
    rw [← this, hg0, norm_zero] at heq
    exact zero_ne_one heq
  -- `g` is not constant
  have hgnc : ∀ c : ℂ, ¬ EqOn g (fun _ => c) Ω := by
    intro c hc
    have hev : g =ᶠ[𝓝 z₀] fun _ => c := Filter.eventually_of_mem (hΩo.mem_nhds hz₀) hc
    have := hev.deriv_eq
    rw [deriv_const] at this
    have h2 := hre
    rw [this, Complex.zero_re] at h2
    linarith
  -- injectivity, by Hurwitz's theorem
  have hginj : InjOn g Ω := by
    intro x hx y hy hxy
    by_contra hne
    obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 hΩo y hy
    set r := min (dist x y / 2) R with hr
    have hdxy : 0 < dist x y := dist_pos.2 hne
    have hr0 : 0 < r := lt_min (by linarith) hR
    have hD : ball y r ⊆ Ω := (ball_subset_ball (min_le_right _ _)).trans hRΩ
    have hxD : x ∉ ball y r := by
      rw [mem_ball]; intro h; have := min_le_left (dist x y / 2) R; linarith
    have hreg : IsRegion (ball y r) := ⟨isOpen_ball, isConnected_ball hr0⟩
    have hcases := hurwitz hreg (F := fun n z => fs (φ n) z - fs (φ n) x)
      (f := fun z => g z - g x)
      (fun n z hz => ((hfs (φ n)).1 z (hD hz)).sub analyticAt_const)
      (fun n z hz h0 => by
        have hzx : z = x := (hfs (φ n)).2.1 (hD hz) hx (by linear_combination h0)
        exact hxD (hzx ▸ hz))
      (fun K hK hKc => by
        have hKx : IsCompact (K ∪ {x}) := hKc.union isCompact_singleton
        have h1 := (hconv _ (union_subset (hK.trans hD) (singleton_subset_iff.2 hx)) hKx).mono
          subset_union_left
        have h2 := (hval x hx).tendstoUniformlyOn_const K
        exact h1.sub h2)
    rcases hcases with h0 | h0
    · apply hgnc (g x)
      have hev : g =ᶠ[𝓝 y] fun _ => g x := by
        filter_upwards [ball_mem_nhds y hr0] with z hz
        linear_combination h0 z hz
      exact hga.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩc hy hev
    · exact h0 y (mem_ball_self hr0) (by rw [hxy, sub_self])
  refine ⟨g, ⟨hga, hginj, hglt, hg0, by rw [hre]; exact hBpos, him⟩, fun f hf => ?_⟩
  rw [hre]
  exact le_csSup hAbdd ⟨f, hf, rfl⟩

include hΩ hz₀ in
/-- Step 3 (Koebe): an extremal map is onto the disk. -/
lemma extremal_onto {g : ℂ → ℂ} (hg : Fam Ω z₀ g)
    (hmax : ∀ f, Fam Ω z₀ f → (deriv f z₀).re ≤ (deriv g z₀).re) : g '' Ω = ball 0 1 := by
  have hΩo : IsOpen Ω := hΩ.1.1
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩; exact mem_ball_zero_iff.2 (hg.2.2.1 z hz)
  intro w₀ hw₀
  by_contra hnot
  have hw₀' : ‖w₀‖ < 1 := mem_ball_zero_iff.1 hw₀
  have hgw : ∀ z ∈ Ω, g z ≠ w₀ := fun z hz h => hnot ⟨z, hz, h⟩
  set B := (deriv g z₀).re with hB
  have hBpos : 0 < B := hg.2.2.2.2.1
  have hgB : deriv g z₀ = (B : ℂ) := Complex.ext (by simp [hB]) (by simp [hg.2.2.2.2.2])
  have hgb : ∀ z ∈ Ω, ‖g z‖ < 1 := hg.2.2.1
  set F : ℂ → ℂ := fun z => mob w₀ (g z) with hF
  have hFa : AnalyticOnNhd ℂ F Ω :=
    (analyticOnNhd_mob hw₀').comp hg.1 (fun z hz => mem_ball_zero_iff.2 (hgb z hz))
  have hF0 : ∀ z ∈ Ω, F z ≠ 0 := fun z hz =>
    div_ne_zero (sub_ne_zero.2 (hgw z hz)) (mob_den_ne hw₀' (hgb z hz).le)
  have hFi : InjOn F Ω := fun x hx y hy hxy =>
    hg.2.1 hx hy (mob_injOn hw₀' (mem_ball_zero_iff.2 (hgb x hx)) (mem_ball_zero_iff.2 (hgb y hy)) hxy)
  obtain ⟨G, hGa, hG⟩ := (exists_log_and_root hΩ hFa hF0).2 2 two_pos
  have hGb : ∀ z ∈ Ω, ‖G z‖ < 1 := by
    intro z hz
    have h1 : ‖G z‖ ^ 2 < 1 := by
      rw [← norm_pow, hG z hz]; exact norm_mob_lt hw₀' (hgb z hz)
    nlinarith [norm_nonneg (G z)]
  have hGi : InjOn G Ω := fun x hx y hy hxy =>
    hFi hx hy (by rw [← hG x hx, ← hG y hy, hxy])
  obtain ⟨H, hH, hHd⟩ := normalize hΩo hz₀ hGa hGi hGb
  have hle := hmax H hH
  rw [hHd, Complex.ofReal_re] at hle
  -- computations at `z₀`
  have hg0 : g z₀ = 0 := hg.2.2.2.1
  have hw0ne : w₀ ≠ 0 := fun h => hgw z₀ hz₀ (by rw [hg0, h])
  set s := ‖G z₀‖ with hs
  have hs2 : s ^ 2 = ‖w₀‖ := by
    rw [hs, ← norm_pow, hG z₀ hz₀, hF]
    simp only [hg0, mob_zero, norm_neg]
  have hspos : 0 < s := by
    have : 0 < ‖w₀‖ := norm_pos_iff.2 hw0ne
    by_contra hle
    push Not at hle
    have hs0 : s = 0 := le_antisymm hle (norm_nonneg _)
    rw [hs0] at hs2
    nlinarith
  have hs1 : s < 1 := by nlinarith
  have hFd : HasDerivAt F ((1 - normSq w₀) / (1 - conj w₀ * g z₀) ^ 2 * deriv g z₀) z₀ :=
    (hasDerivAt_mob (mob_den_ne hw₀' (hgb z₀ hz₀).le)).comp z₀
      ((hg.1 z₀ hz₀).differentiableAt.hasDerivAt)
  have hGd : HasDerivAt (fun z => G z ^ 2) ((2 : ℕ) * G z₀ ^ (2 - 1) * deriv G z₀) z₀ :=
    ((hGa z₀ hz₀).differentiableAt.hasDerivAt).pow 2
  have hev : (fun z => G z ^ 2) =ᶠ[𝓝 z₀] F := by
    filter_upwards [hΩo.mem_nhds hz₀] with z hz
    exact hG z hz
  have heq := (hGd.congr_of_eventuallyEq hev.symm).unique hFd
  rw [hg0, mul_zero, sub_zero, one_pow, div_one, hgB] at heq
  have hkey : ‖deriv G z₀‖ * (2 * s) = (1 - s ^ 4) * B := by
    have hn1 : ‖((1 : ℂ) - (normSq w₀ : ℂ))‖ = 1 - s ^ 4 := by
      rw [show (1 : ℂ) - (normSq w₀ : ℂ) = ((1 - normSq w₀ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, normSq_eq_norm_sq, ← hs2]
      rw [abs_of_nonneg (by nlinarith)]; ring
    have e1 : ‖((2 : ℕ) : ℂ) * G z₀ ^ (2 - 1) * deriv G z₀‖ = 2 * s * ‖deriv G z₀‖ := by
      simp [hs]
    have e2 : ‖((1 : ℂ) - (normSq w₀ : ℂ)) * (B : ℂ)‖ = (1 - s ^ 4) * B := by
      rw [norm_mul, hn1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBpos]
    have := congrArg norm heq
    rw [e1, e2] at this
    linarith
  have h1s : 0 < 1 - s ^ 2 := by nlinarith
  have hGle : ‖deriv G z₀‖ ≤ B * (1 - s ^ 2) := by
    rwa [div_le_iff₀ h1s] at hle
  have hpos : 0 < (1 - s ^ 2) * B * (1 - s) ^ 2 :=
    mul_pos (mul_pos h1s hBpos) (by nlinarith)
  nlinarith

include hΩ hz₀ in
/-- Existence part of the Riemann mapping theorem. -/
theorem riemann_exists (hne : Ω ≠ univ) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧
      (deriv f z₀).im = 0 ∧ InjOn f Ω ∧ f '' Ω = ball 0 1 := by
  obtain ⟨g, hg, hmax⟩ := exists_extremal hΩ hz₀ hne
  exact ⟨g, hg.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2, hg.2.1,
    extremal_onto hΩ hz₀ hg hmax⟩

end Existence

end RMB


open Complex Set Metric Filter Topology

namespace RMB

open AhlforsComplexAnalysis

/-- The normalization conditions of the Riemann mapping theorem. -/
def IsRiemannMap (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
    InjOn f Ω ∧ f '' Ω = ball 0 1

section Uniqueness

variable {Ω : Set ℂ} (hΩ : IsSimplyConnectedRegion Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)

include hΩ hz₀ in
/-- `f ∘ g⁻¹` satisfies the hypotheses of Schwarz's lemma. -/
lemma comp_inv_schwarz {f g : ℂ → ℂ} (hf : IsRiemannMap Ω z₀ f) (hg : IsRiemannMap Ω z₀ g) :
    AnalyticOnNhd ℂ (fun w => f (Function.invFunOn g Ω w)) (ball 0 1) ∧
    (∀ w ∈ ball (0 : ℂ) 1, ‖f (Function.invFunOn g Ω w)‖ ≤ 1) ∧
    f (Function.invFunOn g Ω 0) = 0 ∧
    ∀ z ∈ Ω, Function.invFunOn g Ω (g z) = z := by
  have hΩo : IsOpen Ω := hΩ.1.1
  obtain ⟨-, hGa⟩ := analyticOnNhd_invFunOn hΩo hΩ.1.2.isPreconnected ⟨z₀, hz₀⟩ hg.1 hg.2.2.2.2.1
  have hleft : ∀ z ∈ Ω, Function.invFunOn g Ω (g z) = z :=
    fun z hz => hg.2.2.2.2.1.leftInvOn_invFunOn hz
  have hmaps : MapsTo (Function.invFunOn g Ω) (ball 0 1) Ω := by
    intro w hw
    rw [← hg.2.2.2.2.2] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [hleft x hx]; exact hx
  rw [hg.2.2.2.2.2] at hGa
  refine ⟨hf.1.comp hGa hmaps, fun w hw => ?_, ?_, hleft⟩
  · have : f (Function.invFunOn g Ω w) ∈ f '' Ω := ⟨_, hmaps hw, rfl⟩
    rw [hf.2.2.2.2.2, mem_ball_zero_iff] at this
    exact this.le
  · rw [← hg.2.1, hleft z₀ hz₀, hf.2.1, hg.2.1]

include hΩ hz₀ in
lemma norm_le_of_riemann {f g : ℂ → ℂ} (hf : IsRiemannMap Ω z₀ f) (hg : IsRiemannMap Ω z₀ g) :
    ∀ z ∈ Ω, ‖f z‖ ≤ ‖g z‖ := by
  obtain ⟨ha, hb, h0, hleft⟩ := comp_inv_schwarz hΩ hz₀ hf hg
  have hs := (schwarz_lemma ha hb h0).1
  intro z hz
  have hgz : g z ∈ ball (0 : ℂ) 1 := by rw [← hg.2.2.2.2.2]; exact ⟨z, hz, rfl⟩
  have := hs (g z) hgz
  rwa [hleft z hz] at this

include hΩ hz₀ in
theorem riemann_unique {f g : ℂ → ℂ} (hf : IsRiemannMap Ω z₀ f) (hg : IsRiemannMap Ω z₀ g) :
    EqOn f g Ω := by
  have hΩo : IsOpen Ω := hΩ.1.1
  obtain ⟨ha, hb, h0, hleft⟩ := comp_inv_schwarz hΩ hz₀ hf hg
  have hfg := norm_le_of_riemann hΩ hz₀ hf hg
  have hgf := norm_le_of_riemann hΩ hz₀ hg hf
  -- equality in Schwarz at `w = 1/2`
  set G := Function.invFunOn g Ω with hG
  have hw : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; norm_num
  have hwimg : (1 / 2 : ℂ) ∈ g '' Ω := by rw [hg.2.2.2.2.2]; exact hw
  obtain ⟨x, hx, hgx⟩ := hwimg
  have heqn : ‖f (G (1 / 2))‖ = ‖(1 / 2 : ℂ)‖ := by
    rw [← hgx, hleft x hx]
    exact le_antisymm (hfg x hx) (hgf x hx)
  obtain ⟨c, hc1, hc⟩ := (schwarz_lemma ha hb h0).2.2
    (Or.inl ⟨1 / 2, hw, by norm_num, heqn⟩)
  have hfcg : ∀ z ∈ Ω, f z = c * g z := by
    intro z hz
    have hgz : g z ∈ ball (0 : ℂ) 1 := by rw [← hg.2.2.2.2.2]; exact ⟨z, hz, rfl⟩
    have := hc (g z) hgz
    rwa [hleft z hz] at this
  -- `c = 1` from the normalization of the derivatives
  have hev : f =ᶠ[𝓝 z₀] fun z => c * g z := by
    filter_upwards [hΩo.mem_nhds hz₀] with z hz
    exact hfcg z hz
  have hd : deriv f z₀ = c * deriv g z₀ := by
    rw [hev.deriv_eq]
    exact ((hg.1 z₀ hz₀).differentiableAt.hasDerivAt.const_mul c).deriv
  set a := (deriv f z₀).re
  set b := (deriv g z₀).re
  have hfa : deriv f z₀ = (a : ℂ) := Complex.ext (by simp [a]) (by simp [hf.2.2.2.1])
  have hgb : deriv g z₀ = (b : ℂ) := Complex.ext (by simp [b]) (by simp [hg.2.2.2.1])
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hg.2.2.1.ne'
  have hcab : c = ((a / b : ℝ) : ℂ) := by
    rw [hfa, hgb] at hd
    push_cast
    field_simp
    linear_combination -hd
  have hab : a / b = 1 := by
    have := hc1
    rw [hcab, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hf.2.2.1 hg.2.2.1)]
      at this
    exact this
  have hc1' : c = 1 := by rw [hcab, hab]; simp
  intro z hz
  rw [hfcg z hz, hc1', one_mul]

end Uniqueness

/-- **The Riemann mapping theorem.** -/
theorem riemann_mapping {Ω : Set ℂ} (hΩ : IsSimplyConnectedRegion Ω) (hne : Ω ≠ Set.univ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    (∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧
        0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) ∧
    ∀ f g : ℂ → ℂ,
      (AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) →
      (AnalyticOnNhd ℂ g Ω ∧ g z₀ = 0 ∧ 0 < (deriv g z₀).re ∧ (deriv g z₀).im = 0 ∧
        Set.InjOn g Ω ∧ g '' Ω = Metric.ball 0 1) →
      Set.EqOn f g Ω :=
  ⟨riemann_exists hΩ hz₀ hne, fun _ _ hf hg => riemann_unique hΩ hz₀ hf hg⟩

end RMB

open AhlforsComplexAnalysis

theorem solution {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) (hne : Ω ≠ Set.univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    (∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧
        0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) ∧
    ∀ f g : ℂ → ℂ,
      (AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) →
      (AnalyticOnNhd ℂ g Ω ∧ g z₀ = 0 ∧ 0 < (deriv g z₀).re ∧ (deriv g z₀).im = 0 ∧
        Set.InjOn g Ω ∧ g '' Ω = Metric.ball 0 1) →
      Set.EqOn f g Ω :=
  RMB.riemann_mapping hΩ hne hz₀
