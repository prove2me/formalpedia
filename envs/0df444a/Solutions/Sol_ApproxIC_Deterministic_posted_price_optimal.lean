-- Prove2me | solution 1 for ApproxIC.Deterministic.posted_price_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:36:01.637396+00:00
-- url     : https://prove2.me/submissions/5a91d024-2857-4820-b3f2-c276ecc6d235

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

open MeasureTheory

namespace ApproxIC.Deterministic

section Abstract
variable {Q T : ℝ → ℝ} {a b : ℝ}

def ICabs (Q T : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∀ x' ∈ Set.Icc a b, x * Q x' - T x' ≤ x * Q x - T x

lemma abs_mono (h : ICabs Q T a b) : MonotoneOn Q (Set.Icc a b) := by
  intro x hx y hy hxy
  have h1 := h x hx y hy
  have h2 := h y hy x hx
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · nlinarith

lemma abs_sub (h : ICabs Q T a b) {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    (y - x) * Q x ≤ (y * Q y - T y) - (x * Q x - T x) := by
  have := h y hy x hx; nlinarith

lemma abs_lip (h : ICabs Q T a b) (hab : a ≤ b) :
    LipschitzOnWith (Real.toNNReal (max |Q a| |Q b|)) (fun x => x * Q x - T x) (Set.Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hm := abs_mono h
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have bx : |Q x| ≤ max |Q a| |Q b| := by
    have := hm ha hx hx.1; have := hm hx hb hx.2
    rw [abs_le]; constructor
    · have := le_max_left |Q a| |Q b|; have := neg_abs_le (Q a); linarith
    · have := le_max_right |Q a| |Q b|; have := le_abs_self (Q b); linarith
  have byy : |Q y| ≤ max |Q a| |Q b| := by
    have := hm ha hy hy.1; have := hm hy hb hy.2
    rw [abs_le]; constructor
    · have := le_max_left |Q a| |Q b|; have := neg_abs_le (Q a); linarith
    · have := le_max_right |Q a| |Q b|; have := le_abs_self (Q b); linarith
  have h1 := abs_sub h hx hy
  have h2 := abs_sub h hy hx
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (le_trans (abs_nonneg _) (le_max_left _ _))]
  set M := max |Q a| |Q b|
  rw [abs_le]
  rcases le_total x y with hxy | hxy
  · have e1 : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [e1]
    have := abs_le.1 bx; have := abs_le.1 byy
    constructor <;> nlinarith
  · have e1 : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [e1]
    have := abs_le.1 bx; have := abs_le.1 byy
    constructor <;> nlinarith

/-- monotone extension -/
noncomputable def ext (Q : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) : ℝ → ℝ :=
  fun x => Q (Set.projIcc a b hab x)

lemma ext_mono (h : ICabs Q T a b) (hab : a ≤ b) : Monotone (ext Q a b hab) := by
  intro x y hxy
  exact abs_mono h (Set.projIcc a b hab x).2 (Set.projIcc a b hab y).2
    (Set.monotone_projIcc hab hxy)

lemma ext_eq (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) : ext Q a b hab x = Q x := by
  simp [ext, Set.projIcc_of_mem hab hx]

lemma abs_hasDerivAt (h : ICabs Q T a b) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hc : ContinuousAt (ext Q a b hab) x) :
    HasDerivAt (fun x => x * Q x - T x) (Q x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hxI : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
  have hev : ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∈ Set.Icc a b :=
    nhdsWithin_le_nhds (Icc_mem_nhds hx.1 hx.2)
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Filter.Tendsto (fun y => dist (ext Q a b hab y) (Q x)) (nhdsWithin x {x}ᶜ)
      (nhds 0) := by
    have : Filter.Tendsto (ext Q a b hab) (nhdsWithin x {x}ᶜ) (nhds (ext Q a b hab x)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [ext_eq hab hxI] at this
    exact (tendsto_iff_dist_tendsto_zero).1 this
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) _ hlim
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hyx
  rw [ext_eq hab hy, slope_def_field, Real.dist_eq, Real.dist_eq]
  have hyx' : y - x ≠ 0 := sub_ne_zero.2 hyx
  have h1 := abs_sub h hxI hy
  have h2 := abs_sub h hy hxI
  have hm := abs_mono h
  obtain ⟨s, hsD⟩ : ∃ s, (y * Q y - T y) - (x * Q x - T x) = s * (y - x) :=
    ⟨_, (div_mul_cancel₀ _ hyx').symm⟩
  rw [hsD, mul_div_cancel_right₀ _ hyx']
  rw [hsD] at h1
  have h2' : (x - y) * Q y ≤ -(s * (y - x)) := by linarith
  clear h2
  rcases lt_or_gt_of_ne hyx with hlt | hgt
  · have hQ := hm hy hxI hlt.le
    have b1 : s ≤ Q x := by nlinarith
    have b2 : Q y ≤ s := by nlinarith [h2']
    rw [abs_le]; constructor <;> rw [abs_of_nonpos (by linarith)] <;> linarith
  · have hQ := hm hxI hy hgt.le
    have b1 : Q x ≤ s := by nlinarith
    have b2 : s ≤ Q y := by nlinarith [h2']
    rw [abs_le]; constructor <;> rw [abs_of_nonneg (by linarith)] <;> linarith

lemma abs_payoff (h : ICabs Q T a b) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    x * Q x - T x = (a * Q a - T a) + ∫ y in a..x, Q y := by
  have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hx.2
  have key := integral_eq_of_hasDerivAt_off_countable_of_le (fun x => x * Q x - T x) Q hx.1
    (ext_mono h hab).countable_not_continuousAt
    ((abs_lip h hab).continuousOn.mono hsub)
    (fun y hy => abs_hasDerivAt h hab ⟨hy.1.1, lt_of_lt_of_le hy.1.2 hx.2⟩ (by
      by_contra hc; exact hy.2 hc))
    (by
      apply MonotoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hx.1]; exact (abs_mono h).mono hsub)
  rw [key]; ring

end Abstract

lemma aic3p_f_int (M : Model) (hM : M.Standing) : Integrable M.f :=
  hM.2.2.2.1.integrable_of_forall_notMem_eq_zero (fun x hx => hM.2.2.1 x hx)

lemma aic3p_f_ii (M : Model) (hM : M.Standing) (a b : ℝ) : IntervalIntegrable M.f volume a b :=
  (aic3p_f_int M hM).intervalIntegrable

lemma ae_ne_pt (p : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ p := by
  rw [ae_iff]; simp

lemma aic3p_cdfBar_eq' (M : Model) (hM : M.Standing) (c : ℝ) :
    cdfBar M c = ∫ u in c..M.vbar, M.f u := by
  unfold cdfBar cdf
  have := intervalIntegral.integral_add_adjacent_intervals (aic3p_f_ii M hM 0 c)
    (aic3p_f_ii M hM c M.vbar)
  rw [hM.2.2.2.2] at this
  linarith

lemma aic3p_ii_bdd_mul (M : Model) (hM : M.Standing) {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc 0 M.vbar, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * M.f x) volume 0 M.vbar := by
  have hf := aic3p_f_ii M hM 0 M.vbar
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM.1.le] at hf ⊢
  refine Integrable.bdd_mul (c := C) hf hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using hC x (Set.Ioc_subset_Icc_self hx)

lemma aic3p_ii_bdd_mul' (M : Model) (hM : M.Standing) {g : ℝ → ℝ} (hg : Measurable g) (a b C : ℝ)
    (hC : ∀ x, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * M.f x) volume a b := by
  have hf := aic3p_f_ii M hM a b
  rw [intervalIntegrable_iff] at hf ⊢
  exact Integrable.bdd_mul (c := C) hf hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)

lemma aic3p_t_bound (M : Model) (ε : ℝ) (m : Mech) (hm : m ∈ Mset M ε) :
    ∀ v ∈ Set.Icc 0 M.vbar, |m.t v| ≤ |m.t 0| + |ε| + M.vbar := by
  obtain ⟨⟨_, _, hx⟩, hIR, hIC⟩ := hm
  intro v hv
  have h0 : (0:ℝ) ∈ Set.Icc 0 M.vbar := ⟨le_rfl, hv.1.trans hv.2⟩
  have h1 := hIC 0 h0 v hv
  have h2 := hIR v hv
  have hx1 := hx v hv
  have : v * m.x v ≤ M.vbar := by nlinarith [hv.1, hv.2, hx1.1, hx1.2]
  rw [abs_le]; constructor
  · have := neg_abs_le (m.t 0); have := le_abs_self ε; have := abs_nonneg ε
    simp only [zero_mul, zero_sub] at h1
    linarith [hv.1, hv.2]
  · have := abs_nonneg (m.t 0); have := abs_nonneg ε; linarith

lemma tf_ii (M : Model) (hM : M.Standing) (ε : ℝ) (m : Mech) (hm : m ∈ Mset M ε) :
    IntervalIntegrable (fun v => m.t v * M.f v) volume 0 M.vbar :=
  aic3p_ii_bdd_mul M hM hm.1.2.1 _ (aic3p_t_bound M ε m hm)

lemma isIC_abs (M : Model) (m : Mech) (hm : m ∈ Mset M 0) : ICabs m.x m.t 0 M.vbar := by
  intro x hx x' hx'
  have := hm.2.2 x hx x' hx'
  linarith

lemma revenue_equivalence_core (M : Model) (hab : 0 ≤ M.vbar) (m : Mech) (hm : m ∈ Mset M 0) :
    ∀ θ ∈ Set.Icc 0 M.vbar,
      m.t θ = m.t 0 + θ * m.x θ - ∫ x in (0)..θ, m.x x := by
  intro x hx
  have := abs_payoff (isIC_abs M m hm) hab hx
  linarith

/-- threshold structure of a monotone 0/1 function -/
lemma threshold_of_mono01 {a b : ℝ} (hab : a ≤ b) (c : ℝ → ℝ) (hmono : MonotoneOn c (Set.Icc a b))
    (h01 : ∀ x ∈ Set.Icc a b, c x = 0 ∨ c x = 1) :
    ∃ p ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, x ≠ p → c x = if p < x then 1 else 0 := by
  by_cases hS : ∃ x ∈ Set.Icc a b, c x = 1
  · set S := {x | x ∈ Set.Icc a b ∧ c x = 1}
    obtain ⟨x0, hx0, hcx0⟩ := hS
    have hne : S.Nonempty := ⟨x0, hx0, hcx0⟩
    have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
    refine ⟨sInf S, ⟨le_csInf hne (fun x hx => hx.1.1), (csInf_le hbdd ⟨hx0, hcx0⟩).trans hx0.2⟩, ?_⟩
    intro x hx hxp
    split_ifs with hpx
    · obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne hpx
      have := hmono hy.1 hx hyx.le
      rcases h01 x hx with h | h
      · rw [hy.2] at this; linarith
      · exact h
    · have hxlt : x < sInf S := lt_of_le_of_ne (not_lt.1 hpx) hxp
      rcases h01 x hx with h | h
      · exact h
      · exact absurd (csInf_le hbdd ⟨hx, h⟩) (not_le.2 hxlt)
  · push Not at hS
    refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
    intro x hx hxb
    have : ¬ b < x := not_lt.2 hx.2
    rw [if_neg this]
    rcases h01 x hx with h | h
    · exact h
    · exact absurd h (hS x hx)
lemma int_thr {a p θ : ℝ} (hp : a ≤ p) (hθ : a ≤ θ) :
    ∫ x in a..θ, (if p < x then (1:ℝ) else 0) = if p < θ then θ - p else 0 := by
  split_ifs with hpθ
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := p)]
    · have h1 : ∫ x in a..p, (if p < x then (1:ℝ) else 0) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
        · simp
        intro x hx; rw [Set.uIcc_of_le hp] at hx; simp [not_lt.2 hx.2]
      have h2 : ∫ x in p..θ, (if p < x then (1:ℝ) else 0) = θ - p := by
        rw [intervalIntegral.integral_congr_ae (g := fun _ => (1:ℝ))]
        · simp
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le hpθ.le] at hx; simp [hx.1]
      rw [h1, h2]; ring
    · apply Monotone.intervalIntegrable
      intro x y hxy; dsimp only
      by_cases h1 : p < x
      · have : p < y := h1.trans_le hxy
        simp [h1, this]
      · by_cases h2 : p < y <;> simp [h1, h2]
    · apply Monotone.intervalIntegrable
      intro x y hxy; dsimp only
      by_cases h1 : p < x
      · have : p < y := h1.trans_le hxy
        simp [h1, this]
      · by_cases h2 : p < y <;> simp [h1, h2]
  · rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    intro x hx; rw [Set.uIcc_of_le hθ] at hx
    simp only
    rw [if_neg]; intro h; exact hpθ (h.trans_le hx.2)

lemma ite_meas (p v : ℝ) : Measurable (fun θ : ℝ => if p < θ then v else 0) :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

lemma thr_ii (M : Model) (hM : M.Standing) (p v : ℝ) :
    IntervalIntegrable (fun θ => (if p < θ then v else 0) * M.f θ) volume 0 M.vbar :=
  aic3p_ii_bdd_mul M hM (ite_meas p v) (|v|) (fun x _ => by split_ifs <;> simp)

lemma thr_integral (M : Model) (hM : M.Standing) {p : ℝ} (hp : p ∈ Set.Icc 0 M.vbar) :
    ∫ θ in (0)..M.vbar, (if p < θ then p else 0) * M.f θ = p * cdfBar M p := by
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun θ => (if p < θ then p else 0) * M.f θ) volume a b :=
    fun a b => aic3p_ii_bdd_mul' M hM (ite_meas p p) a b (|p|) (fun x => by split_ifs <;> simp)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := p) (hI _ _) (hI _ _)]
  have h1 : ∫ θ in (0)..p, (if p < θ then p else 0) * M.f θ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    intro x hx; rw [Set.uIcc_of_le hp.1] at hx; simp [not_lt.2 hx.2]
  have h2 : ∫ θ in p..M.vbar, (if p < θ then p else 0) * M.f θ = p * ∫ θ in p..M.vbar, M.f θ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hp.2] at hx; simp [hx.1]
  rw [h1, h2, aic3p_cdfBar_eq' M hM p, zero_add]

lemma count_floor (n : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hyn : y ≤ n) :
    (∑ k ∈ Finset.Icc 1 n, (if (k:ℝ) ≤ y then (1:ℝ) else 0)) = (⌊y⌋₊ : ℝ) := by
  rw [Finset.sum_boole]
  have hfl : ⌊y⌋₊ ≤ n := Nat.floor_le_of_le hyn
  have : (Finset.Icc 1 n).filter (fun k : ℕ => (k:ℝ) ≤ y) = Finset.Icc 1 ⌊y⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [← Nat.le_floor_iff hy0]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hfl⟩, h3⟩
  rw [this]; simp

theorem rev_bound (M : Model) (hM : M.Standing) (m' : Mech) (hm : m' ∈ Mset M 0) (G : ℝ)
    (hG : ∀ p ∈ Set.Icc 0 M.vbar, p * cdfBar M p ≤ G) (n : ℕ) (hn : 0 < n) :
    revenue M m' ≤ G + M.vbar / n := by
  have hab : (0:ℝ) ≤ M.vbar := hM.1.le
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hq : MonotoneOn m'.x (Set.Icc 0 M.vbar) := abs_mono (isIC_abs M m' hm)
  have hqmem : ∀ x ∈ Set.Icc 0 M.vbar, m'.x x ∈ Set.Icc (0:ℝ) 1 := hm.1.2.2
  set c : ℕ → ℝ → ℝ := fun k x => if (k:ℝ) ≤ n * m'.x x then 1 else 0 with hc_def
  have hc_mono : ∀ k, MonotoneOn (c k) (Set.Icc 0 M.vbar) := by
    intro k x hx y hy hxy
    simp only [hc_def]
    have := hq hx hy hxy
    by_cases h1 : (k:ℝ) ≤ n * m'.x x
    · have h2 : (k:ℝ) ≤ n * m'.x y := h1.trans (by nlinarith)
      simp [h1, h2]
    · by_cases h2 : (k:ℝ) ≤ n * m'.x y <;> simp [h1, h2]
  have hc01 : ∀ k, ∀ x ∈ Set.Icc 0 M.vbar, c k x = 0 ∨ c k x = 1 := by
    intro k x _; simp only [hc_def]; split_ifs <;> simp
  have hthr : ∀ k, ∃ p ∈ Set.Icc 0 M.vbar, ∀ x ∈ Set.Icc 0 M.vbar, x ≠ p →
      c k x = if p < x then 1 else 0 :=
    fun k => threshold_of_mono01 hab (c k) (hc_mono k) (hc01 k)
  choose P hPmem hPeq using hthr
  set K := Finset.Icc 1 n with hK
  have hcount : ∀ x ∈ Set.Icc 0 M.vbar,
      (∑ k ∈ K, c k x) ≤ n * m'.x x ∧ n * m'.x x < (∑ k ∈ K, c k x) + 1 := by
    intro x hx
    have q1 := hqmem x hx
    have hy0 : 0 ≤ (n:ℝ) * m'.x x := mul_nonneg hnR.le q1.1
    have hyn : (n:ℝ) * m'.x x ≤ n := by nlinarith [q1.2]
    have := count_floor n _ hy0 hyn
    simp only [hc_def, K]
    rw [this]
    exact ⟨Nat.floor_le hy0, Nat.lt_floor_add_one _⟩
  -- pointwise bound
  have hpt : ∀ θ ∈ Set.Icc 0 M.vbar, (∀ k ∈ K, θ ≠ P k) →
      m'.t θ ≤ (∑ k ∈ K, (if P k < θ then P k else 0)) / n + M.vbar / n := by
    intro θ hθ hne
    have hlo' : (0:ℝ) ∈ Set.Icc 0 M.vbar := ⟨le_rfl, hab⟩
    have hirl := hm.2.1 0 hlo'
    simp only [zero_mul, zero_sub] at hirl
    have hrev := revenue_equivalence_core M hab m' hm θ hθ
    have hsub : Set.uIcc 0 θ ⊆ Set.Icc 0 M.vbar := by
      rw [Set.uIcc_of_le hθ.1]; exact Set.Icc_subset_Icc le_rfl hθ.2
    have hcI : ∀ k, IntervalIntegrable (c k) volume 0 θ :=
      fun k => ((hc_mono k).mono hsub).intervalIntegrable
    have hqI : IntervalIntegrable m'.x volume 0 θ := (hq.mono hsub).intervalIntegrable
    have hsumI : IntervalIntegrable (fun x => (∑ k ∈ K, c k x) / n) volume 0 θ := by
      have := (IntervalIntegrable.sum K (fun k _ => hcI k)).div_const (n:ℝ)
      simpa only [Finset.sum_apply] using this
    have hint1 : ∫ x in (0)..θ, (∑ k ∈ K, c k x) / n ≤ ∫ x in (0)..θ, m'.x x := by
      apply intervalIntegral.integral_mono_on hθ.1 hsumI hqI
      intro x hx
      have hxI : x ∈ Set.Icc 0 M.vbar := hsub (by rw [Set.uIcc_of_le hθ.1]; exact hx)
      rw [div_le_iff₀ hnR]; linarith [(hcount x hxI).1]
    have hint2 : ∫ x in (0)..θ, (∑ k ∈ K, c k x) / n
        = (∑ k ∈ K, (if P k < θ then θ - P k else 0)) / n := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_finset_sum (fun k _ => hcI k)]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [← int_thr (hPmem k).1 hθ.1]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_ne_pt (P k)] with x hx hxI
      rw [Set.uIoc_of_le hθ.1] at hxI
      exact hPeq k x ⟨hxI.1.le, hxI.2.trans hθ.2⟩ hx
    have hA : (∑ k ∈ K, c k θ) = ∑ k ∈ K, (if P k < θ then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk; exact hPeq k θ hθ (hne k hk)
    set A := ∑ k ∈ K, (if P k < θ then (1:ℝ) else 0)
    set B := ∑ k ∈ K, (if P k < θ then θ - P k else 0)
    set C := ∑ k ∈ K, (if P k < θ then P k else 0)
    have hABC : θ * A - B = C := by
      simp only [A, B, C]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _; split_ifs <;> ring
    have hqθ : m'.x θ ≤ (A + 1) / n := by
      rw [le_div_iff₀ hnR]; have := (hcount θ hθ).2; rw [hA] at this; linarith
    have hθ0 : 0 ≤ θ := hθ.1
    have h3 : θ * m'.x θ ≤ θ * ((A + 1) / n) := mul_le_mul_of_nonneg_left hqθ hθ0
    have h4 : θ * ((A + 1) / n) - B / n = C / n + θ / n := by rw [← hABC]; ring
    have h5 : θ / n ≤ M.vbar / n := div_le_div_of_nonneg_right hθ.2 hnR.le
    rw [hint2] at hint1
    linarith
  -- integrate
  have hfI := aic3p_f_ii M hM 0 M.vbar
  have hgI : IntervalIntegrable
      (fun θ => (∑ k ∈ K, (if P k < θ then P k else 0) * M.f θ) / n + M.vbar / n * M.f θ)
      volume 0 M.vbar := by
    have h1 := (IntervalIntegrable.sum K (fun k _ => thr_ii M hM (P k) (P k))).div_const (n:ℝ)
    simp only [Finset.sum_apply] at h1
    exact h1.add (hfI.const_mul _)
  have hmono : revenue M m' ≤ ∫ θ in (0)..M.vbar,
      ((∑ k ∈ K, (if P k < θ then P k else 0) * M.f θ) / n + M.vbar / n * M.f θ) := by
    unfold revenue
    apply intervalIntegral.integral_mono_ae_restrict hab (tf_ii M hM 0 m' hm) hgI
    have hae : ∀ᵐ θ ∂(volume : Measure ℝ), ∀ k ∈ K, θ ≠ P k :=
      (Filter.eventually_all_finset K).2 (fun k _ => ae_ne_pt (P k))
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hae] with θ hθ hne
    have := mul_le_mul_of_nonneg_right (hpt θ hθ hne) (hM.2.1 θ)
    calc m'.t θ * M.f θ ≤ _ := this
      _ = _ := by rw [add_mul, div_mul_eq_mul_div, Finset.sum_mul]
  have hval : ∫ θ in (0)..M.vbar,
      ((∑ k ∈ K, (if P k < θ then P k else 0) * M.f θ) / n + M.vbar / n * M.f θ)
      = (∑ k ∈ K, P k * cdfBar M (P k)) / n + M.vbar / n := by
    rw [intervalIntegral.integral_add
      (by have h1 := (IntervalIntegrable.sum K (fun k _ => thr_ii M hM (P k) (P k))).div_const (n:ℝ)
          simpa only [Finset.sum_apply] using h1)
      (hfI.const_mul _)]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_finset_sum
      (fun k _ => thr_ii M hM (P k) (P k)), intervalIntegral.integral_const_mul, hM.2.2.2.2]
    congr 1
    · congr 1; apply Finset.sum_congr rfl; intro k _; exact thr_integral M hM (hPmem k)
    · ring
  have hsumG : (∑ k ∈ K, P k * cdfBar M (P k)) ≤ n * G := by
    have := Finset.sum_le_sum (fun k (_ : k ∈ K) => hG (P k) (hPmem k))
    simpa [K] using this
  have : (∑ k ∈ K, P k * cdfBar M (P k)) / n ≤ G := by
    rw [div_le_iff₀ hnR]; linarith
  linarith

lemma postedPrice_mem (M : Model) (p : ℝ) (hp : 0 ≤ p) : postedPrice p ∈ Mset M 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show Measurable (fun v : ℝ => if p ≤ v then (1:ℝ) else 0)
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  · show Measurable (fun v : ℝ => if v < p then (0:ℝ) else if v < p then v else p)
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iio measurable_id measurable_const)
  · intro v _
    show (if p ≤ v then (1:ℝ) else 0) ∈ Set.Icc (0:ℝ) 1
    split_ifs <;> simp
  · intro v hv
    show 0 ≤ v * (if p ≤ v then (1:ℝ) else 0) - (if v < p then (0:ℝ) else if v < p then v else p)
    split_ifs <;> nlinarith
  · intro v hv v' hv'
    show v * (if p ≤ v' then (1:ℝ) else 0) - (if v' < p then (0:ℝ) else if v' < p then v' else p) - 0
      ≤ v * (if p ≤ v then (1:ℝ) else 0) - (if v < p then (0:ℝ) else if v < p then v else p)
    split_ifs <;> nlinarith

lemma postedPrice_revenue (M : Model) (hM : M.Standing) (p : ℝ) (hp : p ∈ Set.Icc 0 M.vbar) :
    revenue M (postedPrice p) = R M p := by
  unfold revenue R
  rw [← thr_integral M hM hp]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_ne_pt p] with x hx _
  show (if x < p then (0:ℝ) else if x < p then x else p) * M.f x = (if p < x then p else 0) * M.f x
  rcases lt_or_gt_of_ne hx with h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, not_lt.2 h.le]

theorem aic3_posted_price_optimal (M : Model) (hM : M.Standing) (p : ℝ)
    (hp : p ∈ Set.Icc 0 M.vbar) (hmax : IsMaxOn (R M) (Set.Icc 0 M.vbar) p) :
    postedPrice p ∈ Mset M 0 ∧ revenue M (postedPrice p) = R M p ∧
      IsGreatest (revenue M '' Mset M 0) (R M p) ∧ optRev M 0 = R M p := by
  have hmem := postedPrice_mem M p hp.1
  have hrev := postedPrice_revenue M hM p hp
  have hG : IsGreatest (revenue M '' Mset M 0) (R M p) := by
    refine ⟨⟨_, hmem, hrev⟩, ?_⟩
    rintro _ ⟨m', hm', rfl⟩
    have hG' : ∀ q ∈ Set.Icc 0 M.vbar, q * cdfBar M q ≤ R M p := fun q hq => hmax hq
    by_contra hcon
    push Not at hcon
    set δ := revenue M m' - R M p
    have hδ : 0 < δ := by simp only [δ]; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (M.vbar / δ)
    have hnpos : (0:ℝ) < n := lt_trans (div_pos hM.1 hδ) hn
    have hb := rev_bound M hM m' hm' _ hG' n (by exact_mod_cast hnpos)
    have : M.vbar / n < δ := by
      rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hδ] at hn; linarith
    simp only [δ] at this
    linarith
  exact ⟨hmem, hrev, hG, hG.csSup_eq⟩

end ApproxIC.Deterministic

open ApproxIC.Deterministic

theorem solution (M : Model) (hM : M.Standing) (p : ℝ)
    (hp : p ∈ Set.Icc 0 M.vbar) (hmax : IsMaxOn (R M) (Set.Icc 0 M.vbar) p) :
    postedPrice p ∈ Mset M 0 ∧ revenue M (postedPrice p) = R M p ∧
      IsGreatest (revenue M '' Mset M 0) (R M p) ∧ optRev M 0 = R M p :=
  aic3_posted_price_optimal M hM p hp hmax
