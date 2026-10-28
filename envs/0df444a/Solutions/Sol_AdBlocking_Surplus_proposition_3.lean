-- Prove2me | solution 1 for AdBlocking.Surplus.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T04:13:21.751639+00:00
-- url     : https://prove2.me/submissions/4d83285a-d598-42ad-a500-e8fba2fb4009

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

set_option autoImplicit false

open MeasureTheory

namespace AdBlocking.Surplus.F55

/-- Integral against the uniform law on `[0, κbar]` as a normalised set integral. -/
lemma integral_unif0 (κbar : ℝ) (hk : 0 < κbar) (f : ℝ → ℝ) :
    ∫ κ, f κ ∂(unifIcc 0 κbar) = (∫ κ in Set.Icc 0 κbar, f κ) / κbar := by
  have h : unifIcc 0 κbar = (ENNReal.ofReal (κbar - 0))⁻¹ • volume.restrict (Set.Icc 0 κbar) := by
    simp [unifIcc, hk]
  rw [h, integral_smul_measure, sub_zero, ENNReal.toReal_inv, ENNReal.toReal_ofReal hk.le,
    smul_eq_mul]
  ring

/-- Download probability: `P(κ < g) = g⁺ / κbar` when `g ≤ κbar`. -/
lemma integral_unif0_ind (κbar g : ℝ) (hk : 0 < κbar) (hg : g ≤ κbar) :
    ∫ κ, (if κ < g then (1 : ℝ) else 0) ∂(unifIcc 0 κbar) = max g 0 / κbar := by
  rw [integral_unif0 κbar hk]
  congr 1
  have hfun : (fun κ : ℝ => if κ < g then (1 : ℝ) else 0) = (Set.Iio g).indicator 1 := by
    funext κ
    simp [Set.indicator_apply, Set.mem_Iio]
  rw [hfun, integral_indicator_one measurableSet_Iio, Measure.real,
    Measure.restrict_apply measurableSet_Iio]
  rcases le_or_gt g 0 with h0 | h0
  · have : Set.Iio g ∩ Set.Icc 0 κbar = ∅ := by
      ext κ
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2
      intro _
      linarith
    rw [this, measure_empty, ENNReal.toReal_zero, max_eq_right h0]
  · have : Set.Iio g ∩ Set.Icc 0 κbar = Set.Ico 0 g := by
      ext κ
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal h0.le, max_eq_left h0.le]

/-- Expected excess `E (g - κ)⁺ = (g⁺)² / (2 κbar)` when `g ≤ κbar`. -/
lemma integral_unif0_excess (κbar g : ℝ) (hk : 0 < κbar) (hg : g ≤ κbar) :
    ∫ κ, max (g - κ) 0 ∂(unifIcc 0 κbar) = (max g 0) ^ 2 / (2 * κbar) := by
  rw [integral_unif0 κbar hk, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hk.le]
  have hc : Continuous fun κ : ℝ => max (g - κ) 0 := by fun_prop
  rcases le_or_gt g 0 with h0 | h0
  · have : ∫ κ in (0 : ℝ)..κbar, max (g - κ) 0 = ∫ κ in (0 : ℝ)..κbar, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro κ hκ
      rw [Set.uIcc_of_le hk.le] at hκ
      simp only
      exact max_eq_right (by linarith [hκ.1])
    rw [this, intervalIntegral.integral_zero, max_eq_right h0]
    simp
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := g)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have e1 : ∫ κ in (0 : ℝ)..g, max (g - κ) 0 = ∫ κ in (0 : ℝ)..g, (g - κ) := by
      apply intervalIntegral.integral_congr
      intro κ hκ
      rw [Set.uIcc_of_le h0.le] at hκ
      simp only
      exact max_eq_left (by linarith [hκ.2])
    have e2 : ∫ κ in g..κbar, max (g - κ) 0 = ∫ κ in g..κbar, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro κ hκ
      rw [Set.uIcc_of_le hg] at hκ
      simp only
      exact max_eq_right (by linarith [hκ.1])
    rw [e1, e2, intervalIntegral.integral_zero, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id, integral_id,
      intervalIntegral.integral_const, max_eq_left h0.le]
    field_simp
    ring

/-- Pointwise split of the adblock-regime surplus. -/
lemma max_split (x y κ : ℝ) :
    max (max x (y - κ)) 0 = max x 0 + max ((y - max x 0) - κ) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- Survival: `P(g ≤ κ) = 1 - g⁺ / κbar` when `g ≤ κbar`. -/
lemma integral_unif0_ind_ge (κbar g : ℝ) (hk : 0 < κbar) (hg : g ≤ κbar) :
    ∫ κ, (if κ < g then (0 : ℝ) else 1) ∂(unifIcc 0 κbar) = 1 - max g 0 / κbar := by
  rw [integral_unif0 κbar hk]
  have hfun : (fun κ : ℝ => if κ < g then (0 : ℝ) else 1) = (Set.Ici g).indicator 1 := by
    funext κ
    by_cases h : κ < g
    · simp [Set.indicator_apply, Set.mem_Ici, h, not_le.mpr h]
    · simp [Set.indicator_apply, Set.mem_Ici, h, not_lt.mp h]
  rw [hfun, integral_indicator_one measurableSet_Ici, Measure.real,
    Measure.restrict_apply measurableSet_Ici]
  have : Set.Ici g ∩ Set.Icc 0 κbar = Set.Icc (max g 0) κbar := by
    ext κ
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, max_le_iff]
    tauto
  have hm : max g 0 ≤ κbar := max_le hg hk.le
  rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  field_simp

/-- Integrals against `unifIcc a b` only see values on `[a, b]`. -/
lemma integral_unifIcc_congr {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc a b, f x = g x) :
    ∫ x, f x ∂(unifIcc a b) = ∫ x, g x ∂(unifIcc a b) := by
  unfold unifIcc
  split_ifs with hlt
  · rw [integral_smul_measure, integral_smul_measure,
      setIntegral_congr_fun measurableSet_Icc h]
  · rw [integral_dirac, integral_dirac]
    exact h b ⟨hab, le_rfl⟩

/-- Download mass for a large support `κbar ≥ q`. -/
lemma dlMass_eq (r t κbar q A V : ℝ) (hr1 : r ≤ 1) (ht1 : t ≤ 1) (hk : 0 < κbar)
    (hq : 0 ≤ q) (hqk : q ≤ κbar) (hV : 0 ≤ V) (hr : 0 ≤ r) :
    dlMass r t κbar q A V =
      E2 r t (fun θ γ => max (θ * q - γ * V - max (θ * q - γ * A) 0) 0 / κbar) := by
  unfold dlMass E3 E2
  apply integral_unifIcc_congr ht1
  intro θ hθ
  apply integral_unifIcc_congr hr1
  intro γ hγ
  have hg : θ * q - γ * V - max (θ * q - γ * A) 0 ≤ κbar := by
    have h1 : θ * q ≤ q := by nlinarith [hθ.2]
    have h2 : 0 ≤ γ * V := mul_nonneg (le_trans hr hγ.1) hV
    have h3 : 0 ≤ max (θ * q - γ * A) 0 := le_max_right _ _
    linarith
  beta_reduce
  rw [← integral_unif0_ind κbar _ hk hg]
  apply integral_unifIcc_congr hk.le
  intro κ _
  unfold downloads
  by_cases h : κ < θ * q - γ * V - max (θ * q - γ * A) 0
  · rw [if_pos (by linarith), if_pos h]
  · rw [if_neg (by intro h'; exact h (by linarith)), if_neg h]

/-- Consumer surplus in the adblock regime for a large support `κbar ≥ q`. -/
lemma csAB_eq (r t κbar q A V : ℝ) (hr1 : r ≤ 1) (ht1 : t ≤ 1) (hk : 0 < κbar)
    (hq : 0 ≤ q) (hqk : q ≤ κbar) (hV : 0 ≤ V) (hr : 0 ≤ r) :
    csAB r t κbar q A V =
      E2 r t (fun θ γ => max (θ * q - γ * A) 0 +
        (max (θ * q - γ * V - max (θ * q - γ * A) 0) 0) ^ 2 / (2 * κbar)) := by
  unfold csAB E3 E2
  apply integral_unifIcc_congr ht1
  intro θ hθ
  apply integral_unifIcc_congr hr1
  intro γ hγ
  have hg : θ * q - γ * V - max (θ * q - γ * A) 0 ≤ κbar := by
    have h1 : θ * q ≤ q := by nlinarith [hθ.2]
    have h2 : 0 ≤ γ * V := mul_nonneg (le_trans hr hγ.1) hV
    have h3 : 0 ≤ max (θ * q - γ * A) 0 := le_max_right _ _
    linarith
  beta_reduce
  simp_rw [max_split (θ * q - γ * A) (θ * q - γ * V)]
  have hint : Integrable (fun κ : ℝ => max (θ * q - γ * V - max (θ * q - γ * A) 0 - κ) 0)
      (unifIcc 0 κbar) := by
    have h : unifIcc 0 κbar = (ENNReal.ofReal (κbar - 0))⁻¹ • volume.restrict (Set.Icc 0 κbar) := by
      simp [unifIcc, hk]
    rw [h]
    apply Integrable.smul_measure _ (by simp [hk])
    exact (Continuous.integrableOn_Icc (by fun_prop))
  have : IsProbabilityMeasure (unifIcc 0 κbar) := by
    constructor
    simp only [unifIcc, hk, if_true, sub_zero, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Icc, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [hk]) ENNReal.ofReal_ne_top
  rw [integral_add (integrable_const _) hint, integral_const, integral_unif0_excess κbar _ hk hg]
  simp

/-- Publisher profit in the adblock regime for a large support `κbar ≥ q`. -/
lemma pubProfitAB_eq (pa c r t κbar q A V : ℝ) (hr1 : r ≤ 1) (ht1 : t ≤ 1) (hk : 0 < κbar)
    (hq : 0 ≤ q) (hqk : q ≤ κbar) (hV : 0 ≤ V) (hr : 0 ≤ r) :
    pubProfitAB pa c r t κbar q A V =
      pa * A * E2 r t (fun θ γ => by
        classical
        exact if visits q A θ γ then
          1 - max (θ * q - γ * V - max (θ * q - γ * A) 0) 0 / κbar else 0) - c * q ^ 2 := by
  unfold pubProfitAB E3 E2
  congr 2
  apply integral_unifIcc_congr ht1
  intro θ hθ
  apply integral_unifIcc_congr hr1
  intro γ hγ
  beta_reduce
  have hg : θ * q - γ * V - max (θ * q - γ * A) 0 ≤ κbar := by
    have h1 : θ * q ≤ q := by nlinarith [hθ.2]
    have h2 : 0 ≤ γ * V := mul_nonneg (le_trans hr hγ.1) hV
    have h3 : 0 ≤ max (θ * q - γ * A) 0 := le_max_right _ _
    linarith
  by_cases hv : visits q A θ γ
  · rw [if_pos hv, ← integral_unif0_ind_ge κbar _ hk hg]
    apply integral_unifIcc_congr hk.le
    intro κ _
    unfold downloads
    by_cases h : κ < θ * q - γ * V - max (θ * q - γ * A) 0
    · rw [if_neg (by intro h'; exact h'.2 (by linarith)), if_pos h]
    · rw [if_pos ⟨hv, by intro h'; exact h (by linarith)⟩, if_neg h]
  · rw [if_neg hv]
    calc _ = ∫ _κ, (0 : ℝ) ∂(unifIcc 0 κbar) := by
          congr 1
          funext κ
          exact if_neg (fun h' => hv h'.1)
      _ = 0 := integral_zero _ _


/-! ## Part 2: integration infrastructure and homogeneity (session 2) -/

lemma unif_prob {a b : ℝ} (hab : a ≤ b) : IsProbabilityMeasure (unifIcc a b) := by
  unfold unifIcc
  split_ifs with h
  · constructor
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr h)).ne'
      ENNReal.ofReal_ne_top
  · infer_instance

lemma unif_ae {a b : ℝ} (hab : a ≤ b) : ∀ᵐ x ∂(unifIcc a b), x ∈ Set.Icc a b := by
  unfold unifIcc
  split_ifs with h
  · exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  · exact (ae_dirac_iff measurableSet_Icc).2 ⟨hab, le_rfl⟩

/-- Integrands that are jointly measurable and bounded on the parameter box. -/
def Nice (r t : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry f) ∧ ∃ C, ∀ θ ∈ Set.Icc t 1, ∀ γ ∈ Set.Icc r 1, |f θ γ| ≤ C

lemma nice_inner {r t : ℝ} (hr : r ≤ 1) {f : ℝ → ℝ → ℝ} (hf : Nice r t f) (θ : ℝ)
    (hθ : θ ∈ Set.Icc t 1) : Integrable (f θ) (unifIcc r 1) := by
  have := unif_prob hr
  obtain ⟨hm, C, hC⟩ := hf
  have hm' : Measurable (f θ) := hm.comp (measurable_const.prodMk measurable_id)
  exact Integrable.of_bound hm'.aestronglyMeasurable C
    ((unif_ae hr).mono fun γ hγ => by rw [Real.norm_eq_abs]; exact hC θ hθ γ hγ)

lemma nice_outer {r t : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) {f : ℝ → ℝ → ℝ} (hf : Nice r t f) :
    Integrable (fun θ => ∫ γ, f θ γ ∂(unifIcc r 1)) (unifIcc t 1) := by
  have := unif_prob hr
  have := unif_prob ht
  obtain ⟨hm, C, hC⟩ := hf
  have hs : StronglyMeasurable fun θ => ∫ γ, f θ γ ∂(unifIcc r 1) :=
    hm.stronglyMeasurable.integral_prod_right
  refine Integrable.of_bound hs.aestronglyMeasurable C ((unif_ae ht).mono fun θ hθ => ?_)
  have := norm_integral_le_of_norm_le_const (μ := unifIcc r 1) (f := f θ) (C := C)
    ((unif_ae hr).mono fun γ hγ => by rw [Real.norm_eq_abs]; exact hC θ hθ γ hγ)
  simpa [probReal_univ] using this

lemma E2_add {r t : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) {f g : ℝ → ℝ → ℝ} (hf : Nice r t f)
    (hg : Nice r t g) : E2 r t (fun θ γ => f θ γ + g θ γ) = E2 r t f + E2 r t g := by
  unfold E2
  rw [← integral_add (nice_outer hr ht hf) (nice_outer hr ht hg)]
  apply integral_unifIcc_congr ht
  intro θ hθ
  exact integral_add (nice_inner hr hf θ hθ) (nice_inner hr hg θ hθ)

lemma E2_sub {r t : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) {f g : ℝ → ℝ → ℝ} (hf : Nice r t f)
    (hg : Nice r t g) : E2 r t (fun θ γ => f θ γ - g θ γ) = E2 r t f - E2 r t g := by
  unfold E2
  rw [← integral_sub (nice_outer hr ht hf) (nice_outer hr ht hg)]
  apply integral_unifIcc_congr ht
  intro θ hθ
  exact integral_sub (nice_inner hr hf θ hθ) (nice_inner hr hg θ hθ)

lemma E2_mul (r t k : ℝ) (f : ℝ → ℝ → ℝ) :
    E2 r t (fun θ γ => k * f θ γ) = k * E2 r t f := by
  unfold E2
  simp_rw [integral_const_mul]

lemma E2_div (r t k : ℝ) (f : ℝ → ℝ → ℝ) :
    E2 r t (fun θ γ => f θ γ / k) = E2 r t f / k := by
  unfold E2
  simp_rw [integral_div]

lemma E2_congr {r t : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) {f g : ℝ → ℝ → ℝ}
    (h : ∀ θ ∈ Set.Icc t 1, ∀ γ ∈ Set.Icc r 1, f θ γ = g θ γ) : E2 r t f = E2 r t g := by
  unfold E2
  apply integral_unifIcc_congr ht
  intro θ hθ
  exact integral_unifIcc_congr hr (h θ hθ)

lemma E2_nonneg {r t : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) {f : ℝ → ℝ → ℝ}
    (h : ∀ θ ∈ Set.Icc t 1, ∀ γ ∈ Set.Icc r 1, 0 ≤ f θ γ) : 0 ≤ E2 r t f := by
  unfold E2
  apply integral_nonneg_of_ae
  refine (unif_ae ht).mono fun θ hθ => ?_
  exact integral_nonneg_of_ae ((unif_ae hr).mono fun γ hγ => h θ hθ γ hγ)

/-- Integral of a `[0,1]`-valued function against a probability measure lies in `[0,1]`. -/
lemma int_unit {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ → ℝ}
    (h0 : ∀ x, 0 ≤ h x) (h1 : ∀ x, h x ≤ 1) : 0 ≤ ∫ x, h x ∂μ ∧ ∫ x, h x ∂μ ≤ 1 := by
  refine ⟨integral_nonneg h0, ?_⟩
  have := integral_mono_of_nonneg (μ := μ) (f := h) (g := fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall h0) (integrable_const 1) (Filter.Eventually.of_forall h1)
  simpa using this

lemma E2_unit {r t : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) {f : ℝ → ℝ → ℝ}
    (h0 : ∀ θ γ, 0 ≤ f θ γ) (h1 : ∀ θ γ, f θ γ ≤ 1) : 0 ≤ E2 r t f ∧ E2 r t f ≤ 1 := by
  have := unif_prob hr
  have := unif_prob ht
  unfold E2
  exact int_unit (fun θ => (int_unit (h0 θ) (h1 θ)).1) (fun θ => (int_unit (h0 θ) (h1 θ)).2)

lemma E3_unit {r t κbar : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) (hk : 0 ≤ κbar)
    {f : ℝ → ℝ → ℝ → ℝ} (h0 : ∀ θ γ κ, 0 ≤ f θ γ κ) (h1 : ∀ θ γ κ, f θ γ κ ≤ 1) :
    0 ≤ E3 r t κbar f ∧ E3 r t κbar f ≤ 1 := by
  have := unif_prob hr
  have := unif_prob ht
  have := unif_prob hk
  unfold E3
  have l2 : ∀ θ, 0 ≤ ∫ γ, ∫ κ, f θ γ κ ∂(unifIcc 0 κbar) ∂(unifIcc r 1) ∧
      ∫ γ, ∫ κ, f θ γ κ ∂(unifIcc 0 κbar) ∂(unifIcc r 1) ≤ 1 := fun θ =>
    int_unit (fun γ => (int_unit (h0 θ γ) (h1 θ γ)).1) (fun γ => (int_unit (h0 θ γ) (h1 θ γ)).2)
  exact int_unit (fun θ => (l2 θ).1) (fun θ => (l2 θ).2)

/-! ### Homogeneity in the quality level `q` -/

lemma mul_pos_max {q : ℝ} (hq : 0 < q) (x : ℝ) : max (q * x) 0 = q * max x 0 := by
  rw [mul_max_of_nonneg _ _ hq.le, mul_zero]

lemma lin_hom {q : ℝ} (hq : 0 < q) (θ γ A : ℝ) : θ * q - γ * A = q * (θ - γ * (A / q)) := by
  field_simp <;> ring

lemma gp_hom {q : ℝ} (hq : 0 < q) (θ γ A V : ℝ) :
    max (θ * q - γ * V - max (θ * q - γ * A) 0) 0 =
      q * max (θ - γ * (V / q) - max (θ - γ * (A / q)) 0) 0 := by
  rw [lin_hom hq θ γ A, mul_pos_max hq,
    show θ * q - γ * V - q * max (θ - γ * (A / q)) 0 =
      q * (θ - γ * (V / q) - max (θ - γ * (A / q)) 0) by field_simp <;> ring,
    mul_pos_max hq]

lemma visits_hom {q : ℝ} (hq : 0 < q) (θ γ A : ℝ) :
    visits q A θ γ ↔ 0 ≤ θ - γ * (A / q) := by
  unfold visits
  rw [lin_hom hq θ γ A]
  constructor
  · intro h
    exact nonneg_of_mul_nonneg_right (by linarith) hq
  · intro h
    exact mul_nonneg hq.le h

lemma demand_hom {q : ℝ} (hq : 0 < q) (r t A : ℝ) :
    demand r t q A = E2 r t (fun θ γ => if 0 ≤ θ - γ * (A / q) then 1 else 0) := by
  unfold demand
  congr 1
  funext θ γ
  by_cases h : 0 ≤ θ - γ * (A / q)
  · rw [if_pos ((visits_hom hq θ γ A).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((visits_hom hq θ γ A).1 h')), if_neg h]

lemma demand_one (r t a : ℝ) :
    demand r t 1 a = E2 r t (fun θ γ => if 0 ≤ θ - γ * a then 1 else 0) := by
  rw [demand_hom one_pos]
  simp

lemma csNA_hom {q : ℝ} (hq : 0 < q) (r t A : ℝ) :
    csNA r t q A = q * E2 r t (fun θ γ => max (θ - γ * (A / q)) 0) := by
  unfold csNA
  rw [← E2_mul]
  congr 1
  funext θ γ
  rw [lin_hom hq θ γ A, mul_pos_max hq]

lemma csNA_one (r t a : ℝ) : csNA r t 1 a = E2 r t (fun θ γ => max (θ - γ * a) 0) := by
  rw [csNA_hom one_pos]
  simp

/-! ## Part 3: the reduction glue (session 2) -/

/-- Adblocker gain at normalised quality `q = 1`. -/
noncomputable def Gf (r t a w : ℝ) : ℝ :=
  E2 r t (fun θ γ => max (θ - γ * w - max (θ - γ * a) 0) 0)

/-- Mass-weighted gain on the visiting set (`β`). -/
noncomputable def Bf (r t a v : ℝ) : ℝ :=
  E2 r t (fun θ γ => if 0 ≤ θ - γ * a then max (θ - γ * v - max (θ - γ * a) 0) 0 else 0)

/-- Second moment of the gain (`H`). -/
noncomputable def Hf (r t a v : ℝ) : ℝ :=
  E2 r t (fun θ γ => (max (θ - γ * v - max (θ - γ * a) 0) 0) ^ 2)

lemma nice_of {r t C : ℝ} {f : ℝ → ℝ → ℝ} (hm : Measurable (Function.uncurry f))
    (h0 : ∀ θ ∈ Set.Icc t 1, ∀ γ ∈ Set.Icc r 1, 0 ≤ f θ γ)
    (h1 : ∀ θ ∈ Set.Icc t 1, ∀ γ ∈ Set.Icc r 1, f θ γ ≤ C) : Nice r t f :=
  ⟨hm, C, fun θ hθ γ hγ => by rw [abs_of_nonneg (h0 θ hθ γ hγ)]; exact h1 θ hθ γ hγ⟩

lemma meas_of_cont {f : ℝ → ℝ → ℝ} (h : Continuous fun p : ℝ × ℝ => f p.1 p.2) :
    Measurable (Function.uncurry f) := h.measurable

lemma meas_ind_mul (a : ℝ) {g : ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
    Measurable (Function.uncurry fun θ γ => if 0 ≤ θ - γ * a then g θ γ else 0) := by
  show Measurable fun p : ℝ × ℝ => if 0 ≤ p.1 - p.2 * a then g p.1 p.2 else 0
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) hg.measurable
    measurable_const

lemma gp1_le {θ γ a v : ℝ} (hθ1 : θ ≤ 1) (hγ : 0 ≤ γ) (hv : 0 ≤ v) :
    max (θ - γ * v - max (θ - γ * a) 0) 0 ≤ 1 :=
  max_le (by nlinarith [le_max_right (θ - γ * a) 0, mul_nonneg hγ hv]) zero_le_one

lemma lin_hom' (q θ γ a : ℝ) : θ * q - γ * (a * q) = q * (θ - γ * a) := by ring

lemma gp_hom' {q : ℝ} (hq : 0 < q) (θ γ a v : ℝ) :
    max (θ * q - γ * (v * q) - max (θ * q - γ * (a * q)) 0) 0 =
      q * max (θ - γ * v - max (θ - γ * a) 0) 0 := by
  rw [lin_hom' q θ γ a, mul_pos_max hq,
    show θ * q - γ * (v * q) - q * max (θ - γ * a) 0 = q * (θ - γ * v - max (θ - γ * a) 0) by ring,
    mul_pos_max hq]

lemma visits_hom' {q : ℝ} (hq : 0 < q) (θ γ a : ℝ) : visits q (a * q) θ γ ↔ 0 ≤ θ - γ * a := by
  rw [visits_hom hq, show a * q / q = a by field_simp]

lemma benchRev_hom {pa r t q : ℝ} (hq : 0 < q) (B : ℝ) :
    benchRev pa r t q B = pa * q * (B / q * demand r t 1 (B / q)) := by
  unfold benchRev
  rw [demand_hom hq, demand_one]
  have key : ∀ E : ℝ, pa * B * E = pa * q * (B / q * E) := fun E => by field_simp
  exact key _

lemma asel_eq {pa c r t a : ℝ} (hs : Standing pa c r t) (ha0 : 0 < a)
    (hau : ∀ b, 0 ≤ b → b ≠ a → b * demand r t 1 b < a * demand r t 1 a)
    {Asel : ℝ → ℝ} (hbest : ∀ q, 0 ≤ q → IsBenchAdBest pa r t q (Asel q))
    {q : ℝ} (hq : 0 < q) : Asel q = a * q := by
  obtain ⟨hA0, hmax⟩ := hbest q hq.le
  by_contra hne
  have hb : Asel q / q ≠ a := fun h => hne (by rw [← h]; field_simp)
  have h1 := hau (Asel q / q) (div_nonneg hA0 hq.le) hb
  have h2 := hmax (a * q) (mul_nonneg ha0.le hq.le)
  rw [benchRev_hom hq, benchRev_hom hq, show a * q / q = a by field_simp] at h2
  have h3 := mul_lt_mul_of_pos_left h1 (mul_pos hs.1 hq)
  linarith

lemma demand_zero_q {r t A : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht1 : t ≤ 1) (hA : 0 < A) :
    demand r t 0 A = 0 := by
  unfold demand
  rw [E2_congr hr1 ht1 (g := fun _ _ => 0)]
  · unfold E2
    simp
  · intro θ _ γ hγ
    rw [if_neg]
    intro h
    unfold visits at h
    nlinarith [mul_pos (lt_of_lt_of_le hr0 hγ.1) hA]


lemma benchProfit_eq {pa c r t a : ℝ} (hs : Standing pa c r t) (ha0 : 0 < a)
    (hau : ∀ b, 0 ≤ b → b ≠ a → b * demand r t 1 b < a * demand r t 1 a)
    {Asel : ℝ → ℝ} (hbest : ∀ q, 0 ≤ q → IsBenchAdBest pa r t q (Asel q))
    {q : ℝ} (hq : 0 ≤ q) :
    benchProfit pa c r t Asel q = pa * a * demand r t 1 a * q - c * q ^ 2 := by
  unfold benchProfit
  rcases hq.lt_or_eq with hq | hq
  · rw [asel_eq hs ha0 hau hbest hq, benchRev_hom hq, show a * q / q = a by field_simp]
    ring
  · subst hq
    obtain ⟨hA0, -⟩ := hbest 0 le_rfl
    unfold benchRev
    rcases hA0.lt_or_eq with hA | hA
    · rw [demand_zero_q hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2 hA]
      ring
    · rw [← hA]
      ring

lemma quad_peak {α c q0 : ℝ} (hc : 0 < c)
    (h : α * (α / (2 * c)) - c * (α / (2 * c)) ^ 2 ≤ α * q0 - c * q0 ^ 2) :
    q0 = α / (2 * c) := by
  set x := α / (2 * c) with hx
  have hα : α = 2 * c * x := by rw [hx]; field_simp
  rw [hα] at h
  have h2 : c * (q0 - x) ^ 2 ≤ 0 := by nlinarith
  have h3 : (q0 - x) ^ 2 ≤ 0 := by
    by_contra hh
    push_neg at hh
    nlinarith [mul_pos hc hh]
  have h4 : q0 - x = 0 := by
    apply (pow_eq_zero_iff two_ne_zero).mp
    linarith [sq_nonneg (q0 - x)]
  linarith

lemma payoff_hom {pa r t κbar q a W : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht1 : t ≤ 1)
    (hk : 0 < κbar) (hq : 0 < q) (hqk : q ≤ κbar) (hW : 0 ≤ W) :
    adblockerPayoff pa r t κbar q (a * q) W = pa * q ^ 2 / κbar * (W / q * Gf r t a (W / q)) := by
  unfold adblockerPayoff
  rw [dlMass_eq r t κbar q (a * q) W hr1 ht1 hk hq.le hqk hW hr0.le, E2_div]
  have : E2 r t (fun θ γ => max (θ * q - γ * W - max (θ * q - γ * (a * q)) 0) 0) =
      q * Gf r t a (W / q) := by
    unfold Gf
    rw [← E2_mul]
    congr 1
    funext θ γ
    rw [gp_hom hq, show a * q / q = a by field_simp]
  rw [this]
  field_simp

lemma vsel_eq {pa r t κbar a v : ℝ} (hpa : 0 < pa) (hr0 : 0 < r) (hr1 : r ≤ 1) (ht1 : t ≤ 1)
    (hk : 0 < κbar) (hv0 : 0 ≤ v)
    (hvu : ∀ w, 0 ≤ w → w ≠ v → w * Gf r t a w < v * Gf r t a v)
    {q : ℝ} (hq : 0 < q) (hqk : q ≤ κbar) {Vq : ℝ}
    (hbest : IsAdblockBest pa r t κbar q (a * q) Vq) : Vq = v * q := by
  obtain ⟨hV0, hmax⟩ := hbest
  by_contra hne
  have hb : Vq / q ≠ v := fun h => hne (by rw [← h]; field_simp)
  have h1 := hvu (Vq / q) (div_nonneg hV0 hq.le) hb
  have h2 := hmax (v * q) (mul_nonneg hv0 hq.le)
  rw [payoff_hom hr0 hr1 ht1 hk hq hqk (mul_nonneg hv0 hq.le), payoff_hom hr0 hr1 ht1 hk hq hqk hV0,
    show v * q / q = v by field_simp] at h2
  have h3 := mul_lt_mul_of_pos_left h1 (show 0 < pa * q ^ 2 / κbar by positivity)
  linarith

lemma pub_eq {pa c r t κbar q a v : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hk : 0 < κbar) (hq : 0 < q) (hqk : q ≤ κbar) (hv0 : 0 ≤ v) :
    pubProfitAB pa c r t κbar q (a * q) (v * q) =
      pa * a * demand r t 1 a * q - (c + pa * a * Bf r t a v / κbar) * q ^ 2 := by
  rw [pubProfitAB_eq pa c r t κbar q (a * q) (v * q) hr1 ht1 hk hq.le hqk
    (mul_nonneg hv0 hq.le) hr0.le]
  rw [E2_congr hr1 ht1 (g := fun θ γ => (if 0 ≤ θ - γ * a then (1 : ℝ) else 0) -
      q * (if 0 ≤ θ - γ * a then max (θ - γ * v - max (θ - γ * a) 0) 0 else 0) / κbar) ?_]
  · rw [E2_sub hr1 ht1 ?n1 ?n2, E2_div, E2_mul, ← demand_one]
    · unfold Bf
      ring
    · exact nice_of (C := 1) (meas_ind_mul a (g := fun _ _ => 1) (by fun_prop))
        (fun θ _ γ _ => by split_ifs <;> norm_num) (fun θ _ γ _ => by split_ifs <;> norm_num)
    · refine nice_of (C := q / κbar) ?_ (fun θ _ γ _ => ?_) (fun θ hθ γ hγ => ?_)
      · show Measurable fun p : ℝ × ℝ => q * (if 0 ≤ p.1 - p.2 * a then
          max (p.1 - p.2 * v - max (p.1 - p.2 * a) 0) 0 else 0) / κbar
        exact ((meas_ind_mul a (g := fun θ γ => max (θ - γ * v - max (θ - γ * a) 0) 0)
          (by fun_prop)).const_mul q).div_const κbar
      · split_ifs
        · positivity
        · simp
      · have hg := gp1_le (θ := θ) (γ := γ) (a := a) (v := v) hθ.2 (by linarith [hγ.1]) hv0
        have key : ∀ X : ℝ, X ≤ 1 → q * X / κbar ≤ q / κbar := fun X hX => by
          rw [div_le_div_iff_of_pos_right hk]
          nlinarith
        split_ifs
        · exact key _ hg
        · exact key 0 zero_le_one
  · intro θ _ γ _
    by_cases h : 0 ≤ θ - γ * a
    · rw [if_pos ((visits_hom' hq θ γ a).2 h), if_pos h, if_pos h, gp_hom' hq]
      try ring
    · rw [if_neg (fun h' => h ((visits_hom' hq θ γ a).1 h')), if_neg h, if_neg h]
      try ring

lemma pub_le {pa c r t κbar q A V : ℝ} (hpa : 0 < pa) (hr1 : r ≤ 1) (ht1 : t ≤ 1)
    (hk : 0 < κbar) (hA : 0 ≤ A) :
    pubProfitAB pa c r t κbar q A V ≤ pa * A - c * q ^ 2 := by
  have key : ∀ f : ℝ → ℝ → ℝ → ℝ, (∀ θ γ κ, 0 ≤ f θ γ κ) → (∀ θ γ κ, f θ γ κ ≤ 1) →
      pa * A * E3 r t κbar f - c * q ^ 2 ≤ pa * A - c * q ^ 2 := fun f h0 h1 => by
    nlinarith [mul_le_mul_of_nonneg_left (E3_unit hr1 ht1 hk.le h0 h1).2 (mul_nonneg hpa.le hA)]
  unfold pubProfitAB
  apply key <;> intros <;> split_ifs <;> norm_num

lemma pub_zero {pa c r t κbar A V : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht1 : t ≤ 1) (hA : 0 ≤ A) :
    pubProfitAB pa c r t κbar 0 A V ≤ 0 := by
  rcases hA.lt_or_eq with hA | hA
  · have key : ∀ f : ℝ → ℝ → ℝ → ℝ,
        (∀ θ ∈ Set.Icc t 1, ∀ γ ∈ Set.Icc r 1, ∀ κ, f θ γ κ = 0) →
        pa * A * E3 r t κbar f - c * 0 ^ 2 ≤ 0 := by
      intro f hf
      have : E3 r t κbar f = 0 := by
        unfold E3
        rw [integral_unifIcc_congr ht1 (g := fun _ => 0)]
        · simp
        · intro θ hθ
          rw [integral_unifIcc_congr hr1 (g := fun _ => 0)]
          · simp
          · intro γ hγ
            simp only [hf θ hθ γ hγ, integral_zero]
      rw [this]
      simp
    unfold pubProfitAB
    apply key
    intro θ _ γ hγ κ
    rw [if_neg]
    rintro ⟨h, -⟩
    unfold visits at h
    nlinarith [mul_pos (lt_of_lt_of_le hr0 hγ.1) hA]
  · subst hA
    unfold pubProfitAB
    simp

lemma csAB_hom {r t κbar q a v : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hk : 0 < κbar) (hq : 0 < q) (hqk : q ≤ κbar) (ha0 : 0 ≤ a) (hv0 : 0 ≤ v) :
    csAB r t κbar q (a * q) (v * q) = q * csNA r t 1 a + q ^ 2 * Hf r t a v / (2 * κbar) := by
  rw [csAB_eq r t κbar q (a * q) (v * q) hr1 ht1 hk hq.le hqk (mul_nonneg hv0 hq.le) hr0.le]
  rw [E2_congr hr1 ht1 (g := fun θ γ => q * max (θ - γ * a) 0 +
      q ^ 2 * (max (θ - γ * v - max (θ - γ * a) 0) 0) ^ 2 / (2 * κbar)) ?_]
  · rw [E2_add hr1 ht1 ?n1 ?n2, E2_mul, E2_div, E2_mul, csNA_one]
    · unfold Hf
      ring
    · refine nice_of (C := q) (meas_of_cont (by fun_prop)) (fun θ _ γ _ => by positivity)
        (fun θ hθ γ hγ => ?_)
      have : max (θ - γ * a) 0 ≤ 1 :=
        max_le (by nlinarith [hθ.2, mul_nonneg (le_trans hr0.le hγ.1) ha0]) zero_le_one
      simpa using mul_le_mul_of_nonneg_left this hq.le
    · refine nice_of (C := q ^ 2 / (2 * κbar)) (meas_of_cont (by fun_prop))
        (fun θ _ γ _ => by positivity) (fun θ hθ γ hγ => ?_)
      have hg := gp1_le (θ := θ) (γ := γ) (a := a) (v := v) hθ.2 (by linarith [hγ.1]) hv0
      have hg0 : 0 ≤ max (θ - γ * v - max (θ - γ * a) 0) 0 := le_max_right _ _
      have : (max (θ - γ * v - max (θ - γ * a) 0) 0) ^ 2 ≤ 1 := by nlinarith
      rw [div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg q)]
  · intro θ _ γ _
    rw [gp_hom' hq, lin_hom', mul_pos_max hq]
    try ring

lemma csNA_at {r t q a : ℝ} (hq : 0 < q) : csNA r t q (a * q) = q * csNA r t 1 a := by
  rw [csNA_hom hq, csNA_one, show a * q / q = a by field_simp]

/-! ## Part 4: equilibrium formulas, algebra and the reduction glue (session 2) -/

/-- Child A: the normalised benchmark revenue `b * demand r t 1 b` has a unique maximiser in `(0,1]`. -/
def ChildA : Prop := ∀ r t : ℝ, 0 < r → r ≤ 1 → 0 ≤ t → t ≤ 1 → ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
  ∀ b : ℝ, 0 ≤ b → b ≠ a → b * demand r t 1 b < a * demand r t 1 a

/-- Child V: the normalised adblocker objective `w * Gf r t a w` has a unique maximiser. -/
def ChildV : Prop := ∀ r t a : ℝ, 0 < r → r ≤ 1 → 0 ≤ t → t ≤ 1 → 0 < a → a ≤ 1 →
  ∃ v : ℝ, 0 ≤ v ∧ ∀ w : ℝ, 0 ≤ w → w ≠ v → w * Gf r t a w < v * Gf r t a v

/-- Child N: `Φ < 0` near the edges `r = 0` and `t = 0`. -/
def ChildNeg : Prop := ∃ ε : ℝ, 0 < ε ∧ ∀ r t : ℝ, 0 < r → r ≤ 1 → 0 ≤ t → t ≤ 1 →
  (r < ε ∨ t < ε) → ∀ a v : ℝ, 0 < a → a ≤ 1 →
  (∀ b, 0 ≤ b → b * demand r t 1 b ≤ a * demand r t 1 a) → 0 ≤ v →
  (∀ w, 0 ≤ w → w * Gf r t a w ≤ v * Gf r t a v) →
  demand r t 1 a * Hf r t a v < 4 * csNA r t 1 a * Bf r t a v

/-- Child P: `Φ > 0` near the corner `r = t = 1`. -/
def ChildPos : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ r t : ℝ, 0 < r → r ≤ 1 → 0 ≤ t → t ≤ 1 →
  1 - δ < r → 1 - δ < t → ∀ a v : ℝ, 0 < a →
  (∀ b, 0 ≤ b → b * demand r t 1 b ≤ a * demand r t 1 a) → 0 ≤ v →
  (∀ w, 0 ≤ w → w * Gf r t a w ≤ v * Gf r t a v) →
  4 * csNA r t 1 a * Bf r t a v < demand r t 1 a * Hf r t a v

lemma weak {f : ℝ → ℝ} {a : ℝ} (h : ∀ b, 0 ≤ b → b ≠ a → f b < f a) :
    ∀ b, 0 ≤ b → f b ≤ f a := fun b hb => by
  rcases eq_or_ne b a with h' | h'
  · rw [h']
  · exact (h b hb h').le

lemma core {pa c r t a v κbar : ℝ} (hs : Standing pa c r t) (ha0 : 0 < a)
    (hau : ∀ b, 0 ≤ b → b ≠ a → b * demand r t 1 b < a * demand r t 1 a)
    (hv0 : 0 ≤ v) (hvu : ∀ w, 0 ≤ w → w ≠ v → w * Gf r t a w < v * Gf r t a v)
    (hK : pa * a / c + 1 ≤ κbar) {Asel Vsel : ℝ → ℝ} {qN qA : ℝ}
    (hB : IsBenchEq pa c r t Asel qN) (hA : IsABEq pa c r t κbar Asel Vsel qA) :
    0 < demand r t 1 a ∧ 0 ≤ csNA r t 1 a ∧ 0 ≤ Bf r t a v ∧ 0 ≤ Hf r t a v ∧
    qN = pa * a * demand r t 1 a / (2 * c) ∧
    qA = pa * a * demand r t 1 a / (2 * (c + pa * a * Bf r t a v / κbar)) ∧
    csNA r t qN (Asel qN) = qN * csNA r t 1 a ∧
    csAB r t κbar qA (Asel qA) (Vsel qA) =
      qA * csNA r t 1 a + qA ^ 2 * Hf r t a v / (2 * κbar) := by
  obtain ⟨hpa, hc, hr0, hr1, ht0, ht1⟩ := hs
  have hs' : Standing pa c r t := ⟨hpa, hc, hr0, hr1, ht0, ht1⟩
  have hk : 0 < κbar := by
    have : 0 < pa * a / c := by positivity
    linarith
  have hD0 : 0 < demand r t 1 a := by
    have h := hau 0 le_rfl ha0.ne
    rw [zero_mul] at h
    by_contra hh
    have hh' := not_lt.mp hh
    nlinarith
  have hD1 : demand r t 1 a ≤ 1 := by
    rw [demand_one]
    exact (E2_unit hr1 ht1 (fun θ γ => by split_ifs <;> norm_num)
      (fun θ γ => by split_ifs <;> norm_num)).2
  have hs0 : 0 ≤ csNA r t 1 a := by
    rw [csNA_one]
    exact E2_nonneg hr1 ht1 (fun θ _ γ _ => le_max_right _ _)
  have hβ0 : 0 ≤ Bf r t a v := E2_nonneg hr1 ht1 (fun θ _ γ _ => by
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl)
  have hH0 : 0 ≤ Hf r t a v := E2_nonneg hr1 ht1 (fun θ _ γ _ => sq_nonneg _)
  have hasel : ∀ q, 0 < q → Asel q = a * q := fun q hq => asel_eq hs' ha0 hau hB.1 hq
  obtain ⟨α, hα⟩ : ∃ α, α = pa * a * demand r t 1 a := ⟨_, rfl⟩
  obtain ⟨k, hkd⟩ : ∃ k, k = pa * a * Bf r t a v / κbar := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  have hk0 : 0 ≤ k := by rw [hkd]; positivity
  have hck : 0 < c + k := by linarith
  have hαle : α ≤ pa * a := by
    rw [hα]
    nlinarith [mul_le_mul_of_nonneg_left hD1 (by positivity : (0 : ℝ) ≤ pa * a)]
  -- benchmark quantity
  have hqN : qN = α / (2 * c) := by
    apply quad_peak hc
    have h := hB.2.2 (α / (2 * c)) (by positivity)
    rw [benchProfit_eq hs' ha0 hau hB.1 (by positivity),
      benchProfit_eq hs' ha0 hau hB.1 hB.2.1, ← hα] at h
    exact h
  have hqN0 : 0 < qN := by rw [hqN]; positivity
  -- adblocker selection and publisher profit
  have hvsel : ∀ q, 0 < q → q ≤ κbar → Vsel q = v * q := fun q hq hqk =>
    vsel_eq hpa hr0 hr1 ht1 hk hv0 hvu hq hqk (by have h := hA.1 q hq.le; rwa [hasel q hq] at h)
  have hpub : ∀ q, 0 < q → q ≤ κbar →
      pubProfitAB pa c r t κbar q (Asel q) (Vsel q) = α * q - (c + k) * q ^ 2 :=
    fun q hq hqk => by
      rw [hasel q hq, hvsel q hq hqk, pub_eq hr0 hr1 ht0 ht1 hk hq hqk hv0, ← hα, ← hkd]
  obtain ⟨q1, hq1⟩ : ∃ q1, q1 = α / (2 * (c + k)) := ⟨_, rfl⟩
  have hq10 : 0 < q1 := by rw [hq1]; positivity
  have hq1k : q1 ≤ κbar := by
    have : q1 ≤ pa * a / c := by
      rw [hq1, div_le_div_iff₀ (by positivity) hc]
      nlinarith [mul_le_mul_of_nonneg_right hαle hc.le, mul_nonneg (mul_nonneg hpa.le ha0.le) hk0]
    linarith
  have e1 : (c + k) * q1 = α / 2 := by rw [hq1]; field_simp
  have hpos1 : 0 < α * q1 - (c + k) * q1 ^ 2 := by
    have : (c + k) * q1 ^ 2 = α / 2 * q1 := by rw [sq, ← mul_assoc, e1]
    nlinarith [mul_pos hq10 hα0]
  have hopt := hA.2.2 q1 hq10.le
  rw [hpub q1 hq10 hq1k] at hopt
  have hqA0 : 0 < qA := by
    rcases hA.2.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hopt
      have h0 := pub_zero (pa := pa) (c := c) (κbar := κbar) (V := Vsel 0) hr0 hr1 ht1
        (hB.1 0 le_rfl).1
      linarith
  have hqAk : qA ≤ κbar := by
    have h2 : pubProfitAB pa c r t κbar qA (Asel qA) (Vsel qA) ≤ pa * (a * qA) - c * qA ^ 2 := by
      have := pub_le (c := c) (κbar := κbar) (q := qA) (V := Vsel qA) hpa hr1 ht1 hk
        (hB.1 qA hA.2.1).1
      rw [hasel qA hqA0] at this ⊢
      exact this
    have h3 : c * qA < pa * a := by nlinarith
    have h4 : qA < pa * a / c := by rw [lt_div_iff₀ hc]; linarith
    linarith
  have hqA : qA = α / (2 * (c + k)) := by
    apply quad_peak hck
    rw [hpub qA hqA0 hqAk, hq1] at hopt
    exact hopt
  have hcsN : csNA r t qN (Asel qN) = qN * csNA r t 1 a := by
    rw [hasel qN hqN0]
    exact csNA_at hqN0
  have hcsA : csAB r t κbar qA (Asel qA) (Vsel qA) =
      qA * csNA r t 1 a + qA ^ 2 * Hf r t a v / (2 * κbar) := by
    rw [hasel qA hqA0, hvsel qA hqA0 hqAk]
    exact csAB_hom hr0 hr1 ht0 ht1 hk hqA0 hqAk ha0.le hv0
  refine ⟨hD0, hs0, hβ0, hH0, ?_, ?_, hcsN, hcsA⟩
  · rw [hqN, hα]
  · rw [hqA, hα, hkd]

lemma alg_neg {P c κ D s β H : ℝ} (hP : 0 < P) (hc : 0 < c) (hκ : 0 < κ) (hD : 0 < D)
    (hβ : 0 ≤ β) (hH : 0 ≤ H) (hphi : D * H < 4 * s * β) :
    P * D / (2 * (c + P * β / κ)) * s + (P * D / (2 * (c + P * β / κ))) ^ 2 * H / (2 * κ) <
      P * D / (2 * c) * s := by
  obtain ⟨M, hM⟩ : ∃ M, M = c + P * β / κ := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : c ≤ M := by
    rw [hM]
    have : 0 ≤ P * β / κ := by positivity
    linarith
  have hMpos : 0 < M := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = P * D / (2 * M) := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 < x := by rw [hx]; positivity
  have hPD : P * D = 2 * M * x := by rw [hx]; field_simp
  have hqN : P * D / (2 * c) = x * M / c := by rw [hPD]; field_simp <;> ring
  rw [hqN]
  have hxc : x * c ≤ P * D / 2 := by nlinarith [mul_le_mul_of_nonneg_left hM0 hx0.le]
  have key : x * H * c < 2 * P * β * s := by
    nlinarith [mul_le_mul_of_nonneg_right hxc hH, mul_lt_mul_of_pos_left hphi hP]
  have e : x * M / c * s = x * s + x * (P * β * s) / (κ * c) := by
    rw [hM]; field_simp <;> ring
  rw [e]
  have : x ^ 2 * H / (2 * κ) < x * (P * β * s) / (κ * c) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left key (mul_pos hx0 hκ)]
  linarith

lemma alg_pos {P c κ D s β H : ℝ} (hP : 0 < P) (hc : 0 < c) (hκ : 0 < κ) (hD : 0 < D)
    (hβ : 0 ≤ β) (hs : 0 ≤ s) (hphi : 4 * s * β < D * H)
    (hbig : 4 * P * β ^ 2 * s / (c * (D * H - 4 * s * β)) < κ) :
    P * D / (2 * c) * s <
      P * D / (2 * (c + P * β / κ)) * s + (P * D / (2 * (c + P * β / κ))) ^ 2 * H / (2 * κ) := by
  have hgap : 0 < D * H - 4 * s * β := by linarith
  rw [div_lt_iff₀ (by positivity)] at hbig
  obtain ⟨M, hM⟩ : ∃ M, M = c + P * β / κ := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : c ≤ M := by
    rw [hM]
    have : 0 ≤ P * β / κ := by positivity
    linarith
  have hMpos : 0 < M := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = P * D / (2 * M) := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 < x := by rw [hx]; positivity
  have hPD : P * D = 2 * M * x := by rw [hx]; field_simp
  have hqN : P * D / (2 * c) = x * M / c := by rw [hPD]; field_simp <;> ring
  rw [hqN]
  have h1 : 4 * P * β * s * M < P * D * H * c := by
    rw [hM]
    have e2 : 4 * P * β * s * (c + P * β / κ) = 4 * P * β * s * c + 4 * P ^ 2 * β ^ 2 * s / κ := by
      field_simp <;> ring
    rw [e2]
    have h2 : 4 * P ^ 2 * β ^ 2 * s / κ < P * c * (D * H - 4 * s * β) := by
      rw [div_lt_iff₀ hκ]
      nlinarith [mul_lt_mul_of_pos_left hbig hP]
    nlinarith
  have h3 : P * D * H * c = 2 * M * x * H * c := by rw [hPD]
  have key : 2 * P * β * s < x * H * c := by nlinarith
  have e : x * M / c * s = x * s + x * (P * β * s) / (κ * c) := by
    rw [hM]; field_simp <;> ring
  rw [e]
  have : x * (P * β * s) / (κ * c) < x ^ 2 * H / (2 * κ) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left key (mul_pos hx0 hκ)]
  linarith

theorem glue (hCA : ChildA) (hCV : ChildV) (hCN : ChildNeg) (hCP : ChildPos) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ pa c r t : ℝ, Standing pa c r t →
      (r < ε ∨ t < ε) →
      ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
        ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
          IsBenchEq pa c r t Asel qN →
          IsABEq pa c r t κbar Asel Vsel qA →
          csAB r t κbar qA (Asel qA) (Vsel qA) <
            csNA r t qN (Asel qN)) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ pa c r t : ℝ, Standing pa c r t →
      1 - δ < r → 1 - δ < t →
      ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
        ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
          IsBenchEq pa c r t Asel qN →
          IsABEq pa c r t κbar Asel Vsel qA →
          csNA r t qN (Asel qN) <
            csAB r t κbar qA (Asel qA) (Vsel qA)) := by
  constructor
  · obtain ⟨ε, hε, hneg⟩ := hCN
    refine ⟨ε, hε, fun pa c r t hs hrt => ?_⟩
    obtain ⟨hpa, hc, hr0, hr1, ht0, ht1⟩ := hs
    obtain ⟨a, ha0, ha1, hau⟩ := hCA r t hr0 hr1 ht0 ht1
    obtain ⟨v, hv0, hvu⟩ := hCV r t a hr0 hr1 ht0 ht1 ha0 ha1
    refine ⟨pa * a / c + 1, by positivity, fun κbar hK Asel Vsel qN qA hB hAB => ?_⟩
    obtain ⟨hD0, _, hβ0, hH0, hqN, hqA, hcsN, hcsA⟩ :=
      core ⟨hpa, hc, hr0, hr1, ht0, ht1⟩ ha0 hau hv0 hvu hK hB hAB
    have hk : 0 < κbar := by
      have : 0 < pa * a / c := by positivity
      linarith
    have hphi := hneg r t hr0 hr1 ht0 ht1 hrt a v ha0 ha1 (weak hau) hv0 (weak hvu)
    rw [hcsN, hcsA, hqN, hqA]
    exact alg_neg (P := pa * a) (by positivity) hc hk hD0 hβ0 hH0 hphi
  · obtain ⟨δ, hδ, hpos⟩ := hCP
    refine ⟨δ, hδ, fun pa c r t hs hr ht => ?_⟩
    obtain ⟨hpa, hc, hr0, hr1, ht0, ht1⟩ := hs
    obtain ⟨a, ha0, ha1, hau⟩ := hCA r t hr0 hr1 ht0 ht1
    obtain ⟨v, hv0, hvu⟩ := hCV r t a hr0 hr1 ht0 ht1 ha0 ha1
    have hphi := hpos r t hr0 hr1 ht0 ht1 hr ht a v ha0 (weak hau) hv0 (weak hvu)
    obtain ⟨K2, hK2d⟩ : ∃ K2, K2 = 4 * (pa * a) * Bf r t a v ^ 2 * csNA r t 1 a /
        (c * (demand r t 1 a * Hf r t a v - 4 * csNA r t 1 a * Bf r t a v)) + 1 := ⟨_, rfl⟩
    refine ⟨max (pa * a / c + 1) K2, lt_max_of_lt_left (by positivity),
      fun κbar hK Asel Vsel qN qA hB hAB => ?_⟩
    have hK1 : pa * a / c + 1 ≤ κbar := le_trans (le_max_left _ _) hK
    have hK2 : K2 ≤ κbar := le_trans (le_max_right _ _) hK
    obtain ⟨hD0, hs0, hβ0, _, hqN, hqA, hcsN, hcsA⟩ :=
      core ⟨hpa, hc, hr0, hr1, ht0, ht1⟩ ha0 hau hv0 hvu hK1 hB hAB
    have hk : 0 < κbar := by
      have : 0 < pa * a / c := by positivity
      linarith
    rw [hcsN, hcsA, hqN, hqA]
    exact alg_pos (P := pa * a) (by positivity) hc hk hD0 hβ0 hs0 hphi (by linarith)

/-! ## Part 5: Child P (Φ > 0 near the corner) by crude bounds (session 2) -/

lemma E2_const {r t : ℝ} (hr1 : r ≤ 1) (ht1 : t ≤ 1) (C : ℝ) : E2 r t (fun _ _ => C) = C := by
  have := unif_prob hr1
  have := unif_prob ht1
  unfold E2
  simp

lemma nice_const (r t C : ℝ) : Nice r t (fun _ _ => C) :=
  ⟨measurable_const, |C|, fun _ _ _ _ => le_rfl⟩

lemma nice_mul_const {r t : ℝ} (k : ℝ) {f : ℝ → ℝ → ℝ} (hf : Nice r t f) :
    Nice r t (fun θ γ => k * f θ γ) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.const_mul k, |k| * C, fun θ hθ γ hγ => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC θ hθ γ hγ) (abs_nonneg k)

lemma nice_sub {r t : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Nice r t f) (hg : Nice r t g) :
    Nice r t (fun θ γ => f θ γ - g θ γ) := by
  obtain ⟨hm1, C1, hC1⟩ := hf
  obtain ⟨hm2, C2, hC2⟩ := hg
  refine ⟨hm1.sub hm2, C1 + C2, fun θ hθ γ hγ => ?_⟩
  have h1 := abs_le.1 (hC1 θ hθ γ hγ)
  have h2 := abs_le.1 (hC2 θ hθ γ hγ)
  exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

lemma E2_mono {r t : ℝ} (hr1 : r ≤ 1) (ht1 : t ≤ 1) {f g : ℝ → ℝ → ℝ} (hf : Nice r t f)
    (hg : Nice r t g) (h : ∀ θ ∈ Set.Icc t 1, ∀ γ ∈ Set.Icc r 1, f θ γ ≤ g θ γ) :
    E2 r t f ≤ E2 r t g := by
  have := E2_nonneg hr1 ht1 (f := fun θ γ => g θ γ - f θ γ)
    (fun θ hθ γ hγ => sub_nonneg.2 (h θ hθ γ hγ))
  rw [E2_sub hr1 ht1 hg hf] at this
  linarith

/-- Jensen / Cauchy–Schwarz: `(E X)^2 ≤ E X^2`. -/
lemma E2_sq_ge {r t : ℝ} (hr1 : r ≤ 1) (ht1 : t ≤ 1) {f : ℝ → ℝ → ℝ} (hf : Nice r t f)
    (hf2 : Nice r t (fun θ γ => f θ γ ^ 2)) :
    (E2 r t f) ^ 2 ≤ E2 r t (fun θ γ => f θ γ ^ 2) := by
  obtain ⟨m, hm⟩ : ∃ m, m = E2 r t f := ⟨_, rfl⟩
  have h0 := E2_nonneg hr1 ht1 (f := fun θ γ => (f θ γ - m) ^ 2) (fun θ _ γ _ => sq_nonneg _)
  have e : (fun θ γ => (f θ γ - m) ^ 2) = fun θ γ => (f θ γ ^ 2 - (2 * m) * f θ γ) + m ^ 2 := by
    funext θ γ
    ring
  rw [e, E2_add hr1 ht1 (nice_sub hf2 (nice_mul_const _ hf)) (nice_const _ _ _),
    E2_sub hr1 ht1 hf2 (nice_mul_const _ hf), E2_mul, E2_const hr1 ht1, ← hm] at h0
  rw [← hm]
  nlinarith

lemma nice_gp {r t a w : ℝ} (hr0 : 0 < r) (ht0 : 0 ≤ t) (hw : 0 ≤ w) :
    Nice r t (fun θ γ => max (θ - γ * w - max (θ - γ * a) 0) 0) :=
  nice_of (C := 1) (meas_of_cont (by fun_prop)) (fun _ _ _ _ => le_max_right _ _)
    (fun θ hθ γ hγ => gp1_le hθ.2 (by linarith [hγ.1]) hw)

lemma nice_gp2 {r t a w : ℝ} (hr0 : 0 < r) (ht0 : 0 ≤ t) (hw : 0 ≤ w) :
    Nice r t (fun θ γ => (max (θ - γ * w - max (θ - γ * a) 0) 0) ^ 2) :=
  nice_of (C := 1) (meas_of_cont (by fun_prop)) (fun _ _ _ _ => sq_nonneg _)
    (fun θ hθ γ hγ => by
      have h1 := gp1_le (θ := θ) (γ := γ) (a := a) (v := w) hθ.2 (by linarith [hγ.1]) hw
      have h0 : 0 ≤ max (θ - γ * w - max (θ - γ * a) 0) 0 := le_max_right _ _
      nlinarith)

lemma nice_ind (r t a : ℝ) : Nice r t (fun θ γ => if 0 ≤ θ - γ * a then (1 : ℝ) else 0) :=
  nice_of (C := 1) (meas_ind_mul a (g := fun _ _ => 1) (by fun_prop))
    (fun θ _ γ _ => by split_ifs <;> norm_num) (fun θ _ γ _ => by split_ifs <;> norm_num)

lemma demand_at_t {r t : ℝ} (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    demand r t 1 t = 1 := by
  rw [demand_one, E2_congr hr1 ht1 (g := fun _ _ => 1), E2_const hr1 ht1]
  intro θ hθ γ hγ
  rw [if_pos]
  nlinarith [hθ.1, hγ.2, mul_le_mul_of_nonneg_right hγ.2 ht0]

lemma demand_zero_big {r t a : ℝ} (hr1 : r ≤ 1) (ht1 : t ≤ 1) (ha : 0 < a) (h : 1 < r * a) :
    demand r t 1 a = 0 := by
  rw [demand_one, E2_congr hr1 ht1 (g := fun _ _ => 0), E2_const hr1 ht1]
  intro θ hθ γ hγ
  rw [if_neg]
  intro h'
  nlinarith [hθ.2, mul_le_mul_of_nonneg_right hγ.1 ha.le]

lemma Gf_zero {r t a v : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht1 : t ≤ 1) (hav : a ≤ v) :
    Gf r t a v = 0 := by
  unfold Gf
  rw [E2_congr hr1 ht1 (g := fun _ _ => 0), E2_const hr1 ht1]
  intro θ _ γ hγ
  apply max_eq_right
  nlinarith [le_max_left (θ - γ * a) 0, mul_le_mul_of_nonneg_left hav (le_trans hr0.le hγ.1)]

theorem childPos : ChildPos := by
  refine ⟨1 / 200, by norm_num, ?_⟩
  intro r t hr0 hr1 ht0 ht1 hr ht a v ha0 hamax hv0 hvmax
  have hDu := E2_unit hr1 ht1 (f := fun θ γ => if 0 ≤ θ - γ * a then (1 : ℝ) else 0)
    (fun θ γ => by split_ifs <;> norm_num) (fun θ γ => by split_ifs <;> norm_num)
  rw [← demand_one] at hDu
  obtain ⟨hD0, hD1⟩ := hDu
  have htpos : 0 < t := by linarith
  have hRt : t ≤ a * demand r t 1 a := by
    have h := hamax t ht0
    rwa [demand_at_t hr1 ht0 ht1, mul_one] at h
  have hat : t ≤ a := by nlinarith [mul_le_mul_of_nonneg_left hD1 ha0.le]
  have har : r * a ≤ 1 := by
    by_contra h
    rw [not_le] at h
    rw [demand_zero_big hr1 ht1 ha0 h, mul_zero] at hRt
    linarith
  have hD : r * t ≤ demand r t 1 a := by
    nlinarith [mul_le_mul_of_nonneg_left hRt hr0.le, mul_le_mul_of_nonneg_right har hD0]
  have hrt1 : r * t ≤ 1 := by nlinarith [mul_le_mul hr1 ht1 ht0 zero_le_one]
  have hγa : ∀ γ ∈ Set.Icc r 1, r * t ≤ γ * a := fun γ hγ => by
    nlinarith [mul_le_mul_of_nonneg_right hγ.1 ha0.le, mul_le_mul_of_nonneg_left hat hr0.le]
  have niceA : Nice r t (fun θ γ => max (θ - γ * a) 0) :=
    nice_of (C := 1) (meas_of_cont (by fun_prop)) (fun _ _ _ _ => le_max_right _ _)
      (fun θ hθ γ hγ => max_le (by nlinarith [hθ.2, hγa γ hγ, mul_pos hr0 htpos]) zero_le_one)
  have hs : csNA r t 1 a ≤ 1 - r * t := by
    rw [csNA_one]
    calc E2 r t (fun θ γ => max (θ - γ * a) 0) ≤ E2 r t (fun _ _ => 1 - r * t) :=
          E2_mono hr1 ht1 niceA (nice_const _ _ _)
            (fun θ hθ γ hγ => max_le (by nlinarith [hθ.2, hγa γ hγ]) (by linarith))
      _ = 1 - r * t := E2_const hr1 ht1 _
  have hs0 : 0 ≤ csNA r t 1 a := by
    rw [csNA_one]
    exact E2_nonneg hr1 ht1 (fun θ _ γ _ => le_max_right _ _)
  have niceB : Nice r t (fun θ γ => if 0 ≤ θ - γ * a then
      max (θ - γ * v - max (θ - γ * a) 0) 0 else 0) :=
    nice_of (C := 1) (meas_ind_mul a (by fun_prop))
      (fun θ _ γ _ => by split_ifs; exacts [le_max_right _ _, le_rfl])
      (fun θ hθ γ hγ => by
        split_ifs
        · exact gp1_le hθ.2 (by linarith [hγ.1]) hv0
        · exact zero_le_one)
  have hβ : Bf r t a v ≤ 1 := by
    unfold Bf
    calc _ ≤ E2 r t (fun _ _ => (1 : ℝ)) :=
          E2_mono hr1 ht1 niceB (nice_const _ _ _) (fun θ hθ γ hγ => by
            split_ifs
            · exact gp1_le hθ.2 (by linarith [hγ.1]) hv0
            · exact zero_le_one)
      _ = 1 := E2_const hr1 ht1 _
  have hβ0 : 0 ≤ Bf r t a v := E2_nonneg hr1 ht1 (fun θ _ γ _ => by
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl)
  have hG2 : r * t / 2 * demand r t 1 a ≤ Gf r t a (a / 2) := by
    rw [demand_one, ← E2_mul]
    unfold Gf
    refine E2_mono hr1 ht1 (nice_mul_const _ (nice_ind r t a))
      (nice_gp hr0 ht0 (by positivity)) (fun θ hθ γ hγ => ?_)
    split_ifs with h
    · rw [max_eq_left h, mul_one]
      apply le_max_of_le_left
      nlinarith [hγa γ hγ]
    · rw [mul_zero]
      exact le_max_right _ _
  have hG2pos : 0 < Gf r t a (a / 2) :=
    lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le (mul_pos hr0 htpos) hD)) hG2
  have hvG := hvmax (a / 2) (by positivity)
  have hva : v ≤ a := by
    by_contra h
    rw [not_le] at h
    rw [Gf_zero hr0 hr1 ht1 h.le, mul_zero] at hvG
    nlinarith [mul_pos (half_pos ha0) hG2pos]
  have hGv0 : 0 ≤ Gf r t a v := E2_nonneg hr1 ht1 (fun θ _ γ _ => le_max_right _ _)
  have hGv : Gf r t a (a / 2) / 2 ≤ Gf r t a v := by
    nlinarith [mul_le_mul_of_nonneg_right hva hGv0]
  have hH : Gf r t a v ^ 2 ≤ Hf r t a v :=
    E2_sq_ge hr1 ht1 (nice_gp hr0 ht0 hv0) (nice_gp2 hr0 ht0 hv0)
  obtain ⟨u, hu⟩ : ∃ u, u = r * t := ⟨_, rfl⟩
  rw [← hu] at hD hs hrt1
  have hr' : 199 / 200 < r := by linarith
  have ht' : 199 / 200 < t := by linarith
  have hul : (199 / 200 : ℝ) ^ 2 ≤ u := by
    rw [hu, sq]
    exact mul_le_mul hr'.le ht'.le (by norm_num) hr0.le
  have hu0 : 0 ≤ u := le_trans (by norm_num) hul
  have h1 : u ^ 2 / 4 ≤ Gf r t a v := by
    have : u / 2 * u ≤ u / 2 * demand r t 1 a := mul_le_mul_of_nonneg_left hD (by positivity)
    rw [← hu] at hG2
    nlinarith
  have h2 : (u ^ 2 / 4) ^ 2 ≤ Hf r t a v :=
    le_trans (pow_le_pow_left₀ (by positivity) h1 2) hH
  have h3 : u * (u ^ 2 / 4) ^ 2 ≤ demand r t 1 a * Hf r t a v :=
    mul_le_mul hD h2 (by positivity) hD0
  have h4 : 4 * csNA r t 1 a * Bf r t a v ≤ 4 * (1 - u) := by
    nlinarith [mul_le_mul_of_nonneg_left hβ hs0]
  have h5 : 4 * (1 - u) < u * (u ^ 2 / 4) ^ 2 := by
    have h6 := pow_le_pow_left₀ (by norm_num) hul 5
    have e : u * (u ^ 2 / 4) ^ 2 = u ^ 5 / 16 := by ring
    rw [e]
    norm_num at h6
    linarith
  linarith

/-! ## Part 6: Child N (Φ < 0 near the edges) by boundary perturbation (session 3) -/

lemma unif_int {t : ℝ} (ht : t < 1) (f : ℝ → ℝ) :
    ∫ x, f x ∂(unifIcc t 1) = (∫ x in t..1, f x) / (1 - t) := by
  have h : unifIcc t 1 = (ENNReal.ofReal (1 - t))⁻¹ • volume.restrict (Set.Icc t 1) := by
    simp [unifIcc, ht]
  rw [h, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.le,
    inv_mul_eq_div]

lemma unif01 (f : ℝ → ℝ) : ∫ x, f x ∂(unifIcc 0 1) = ∫ x in (0 : ℝ)..1, f x := by
  rw [unif_int (by norm_num)]
  norm_num

/-- Antiderivative of a cubic. -/
noncomputable def Fp (c0 c1 c2 c3 y : ℝ) : ℝ :=
  c0 * y + c1 * y ^ 2 / 2 + c2 * y ^ 3 / 3 + c3 * y ^ 4 / 4

lemma ipoly (a b c0 c1 c2 c3 : ℝ) :
    ∫ x in a..b, (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) =
      Fp c0 c1 c2 c3 b - Fp c0 c1 c2 c3 a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have h := ((((hasDerivAt_id' x).const_mul c0).add
      (((hasDerivAt_pow 2 x).const_mul c1).div_const 2)).add
      (((hasDerivAt_pow 3 x).const_mul c2).div_const 3)).add
      (((hasDerivAt_pow 4 x).const_mul c3).div_const 4)
    convert h using 1 <;> first | (unfold Fp; rfl) | (norm_num; ring) | norm_num | rfl
  · exact (by fun_prop : Continuous fun x : ℝ => c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3
      ).intervalIntegrable _ _

lemma congr_poly {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (c0 c1 c2 c3 : ℝ)
    (h : ∀ x ∈ Set.Icc a b, f x = c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) :
    ∫ x in a..b, f x = Fp c0 c1 c2 c3 b - Fp c0 c1 c2 c3 a := by
  rw [← ipoly]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact h x hx

lemma split_at {f : ℝ → ℝ} (hf : Continuous f) {a c : ℝ} (b : ℝ) :
    ∫ x in a..c, f x = (∫ x in a..b, f x) + ∫ x in b..c, f x :=
  (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)).symm

lemma unif_poly {r : ℝ} (hr : r ≤ 1) (c0 c1 c2 c3 : ℝ) :
    ∫ x, (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) ∂(unifIcc r 1) =
      c0 + c1 * ((1 + r) / 2) + c2 * ((1 + r + r ^ 2) / 3) +
        c3 * ((1 + r + r ^ 2 + r ^ 3) / 4) := by
  rcases hr.lt_or_eq with hr | hr
  · rw [unif_int hr, ipoly]
    have : (1 - r) ≠ 0 := by linarith
    unfold Fp
    field_simp
    ring
  · subst hr
    simp [unifIcc] <;> ring

lemma int_bdd {a b C : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : Measurable g)
    (hC : ∀ x ∈ Set.Icc a b, |g x| ≤ C) : Integrable g (unifIcc a b) := by
  have := unif_prob hab
  exact Integrable.of_bound hg.aestronglyMeasurable C
    ((unif_ae hab).mono fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx)

/-- Total-variation bound between `U[t,1]` and `U[0,1]`. -/
lemma tv1 {g : ℝ → ℝ} (hg : Measurable g) {C t : ℝ}
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ C) (ht0 : 0 ≤ t) (ht : t < 1) :
    |∫ x, g x ∂(unifIcc t 1) - ∫ x, g x ∂(unifIcc 0 1)| ≤ 2 * C * t := by
  have hii : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → a ≤ b → IntervalIntegrable g volume a b := by
    intro a b ha hb hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hg.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_)
    rw [Real.norm_eq_abs]
    exact hC x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [unif_int ht, unif01, ← intervalIntegral.integral_add_adjacent_intervals
    (hii 0 t le_rfl ht.le ht0) (hii t 1 ht0 le_rfl ht.le)]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := 1) (f := g)
    (C := C) (fun x hx => by
      rw [Set.uIoc_of_le ht.le] at hx
      rw [Real.norm_eq_abs]
      exact hC x ⟨by linarith [hx.1], hx.2⟩)
  have hJ := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (f := g)
    (C := C) (fun x hx => by
      rw [Set.uIoc_of_le ht0] at hx
      rw [Real.norm_eq_abs]
      exact hC x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)] at hI
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - 0)] at hJ
  obtain ⟨I, hIdef⟩ : ∃ I, I = ∫ x in t..1, g x := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J, J = ∫ x in (0 : ℝ)..t, g x := ⟨_, rfl⟩
  rw [← hIdef] at hI ⊢
  rw [← hJdef] at hJ ⊢
  have h1t : 0 < 1 - t := by linarith
  have e : I / (1 - t) - (J + I) = I * t / (1 - t) - J := by field_simp; ring
  rw [e]
  have hIt : |I * t / (1 - t)| ≤ C * t := by
    rw [abs_div, abs_mul, abs_of_pos h1t, abs_of_nonneg ht0, div_le_iff₀ h1t]
    nlinarith [abs_nonneg I, mul_le_mul_of_nonneg_right hI ht0]
  have h1 := abs_le.1 hIt
  have h2 := abs_le.1 hJ
  rw [abs_le]
  constructor <;> linarith

lemma inner_bdd {r C : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hC : ∀ γ ∈ Set.Icc (0 : ℝ) 1, |f θ γ| ≤ C) : |∫ γ, f θ γ ∂(unifIcc r 1)| ≤ C := by
  have := unif_prob hr
  have := norm_integral_le_of_norm_le_const (μ := unifIcc r 1) (f := f θ) (C := C)
    ((unif_ae hr).mono fun γ hγ => by
      rw [Real.norm_eq_abs]
      exact hC γ ⟨by linarith [hγ.1], hγ.2⟩)
  simpa [probReal_univ] using this

lemma tvθ {r t C : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht : t < 1)
    {f : ℝ → ℝ → ℝ} (hm : Measurable (Function.uncurry f))
    (hC : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1, |f θ γ| ≤ C) :
    |E2 r t f - E2 r 0 f| ≤ 2 * C * t := by
  have := unif_prob hr1
  have hs : StronglyMeasurable fun θ => ∫ γ, f θ γ ∂(unifIcc r 1) :=
    hm.stronglyMeasurable.integral_prod_right
  unfold E2
  exact tv1 hs.measurable (fun θ hθ => inner_bdd hr0 hr1 (hC θ hθ)) ht0 ht

lemma tvγ {r t C : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {f : ℝ → ℝ → ℝ} (hm : Measurable (Function.uncurry f))
    (hC : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1, |f θ γ| ≤ C) :
    |E2 r t f - E2 0 t f| ≤ 2 * C * r := by
  have hn : ∀ s : ℝ, 0 ≤ s → Nice s t f := fun s hs =>
    ⟨hm, C, fun θ hθ γ hγ => hC θ ⟨by linarith [hθ.1], hθ.2⟩ γ ⟨by linarith [hγ.1], hγ.2⟩⟩
  have := unif_prob ht1
  unfold E2
  rw [← integral_sub (nice_outer hr.le ht1 (hn r hr0)) (nice_outer zero_le_one ht1 (hn 0 le_rfl))]
  have := norm_integral_le_of_norm_le_const (μ := unifIcc t 1) (C := 2 * C * r)
    (f := fun θ => ∫ γ, f θ γ ∂(unifIcc r 1) - ∫ γ, f θ γ ∂(unifIcc 0 1))
    ((unif_ae ht1).mono fun θ hθ => by
      have hm' : Measurable (f θ) := hm.comp (measurable_const.prodMk measurable_id)
      rw [Real.norm_eq_abs]
      exact tv1 hm' (fun γ hγ => hC θ ⟨by linarith [hθ.1], hθ.2⟩ γ hγ) hr0 hr)
  simpa [probReal_univ] using this

lemma E2_swap {r t : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) {f : ℝ → ℝ → ℝ} (hf : Nice r t f) :
    E2 r t f = ∫ γ, ∫ θ, f θ γ ∂(unifIcc t 1) ∂(unifIcc r 1) := by
  have := unif_prob hr
  have := unif_prob ht
  obtain ⟨hm, C, hC⟩ := hf
  unfold E2
  apply integral_integral_swap
  refine Integrable.of_bound hm.aestronglyMeasurable C ?_
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).2 ?_
  filter_upwards [unif_ae ht] with θ hθ
  filter_upwards [unif_ae hr] with γ hγ
  rw [Real.norm_eq_abs]
  exact hC θ hθ γ hγ

/-! ### Integrands -/

noncomputable def fD (b : ℝ) : ℝ → ℝ → ℝ := fun θ γ => if 0 ≤ θ - γ * b then 1 else 0
noncomputable def fS (b : ℝ) : ℝ → ℝ → ℝ := fun θ γ => max (θ - γ * b) 0
noncomputable def fM (b : ℝ) : ℝ → ℝ → ℝ := fun θ γ => if 0 ≤ θ - γ * b then γ else 0
noncomputable def fK (b : ℝ) : ℝ → ℝ → ℝ := fun θ γ => γ * min θ (γ * b)

lemma mD (b : ℝ) : Measurable (Function.uncurry (fD b)) :=
  meas_ind_mul b (g := fun _ _ => 1) (by fun_prop)
lemma mS (b : ℝ) : Measurable (Function.uncurry (fS b)) := meas_of_cont (by unfold fS; fun_prop)
lemma mM (b : ℝ) : Measurable (Function.uncurry (fM b)) :=
  meas_ind_mul b (g := fun _ γ => γ) (by fun_prop)
lemma mK (b : ℝ) : Measurable (Function.uncurry (fK b)) := meas_of_cont (by unfold fK; fun_prop)

lemma bD (b : ℝ) : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1, |fD b θ γ| ≤ 1 :=
  fun θ _ γ _ => by unfold fD; split_ifs <;> norm_num
lemma bS {b : ℝ} (hb0 : 0 ≤ b) : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1,
    |fS b θ γ| ≤ 1 := fun θ hθ γ hγ => by
  unfold fS
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (by nlinarith [hθ.2, mul_nonneg hγ.1 hb0]) zero_le_one
lemma bM (b : ℝ) : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1, |fM b θ γ| ≤ 1 :=
  fun θ _ γ hγ => by
    unfold fM
    split_ifs
    · rw [abs_of_nonneg hγ.1]; exact hγ.2
    · norm_num
lemma bK {b : ℝ} (hb0 : 0 ≤ b) : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1,
    |fK b θ γ| ≤ 1 := fun θ hθ γ hγ => by
  unfold fK
  have h0 : 0 ≤ min θ (γ * b) := le_min hθ.1 (mul_nonneg hγ.1 hb0)
  have h1 : min θ (γ * b) ≤ 1 := le_trans (min_le_left _ _) hθ.2
  rw [abs_of_nonneg (mul_nonneg hγ.1 h0)]
  nlinarith [hγ.2, hγ.1]

lemma niceq {f : ℝ → ℝ → ℝ} (hm : Measurable (Function.uncurry f))
    (hC : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1, |f θ γ| ≤ 1) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) : Nice r t f :=
  ⟨hm, 1, fun θ hθ γ hγ => hC θ ⟨le_trans ht hθ.1, hθ.2⟩ γ ⟨le_trans hr hγ.1, hγ.2⟩⟩

lemma E2_le1 {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {f : ℝ → ℝ → ℝ} (hm : Measurable (Function.uncurry f))
    (hC : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ Set.Icc (0 : ℝ) 1, |f θ γ| ≤ 1) : E2 r t f ≤ 1 := by
  have := E2_mono hr1 ht1 (niceq hm hC hr0 ht0) (nice_const r t 1)
    (fun θ hθ γ hγ => (abs_le.1 (hC θ ⟨le_trans ht0 hθ.1, hθ.2⟩ γ ⟨le_trans hr0 hγ.1, hγ.2⟩)).2)
  rwa [E2_const hr1 ht1] at this

/-! ### One-dimensional kink integrals -/

lemma iT1 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ θ, (if 0 ≤ θ - x then (1 : ℝ) else 0) ∂(unifIcc 0 1) = 1 - x := by
  have := integral_unif0_ind_ge 1 x one_pos hx1
  rw [max_eq_left hx0, div_one] at this
  rw [← this]
  congr 1
  funext θ
  by_cases h : θ < x
  · rw [if_pos h, if_neg (by linarith)]
  · rw [if_neg h, if_pos (by linarith)]

lemma iT2 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ θ, max (θ - x) 0 ∂(unifIcc 0 1) = (1 - x) ^ 2 / 2 := by
  rw [unif01, split_at (f := fun θ => max (θ - x) 0) (by fun_prop) x,
    congr_poly (f := fun θ => max (θ - x) 0) hx0 0 0 0 0 (fun θ hθ => by
      show max (θ - x) 0 = _
      rw [max_eq_right (by linarith [hθ.2])]; ring),
    congr_poly (f := fun θ => max (θ - x) 0) hx1 (-x) 1 0 0 (fun θ hθ => by
      show max (θ - x) 0 = _
      rw [max_eq_left (by linarith [hθ.1])]; ring)]
  unfold Fp; ring

lemma iT3 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ θ, min θ x ∂(unifIcc 0 1) = x - x ^ 2 / 2 := by
  rw [unif01, split_at (f := fun θ => min θ x) (by fun_prop) x,
    congr_poly (f := fun θ => min θ x) hx0 0 1 0 0 (fun θ hθ => by
      show min θ x = _
      rw [min_eq_left hθ.2]; ring),
    congr_poly (f := fun θ => min θ x) hx1 x 0 0 0 (fun θ hθ => by
      show min θ x = _
      rw [min_eq_right hθ.1]; ring)]
  unfold Fp; ring

lemma iR1 {θ b : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) :
    ∫ γ, (if 0 ≤ θ - γ * b then (1 : ℝ) else 0) ∂(unifIcc 0 1) = min (θ / b) 1 := by
  rw [integral_unif0 1 one_pos, div_one]
  have hfun : (fun γ : ℝ => if 0 ≤ θ - γ * b then (1 : ℝ) else 0) =
      (Set.Iic (θ / b)).indicator 1 := by
    funext γ
    have e : (0 ≤ θ - γ * b) ↔ γ ≤ θ / b := by
      rw [le_div_iff₀ hb]; constructor <;> intro h <;> linarith
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply, e]
  rw [hfun, integral_indicator_one measurableSet_Iic, Measure.real,
    Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic (θ / b) ∩ Set.Icc 0 1 = Set.Icc 0 (min (θ / b) 1) := by
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    tauto
  rw [this, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal (le_min (div_nonneg hθ hb.le) zero_le_one)]

lemma iR2 {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∫ γ, max (θ - γ) 0 ∂(unifIcc 0 1) = θ ^ 2 / 2 := by
  rw [unif01, split_at (f := fun γ => max (θ - γ) 0) (by fun_prop) θ,
    congr_poly (f := fun γ => max (θ - γ) 0) h0 θ (-1) 0 0 (fun γ hγ => by
      show max (θ - γ) 0 = _
      rw [max_eq_left (by linarith [hγ.2])]; ring),
    congr_poly (f := fun γ => max (θ - γ) 0) h1 0 0 0 0 (fun γ hγ => by
      show max (θ - γ) 0 = _
      rw [max_eq_right (by linarith [hγ.1])]; ring)]
  unfold Fp; ring

lemma iR3 {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∫ γ, (if 0 ≤ θ - γ then γ else 0) ∂(unifIcc 0 1) = θ ^ 2 / 2 := by
  have e : (fun γ : ℝ => if 0 ≤ θ - γ then γ else 0) =
      fun γ => θ * (if 0 ≤ θ - γ * 1 then (1 : ℝ) else 0) - max (θ - γ) 0 := by
    funext γ
    simp only [mul_one]
    split_ifs with h
    · rw [max_eq_left h]; ring
    · rw [max_eq_right (by linarith)]; ring
  have hmi : Measurable fun γ : ℝ => (if 0 ≤ θ - γ * 1 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
      measurable_const
  rw [e, integral_sub (int_bdd zero_le_one (hmi.const_mul θ) (C := θ) (fun γ _ => by
      split_ifs <;> simp [abs_of_nonneg h0, h0]))
    (int_bdd zero_le_one (C := 1) (by fun_prop) (fun γ hγ => by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hγ.1]) zero_le_one)),
    integral_const_mul, iR1 one_pos h0, iR2 h0 h1, div_one, min_eq_left h1]
  ring

lemma iR4 {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∫ γ, γ * min θ γ ∂(unifIcc 0 1) = θ / 2 - θ ^ 3 / 6 := by
  rw [unif01, split_at (f := fun γ => γ * min θ γ) (by fun_prop) θ,
    congr_poly (f := fun γ => γ * min θ γ) h0 0 0 1 0 (fun γ hγ => by
      show γ * min θ γ = _
      rw [min_eq_right hγ.2]; ring),
    congr_poly (f := fun γ => γ * min θ γ) h1 0 θ 0 0 (fun γ hγ => by
      show γ * min θ γ = _
      rw [min_eq_left hγ.1]; ring)]
  unfold Fp; ring

lemma L4 {t a : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∫ θ, min θ a ∂(unifIcc t 1) ≤ (1 + t) / 2 - (1 - a) ^ 2 / 2 := by
  rcases le_or_gt a t with hat | hta
  · have e : ∫ θ, min θ a ∂(unifIcc t 1) =
        ∫ θ, (a + 0 * θ + 0 * θ ^ 2 + 0 * θ ^ 3) ∂(unifIcc t 1) :=
      integral_unifIcc_congr ht1 (fun θ hθ => by rw [min_eq_right (by linarith [hθ.1])]; ring)
    rw [e, unif_poly ht1]
    nlinarith [mul_nonneg (sub_nonneg.2 ha1) ha0.le]
  · have ht : t < 1 := lt_of_lt_of_le hta ha1
    rw [unif_int ht, split_at (f := fun θ => min θ a) (by fun_prop) a,
      congr_poly (f := fun θ => min θ a) hta.le 0 1 0 0 (fun θ hθ => by
        show min θ a = _
        rw [min_eq_left hθ.2]; ring),
      congr_poly (f := fun θ => min θ a) ha1 a 0 0 0 (fun θ hθ => by
        show min θ a = _
        rw [min_eq_right hθ.1]; ring)]
    unfold Fp
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg ht0 (sq_nonneg (1 - a))]

/-! ### Boundary formulas -/

lemma t0_formula {r : ℝ} (hr1 : r ≤ 1) {f : ℝ → ℝ → ℝ} (hn : Nice r 0 f) (c0 c1 c2 c3 : ℝ)
    (h : ∀ γ ∈ Set.Icc r 1, ∫ θ, f θ γ ∂(unifIcc 0 1) = c0 + c1 * γ + c2 * γ ^ 2 + c3 * γ ^ 3) :
    E2 r 0 f = c0 + c1 * ((1 + r) / 2) + c2 * ((1 + r + r ^ 2) / 3) +
      c3 * ((1 + r + r ^ 2 + r ^ 3) / 4) := by
  rw [E2_swap hr1 zero_le_one hn, ← unif_poly hr1]
  exact integral_unifIcc_congr hr1 h

lemma r0_formula {t : ℝ} (ht1 : t ≤ 1) {f : ℝ → ℝ → ℝ} (c0 c1 c2 c3 : ℝ)
    (h : ∀ θ ∈ Set.Icc t 1, ∫ γ, f θ γ ∂(unifIcc 0 1) = c0 + c1 * θ + c2 * θ ^ 2 + c3 * θ ^ 3) :
    E2 0 t f = c0 + c1 * ((1 + t) / 2) + c2 * ((1 + t + t ^ 2) / 3) +
      c3 * ((1 + t + t ^ 2 + t ^ 3) / 4) := by
  unfold E2
  rw [← unif_poly ht1]
  exact integral_unifIcc_congr ht1 h

lemma t0D {r b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    E2 r 0 (fD b) = 1 - b * ((1 + r) / 2) := by
  rw [t0_formula hr1 (niceq (mD b) (bD b) hr0 le_rfl) 1 (-b) 0 0 (fun γ hγ => by
    have g0 : 0 ≤ γ := le_trans hr0 hγ.1
    simp only [fD]
    rw [iT1 (mul_nonneg g0 hb0) (by nlinarith [hγ.2])]
    ring)]
  ring

lemma t0S {r b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    E2 r 0 (fS b) = (1 - 2 * b * ((1 + r) / 2) + b ^ 2 * ((1 + r + r ^ 2) / 3)) / 2 := by
  rw [t0_formula hr1 (niceq (mS b) (bS hb0) hr0 le_rfl) (1 / 2) (-b) (b ^ 2 / 2) 0
    (fun γ hγ => by
      have g0 : 0 ≤ γ := le_trans hr0 hγ.1
      simp only [fS]
      rw [iT2 (mul_nonneg g0 hb0) (by nlinarith [hγ.2])]
      ring)]
  ring

lemma t0M {r b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    E2 r 0 (fM b) = (1 + r) / 2 - b * ((1 + r + r ^ 2) / 3) := by
  rw [t0_formula hr1 (niceq (mM b) (bM b) hr0 le_rfl) 0 1 (-b) 0 (fun γ hγ => by
    have g0 : 0 ≤ γ := le_trans hr0 hγ.1
    have e : (fun θ => fM b θ γ) = fun θ => γ * (if 0 ≤ θ - γ * b then (1 : ℝ) else 0) := by
      funext θ
      simp only [fM]
      split_ifs <;> ring
    show ∫ θ, (fun θ => fM b θ γ) θ ∂(unifIcc 0 1) = _
    rw [e, integral_const_mul, iT1 (mul_nonneg g0 hb0) (by nlinarith [hγ.2])]
    ring)]
  ring

lemma t0K {r b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    E2 r 0 (fK b) = b * ((1 + r + r ^ 2) / 3) - b ^ 2 * ((1 + r + r ^ 2 + r ^ 3) / 4) / 2 := by
  rw [t0_formula hr1 (niceq (mK b) (bK hb0) hr0 le_rfl) 0 0 b (-(b ^ 2 / 2)) (fun γ hγ => by
    have g0 : 0 ≤ γ := le_trans hr0 hγ.1
    simp only [fK]
    rw [integral_const_mul, iT3 (mul_nonneg g0 hb0) (by nlinarith [hγ.2])]
    ring)]
  ring

lemma r0Da {t a : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) :
    a * E2 0 t (fD a) = ∫ θ, min θ a ∂(unifIcc t 1) := by
  unfold E2
  rw [← integral_const_mul]
  apply integral_unifIcc_congr ht1
  intro θ hθ
  simp only [fD]
  rw [iR1 ha (le_trans ht0 hθ.1), mul_min_of_nonneg _ _ ha.le, mul_one]
  congr 1
  field_simp

lemma r0D1 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : E2 0 t (fD 1) = (1 + t) / 2 := by
  have h := r0Da ht0 ht1 one_pos
  rw [one_mul] at h
  rw [h, ← add_zero ((1 + t) / 2)]
  have e : ∫ θ, min θ 1 ∂(unifIcc t 1) = ∫ θ, (0 + 1 * θ + 0 * θ ^ 2 + 0 * θ ^ 3) ∂(unifIcc t 1) :=
    integral_unifIcc_congr ht1 (fun θ hθ => by rw [min_eq_left hθ.2]; ring)
  rw [e, unif_poly ht1]
  ring

lemma r0S1 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : E2 0 t (fS 1) = (1 + t + t ^ 2) / 6 := by
  rw [r0_formula ht1 0 0 (1 / 2) 0 (fun θ hθ => by
    simp only [fS, mul_one]
    rw [iR2 (le_trans ht0 hθ.1) hθ.2]
    ring)]
  ring

lemma r0M1 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : E2 0 t (fM 1) = (1 + t + t ^ 2) / 6 := by
  rw [r0_formula ht1 0 0 (1 / 2) 0 (fun θ hθ => by
    simp only [fM, mul_one]
    rw [iR3 (le_trans ht0 hθ.1) hθ.2]
    ring)]
  ring

lemma r0K1 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    E2 0 t (fK 1) = (1 + t) / 4 - (1 + t + t ^ 2 + t ^ 3) / 24 := by
  rw [r0_formula ht1 0 (1 / 2) 0 (-(1 / 6)) (fun θ hθ => by
    simp only [fK, mul_one]
    rw [iR4 (le_trans ht0 hθ.1) hθ.2]
    ring)]
  ring

/-! ### The two strips -/

lemma nn_D {r t b : ℝ} (hr1 : r ≤ 1) (ht1 : t ≤ 1) : 0 ≤ E2 r t (fD b) :=
  E2_nonneg hr1 ht1 (fun θ _ γ _ => by simp only [fD]; split_ifs <;> norm_num)
lemma nn_S {r t b : ℝ} (hr1 : r ≤ 1) (ht1 : t ≤ 1) : 0 ≤ E2 r t (fS b) :=
  E2_nonneg hr1 ht1 (fun θ _ γ _ => by simp only [fS]; exact le_max_right _ _)
lemma nn_M {r t b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht1 : t ≤ 1) : 0 ≤ E2 r t (fM b) :=
  E2_nonneg hr1 ht1 (fun θ _ γ hγ => by
    simp only [fM]; split_ifs
    · exact le_trans hr0 hγ.1
    · exact le_rfl)
lemma nn_K {r t b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb : 0 ≤ b) :
    0 ≤ E2 r t (fK b) :=
  E2_nonneg hr1 ht1 (fun θ hθ γ hγ => by
    simp only [fK]
    have g0 : 0 ≤ γ := le_trans hr0 hγ.1
    exact mul_nonneg g0 (le_min (le_trans ht0 hθ.1) (mul_nonneg g0 hb)))

set_option maxHeartbeats 1000000 in
lemma stripT {r t a : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht : t < 1 / 10 ^ 8)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmax : ∀ b, 0 ≤ b → b * E2 r t (fD b) ≤ a * E2 r t (fD a)) :
    E2 r t (fD a) * E2 r t (fK a) < 4 * E2 r t (fS a) * E2 r t (fM a) ∧
      0 < E2 r t (fM a) := by
  have ht1 : t < 1 := by linarith [show (1 : ℝ) / 10 ^ 8 < 1 by norm_num]
  have hu : 0 < 1 + r := by linarith
  obtain ⟨b0, hb0d⟩ : ∃ b0 : ℝ, b0 = 1 / (1 + r) := ⟨_, rfl⟩
  have hb0 : 0 < b0 := by rw [hb0d]; positivity
  have hb1 : b0 ≤ 1 := by rw [hb0d, div_le_one hu]; linarith
  have hb0u : b0 * (1 + r) = 1 := by rw [hb0d]; field_simp
  have tD := abs_le.1 (tvθ hr0.le hr1 ht0 ht1 (mD a) (bD a))
  have tD0 := abs_le.1 (tvθ hr0.le hr1 ht0 ht1 (mD b0) (bD b0))
  have tS := abs_le.1 (tvθ hr0.le hr1 ht0 ht1 (mS a) (bS ha0.le))
  have tM := abs_le.1 (tvθ hr0.le hr1 ht0 ht1 (mM a) (bM a))
  have tK := abs_le.1 (tvθ hr0.le hr1 ht0 ht1 (mK a) (bK ha0.le))
  rw [t0D hr0.le hr1 ha0.le ha1] at tD
  rw [t0D hr0.le hr1 hb0.le hb1] at tD0
  rw [t0S hr0.le hr1 ha0.le ha1] at tS
  rw [t0M hr0.le hr1 ha0.le ha1] at tM
  rw [t0K hr0.le hr1 ha0.le ha1] at tK
  -- location of the benchmark price
  have hloc := hmax b0 hb0.le
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = (1 + r) * a - 1 := ⟨_, rfl⟩
  have h1 : b0 * (1 - b0 * ((1 + r) / 2) - 2 * 1 * t) ≤ b0 * E2 r t (fD b0) :=
    mul_le_mul_of_nonneg_left (by linarith [tD0.1]) hb0.le
  have h2 : a * E2 r t (fD a) ≤ a * (1 - a * ((1 + r) / 2) + 2 * 1 * t) :=
    mul_le_mul_of_nonneg_left (by linarith [tD.2]) ha0.le
  have e1 : b0 * (1 - b0 * ((1 + r) / 2)) = b0 / 2 := by
    linear_combination (-b0 / 2) * hb0u
  have hX : b0 / 2 - a * (1 - a * ((1 + r) / 2)) ≤ 4 * t := by
    linarith [mul_le_mul_of_nonneg_right hb1 ht0, mul_le_mul_of_nonneg_right ha1 ht0]
  have e2 : d ^ 2 = 2 * (1 + r) * (b0 / 2 - a * (1 - a * ((1 + r) / 2))) := by
    rw [hdd]
    linear_combination (-1 : ℝ) * hb0u
  have hd2 : d ^ 2 ≤ 16 * t := by
    rw [e2]
    linarith [mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ 2 * (1 + r)),
      mul_le_mul_of_nonneg_right hr1 ht0]
  have hdl : -(1 / 1600) ≤ d := by nlinarith only [hd2, ht, ht0]
  have hdu : d ≤ 1 / 1600 := by nlinarith only [hd2, ht, ht0]
  -- the boundary margin
  obtain ⟨D0, hD0d⟩ : ∃ x : ℝ, x = 1 - a * ((1 + r) / 2) := ⟨_, rfl⟩
  obtain ⟨S0, hS0d⟩ : ∃ x : ℝ,
      x = (1 - 2 * a * ((1 + r) / 2) + a ^ 2 * ((1 + r + r ^ 2) / 3)) / 2 := ⟨_, rfl⟩
  obtain ⟨M0, hM0d⟩ : ∃ x : ℝ, x = (1 + r) / 2 - a * ((1 + r + r ^ 2) / 3) := ⟨_, rfl⟩
  obtain ⟨K0, hK0d⟩ : ∃ x : ℝ,
      x = a * ((1 + r + r ^ 2) / 3) - a ^ 2 * ((1 + r + r ^ 2 + r ^ 3) / 4) / 2 := ⟨_, rfl⟩
  rw [← hD0d] at tD
  rw [← hS0d] at tS
  rw [← hM0d] at tM
  rw [← hK0d] at tK
  obtain ⟨P1, hP1⟩ : ∃ x : ℝ,
      x = -(13 / 48 + 29 / 24 * r + 61 / 24 * r ^ 2 + 29 / 24 * r ^ 3 + 13 / 48 * r ^ 4) :=
    ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ x : ℝ,
      x = 7 / 16 + 49 / 24 * r + 61 / 24 * r ^ 2 + 49 / 24 * r ^ 3 + 7 / 16 * r ^ 4 := ⟨_, rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ x : ℝ,
      x = -(41 / 144 + 41 / 72 * r + 19 / 24 * r ^ 2 + 41 / 72 * r ^ 3 + 41 / 144 * r ^ 4) :=
    ⟨_, rfl⟩
  have hkey : (1 + r) ^ 3 * (4 * S0 * M0 - D0 * K0) =
      (1 + 26 * r + 18 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / 144 + d * P1 + d ^ 2 * P2 +
        d ^ 3 * P3 := by
    rw [hD0d, hS0d, hM0d, hK0d, hP1, hP2, hP3, hdd]
    ring
  have r2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
  have r3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0.le hr1
  have r4 : r ^ 4 ≤ 1 := pow_le_one₀ hr0.le hr1
  have r2' : 0 ≤ r ^ 2 := by positivity
  have r3' : 0 ≤ r ^ 3 := by positivity
  have r4' : 0 ≤ r ^ 4 := by positivity
  have hP1l : -(11 / 2) ≤ P1 := by rw [hP1]; linarith
  have hP1u : P1 ≤ 0 := by rw [hP1]; linarith
  have hP2l : 0 ≤ P2 := by rw [hP2]; linarith
  have hP3l : -(5 / 2) ≤ P3 := by rw [hP3]; linarith
  have hP3u : P3 ≤ 0 := by rw [hP3]; linarith
  have q1 : d * P1 ≥ -(11 / 3200) := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 1600 - d) (by linarith : (0 : ℝ) ≤ -P1)]
  have q2 : 0 ≤ d ^ 2 * P2 := mul_nonneg (sq_nonneg d) hP2l
  have hd2s : d ^ 2 ≤ (1 / 1600) ^ 2 := by linarith
  have q3a : -(5 / 2) * (1 / 1600) ^ 2 ≤ d ^ 2 * P3 := by
    linarith [mul_le_mul_of_nonneg_right hd2s (by linarith : (0 : ℝ) ≤ -P3)]
  have q3b : d ^ 2 * P3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg d) hP3u
  have q3 : d ^ 3 * P3 ≥ -(1 / 10 ^ 8) := by
    have e : d ^ 3 * P3 = d * (d ^ 2 * P3) := by ring
    rw [e]
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 1600 - d) (by linarith : (0 : ℝ) ≤ -(d ^ 2 * P3))]
  have hf0 : 1 / 144 ≤ (1 + 26 * r + 18 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / 144 := by linarith
  have hu3 : (1 + r) ^ 3 ≤ 8 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + r) (by linarith : 1 + r ≤ 2) 3
    norm_num at this
    linarith
  have hu3p : 0 < (1 + r) ^ 3 := by positivity
  have hF : 1 / 2560 ≤ 4 * S0 * M0 - D0 * K0 := by
    by_contra hc
    push_neg at hc
    linarith [mul_lt_mul_of_pos_left hc hu3p]
  have hM0 : 1 / 20 ≤ M0 := by
    have e : (1 + r) * M0 = (1 + 4 * r + r ^ 2 - 2 * d * (1 + r + r ^ 2)) / 6 := by
      rw [hM0d, hdd]; ring
    have hm : 1 / 7 ≤ (1 + r) * M0 := by
      rw [e]
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 1600 - d)
        (by positivity : (0 : ℝ) ≤ 1 + r + r ^ 2)]
    by_contra hc
    push_neg at hc
    linarith [mul_lt_mul_of_pos_left hc hu]
  -- actual values
  obtain ⟨D, hDd⟩ : ∃ x : ℝ, x = E2 r t (fD a) := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ x : ℝ, x = E2 r t (fS a) := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ x : ℝ, x = E2 r t (fM a) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = E2 r t (fK a) := ⟨_, rfl⟩
  rw [← hDd] at tD ⊢
  rw [← hSd] at tS ⊢
  rw [← hMd] at tM ⊢
  rw [← hKd] at tK ⊢
  have hDn : 0 ≤ D := hDd ▸ nn_D hr1 ht1.le
  have hSn : 0 ≤ S := hSd ▸ nn_S hr1 ht1.le
  have hKn : 0 ≤ K := hKd ▸ nn_K hr0.le hr1 ht0 ht1.le ha0.le
  have hD1 : D ≤ 1 := hDd ▸ E2_le1 hr0.le hr1 ht0 ht1.le (mD a) (bD a)
  have hS1 : S ≤ 1 := hSd ▸ E2_le1 hr0.le hr1 ht0 ht1.le (mS a) (bS ha0.le)
  have hM1 : M ≤ 1 := hMd ▸ E2_le1 hr0.le hr1 ht0 ht1.le (mM a) (bM a)
  have hK1 : K ≤ 1 := hKd ▸ E2_le1 hr0.le hr1 ht0 ht1.le (mK a) (bK ha0.le)
  have ht8 : t ≤ 1 / 10 ^ 8 := ht.le
  have hM0' : 0 ≤ M0 - 2 * t := by linarith
  have p1 : S * (M0 - 2 * t) ≤ S * M := mul_le_mul_of_nonneg_left (by linarith [tM.1]) hSn
  have p2 : (S0 - 2 * t) * (M0 - 2 * t) ≤ S * (M0 - 2 * t) :=
    mul_le_mul_of_nonneg_right (by linarith [tS.1]) hM0'
  have p3 : D * K ≤ D * (K0 + 2 * t) := mul_le_mul_of_nonneg_left (by linarith [tK.2]) hDn
  have p4 : D * (K0 + 2 * t) ≤ (D0 + 2 * t) * (K0 + 2 * t) :=
    mul_le_mul_of_nonneg_right (by linarith [tD.2]) (by linarith [tK.2])
  have e : 4 * ((S0 - 2 * t) * (M0 - 2 * t)) - (D0 + 2 * t) * (K0 + 2 * t) =
      (4 * S0 * M0 - D0 * K0) - t * (8 * S0 + 8 * M0 + 2 * D0 + 2 * K0) + 12 * t ^ 2 := by ring
  have hsum : t * (8 * S0 + 8 * M0 + 2 * D0 + 2 * K0) ≤ t * 21 :=
    mul_le_mul_of_nonneg_left (by linarith [tS.2, tM.2, tD.1, tK.1]) ht0
  constructor
  · linarith [sq_nonneg t]
  · linarith [tM.1]

set_option maxHeartbeats 1000000 in
lemma stripR {r t a : ℝ} (hr0 : 0 < r) (hr : r < 1 / 10 ^ 8) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmax : ∀ b, 0 ≤ b → b * E2 r t (fD b) ≤ a * E2 r t (fD a)) :
    E2 r t (fD a) * E2 r t (fK a) < 4 * E2 r t (fS a) * E2 r t (fM a) ∧
      0 < E2 r t (fM a) := by
  have hr1 : r < 1 := by linarith [show (1 : ℝ) / 10 ^ 8 < 1 by norm_num]
  have tDa := abs_le.1 (tvγ hr0.le hr1 ht0 ht1 (mD a) (bD a))
  have tD1 := abs_le.1 (tvγ hr0.le hr1 ht0 ht1 (mD 1) (bD 1))
  have tS1 := abs_le.1 (tvγ hr0.le hr1 ht0 ht1 (mS 1) (bS zero_le_one))
  have tM1 := abs_le.1 (tvγ hr0.le hr1 ht0 ht1 (mM 1) (bM 1))
  have tK1 := abs_le.1 (tvγ hr0.le hr1 ht0 ht1 (mK 1) (bK zero_le_one))
  rw [r0D1 ht0 ht1] at tD1
  rw [r0S1 ht0 ht1] at tS1
  rw [r0M1 ht0 ht1] at tM1
  rw [r0K1 ht0 ht1] at tK1
  have haD := r0Da ht0 ht1 ha0
  have hL4 := L4 ht0 ht1 ha0 ha1
  have hSm : E2 r t (fS 1) ≤ E2 r t (fS a) :=
    E2_mono hr1.le ht1 (niceq (mS 1) (bS zero_le_one) hr0.le ht0)
      (niceq (mS a) (bS ha0.le) hr0.le ht0) (fun θ _ γ hγ => by
        have g0 : 0 ≤ γ := le_trans hr0.le hγ.1
        simp only [fS]
        exact max_le_max (by linarith [mul_le_mul_of_nonneg_left ha1 g0]) le_rfl)
  have hMm : E2 r t (fM 1) ≤ E2 r t (fM a) :=
    E2_mono hr1.le ht1 (niceq (mM 1) (bM 1) hr0.le ht0)
      (niceq (mM a) (bM a) hr0.le ht0) (fun θ _ γ hγ => by
        have g0 : 0 ≤ γ := le_trans hr0.le hγ.1
        have := mul_le_mul_of_nonneg_left ha1 g0
        simp only [fM]
        split_ifs <;> linarith)
  have hKm : E2 r t (fK a) ≤ E2 r t (fK 1) :=
    E2_mono hr1.le ht1 (niceq (mK a) (bK ha0.le) hr0.le ht0)
      (niceq (mK 1) (bK zero_le_one) hr0.le ht0) (fun θ _ γ hγ => by
        have g0 : 0 ≤ γ := le_trans hr0.le hγ.1
        simp only [fK]
        exact mul_le_mul_of_nonneg_left
          (min_le_min le_rfl (by linarith [mul_le_mul_of_nonneg_left ha1 g0])) g0)
  have hloc := hmax 1 zero_le_one
  rw [one_mul] at hloc
  obtain ⟨D, hDd⟩ : ∃ x : ℝ, x = E2 r t (fD a) := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ x : ℝ, x = E2 r t (fS a) := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ x : ℝ, x = E2 r t (fM a) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = E2 r t (fK a) := ⟨_, rfl⟩
  rw [← hDd] at tDa hloc ⊢
  rw [← hSd] at hSm ⊢
  rw [← hMd] at hMm ⊢
  rw [← hKd] at hKm ⊢
  have hDn : 0 ≤ D := hDd ▸ nn_D hr1.le ht1
  have hSn : 0 ≤ S := hSd ▸ nn_S hr1.le ht1
  have hKn : 0 ≤ K := hKd ▸ nn_K hr0.le hr1.le ht0 ht1 ha0.le
  have hr8 : r ≤ 1 / 10 ^ 8 := hr.le
  have hDa_up : a * D ≤ (1 + t) / 2 - (1 - a) ^ 2 / 2 + 2 * r := by
    linarith [mul_le_mul_of_nonneg_left tDa.2 ha0.le, mul_nonneg (sub_nonneg.2 ha1) hr0.le]
  have hsq : (1 - a) ^ 2 ≤ 8 * r := by linarith [tD1.1]
  have h1a : 1 - a ≤ 1 / 3000 := by nlinarith only [hsq, hr8]
  have hDa' : a * D ≤ (1 + t) / 2 + 2 * r := by linarith [sq_nonneg (1 - a)]
  obtain ⟨Q, hQd⟩ : ∃ x : ℝ, x = (1 + t + t ^ 2) / 6 - 2 * r := ⟨_, rfl⟩
  obtain ⟨K1, hK1d⟩ : ∃ x : ℝ, x = (1 + t) / 4 - (1 + t + t ^ 2 + t ^ 3) / 24 := ⟨_, rfl⟩
  have hQ0 : 1 / 7 ≤ Q := by rw [hQd]; linarith [sq_nonneg t]
  have hQ1 : Q ≤ 1 / 2 := by rw [hQd]; linarith [sq_nonneg t, pow_le_one₀ (n := 2) ht0 ht1]
  have hK1u : K1 ≤ 1 := by rw [hK1d]; linarith [pow_nonneg ht0 2, pow_nonneg ht0 3]
  have hSQ : Q ≤ S := by rw [hQd]; linarith [tS1.1]
  have hMQ : Q ≤ M := by rw [hQd]; linarith [tM1.1]
  have hKK : K ≤ K1 + 2 * r := by rw [hK1d]; linarith [tK1.2]
  have hg : 4 * ((1 + t + t ^ 2) / 6) ^ 2 - (1 + t) / 2 * K1 =
      (1 + 2 * t + 36 * t ^ 2 + 38 * t ^ 3 + 19 * t ^ 4) / 144 := by rw [hK1d]; ring
  have hg1 : 1 / 144 ≤ 4 * ((1 + t + t ^ 2) / 6) ^ 2 - (1 + t) / 2 * K1 := by
    rw [hg]; linarith [pow_nonneg ht0 2, pow_nonneg ht0 3, pow_nonneg ht0 4]
  have p1 : a * D * K ≤ ((1 + t) / 2 + 2 * r) * K := mul_le_mul_of_nonneg_right hDa' hKn
  have p2 : ((1 + t) / 2 + 2 * r) * K ≤ ((1 + t) / 2 + 2 * r) * (K1 + 2 * r) :=
    mul_le_mul_of_nonneg_left hKK (by positivity)
  have p3 : Q * Q ≤ S * M := mul_le_mul hSQ hMQ (by linarith) hSn
  have p4 : a * (Q * Q) ≤ a * (S * M) := mul_le_mul_of_nonneg_left p3 ha0.le
  have p5 : (1 - a) * (Q * Q) ≤ (1 - a) * (1 / 4) :=
    mul_le_mul_of_nonneg_left (by nlinarith only [hQ0, hQ1]) (by linarith)
  have hS01 : (1 + t + t ^ 2) / 6 ≤ 1 / 2 := by linarith [pow_le_one₀ (n := 2) ht0 ht1]
  have hQs : 4 * (Q * Q) ≥ 4 * ((1 + t + t ^ 2) / 6) ^ 2 - 8 * r := by
    rw [hQd]; linarith [mul_le_mul_of_nonneg_left hS01 hr0.le, sq_nonneg r]
  have hmain : a * (D * K) < a * (4 * (S * M)) := by
    have : ((1 + t) / 2 + 2 * r) * (K1 + 2 * r) < 4 * (a * (Q * Q)) := by
      linarith [mul_le_mul_of_nonneg_left hK1u (by linarith : (0 : ℝ) ≤ 2 * r),
        mul_le_mul_of_nonneg_left ht1 hr0.le, mul_le_mul_of_nonneg_left hr8 hr0.le]
    linarith
  constructor
  · have := lt_of_mul_lt_mul_left hmain ha0.le
    linarith
  · linarith

theorem childNeg : ChildNeg := by
  refine ⟨1 / 10 ^ 8, by norm_num, ?_⟩
  intro r t hr0 hr1 ht0 ht1 hrt a v ha0 ha1 hamax hv0 hvmax
  have hamax' : ∀ b, 0 ≤ b → b * E2 r t (fD b) ≤ a * E2 r t (fD a) := fun b hb => by
    have h := hamax b hb
    rw [demand_one, demand_one] at h
    exact h
  have key : E2 r t (fD a) * E2 r t (fK a) < 4 * E2 r t (fS a) * E2 r t (fM a) ∧
      0 < E2 r t (fM a) := by
    rcases hrt with h | h
    · exact stripR hr0 h ht0 ht1 ha0 ha1 hamax'
    · exact stripT hr0 hr1 ht0 h ha0 ha1 hamax'
  obtain ⟨hDK, hM⟩ := key
  have hG2 : a / 2 * E2 r t (fM a) ≤ Gf r t a (a / 2) := by
    rw [← E2_mul]
    unfold Gf
    refine E2_mono hr1 ht1 (nice_mul_const _ (niceq (mM a) (bM a) hr0.le ht0))
      (nice_gp hr0 ht0 (by positivity)) (fun θ _ γ _ => ?_)
    simp only [fM]
    split_ifs with h
    · rw [max_eq_left h]
      apply le_max_of_le_left
      linarith
    · rw [mul_zero]
      exact le_max_right _ _
  have hGpos : 0 < Gf r t a (a / 2) := lt_of_lt_of_le (mul_pos (half_pos ha0) hM) hG2
  have hva : v < a := by
    by_contra h
    push_neg at h
    have := hvmax (a / 2) (by positivity)
    rw [Gf_zero hr0 hr1 ht1 h, mul_zero] at this
    nlinarith [mul_pos (half_pos ha0) hGpos]
  have hβ : Bf r t a v = (a - v) * E2 r t (fM a) := by
    rw [← E2_mul]
    unfold Bf
    apply E2_congr hr1 ht1
    intro θ _ γ hγ
    have g0 : 0 ≤ γ := le_trans hr0.le hγ.1
    simp only [fM]
    split_ifs with h
    · rw [max_eq_left h, max_eq_left (by nlinarith [mul_nonneg g0 (sub_nonneg.2 hva.le)])]
      ring
    · ring
  have hH : Hf r t a v ≤ (a - v) * E2 r t (fK a) := by
    rw [← E2_mul]
    unfold Hf
    refine E2_mono hr1 ht1 (nice_gp2 hr0 ht0 hv0)
      (nice_mul_const _ (niceq (mK a) (bK ha0.le) hr0.le ht0)) (fun θ hθ γ hγ => ?_)
    simp only [fK]
    have g0 : 0 ≤ γ := le_trans hr0.le hγ.1
    have θ0 : 0 ≤ θ := le_trans ht0 hθ.1
    have hm1 := le_max_left (θ - γ * a) 0
    have hm2 := le_max_right (θ - γ * a) 0
    have hgv := mul_nonneg g0 hv0
    have hav := mul_nonneg g0 (sub_nonneg.2 hva.le)
    have hg0 : 0 ≤ max (θ - γ * v - max (θ - γ * a) 0) 0 := le_max_right _ _
    have hg1 : max (θ - γ * v - max (θ - γ * a) 0) 0 ≤ γ * (a - v) :=
      max_le (by nlinarith) hav
    have hg2 : max (θ - γ * v - max (θ - γ * a) 0) 0 ≤ min θ (γ * a) :=
      le_min (max_le (by nlinarith) θ0) (by nlinarith)
    calc (max (θ - γ * v - max (θ - γ * a) 0) 0) ^ 2
        = max (θ - γ * v - max (θ - γ * a) 0) 0 * max (θ - γ * v - max (θ - γ * a) 0) 0 := by
          ring
      _ ≤ (γ * (a - v)) * min θ (γ * a) := mul_le_mul hg1 hg2 hg0 hav
      _ = (a - v) * (γ * min θ (γ * a)) := by ring
  rw [demand_one, csNA_one, hβ]
  show E2 r t (fD a) * Hf r t a v < 4 * E2 r t (fS a) * ((a - v) * E2 r t (fM a))
  have hD0 : 0 ≤ E2 r t (fD a) := nn_D hr1 ht1
  have hav : 0 < a - v := by linarith
  calc E2 r t (fD a) * Hf r t a v ≤ E2 r t (fD a) * ((a - v) * E2 r t (fK a)) :=
        mul_le_mul_of_nonneg_left hH hD0
    _ = (a - v) * (E2 r t (fD a) * E2 r t (fK a)) := by ring
    _ < (a - v) * (4 * E2 r t (fS a) * E2 r t (fM a)) := mul_lt_mul_of_pos_left hDK hav
    _ = 4 * E2 r t (fS a) * ((a - v) * E2 r t (fM a)) := by ring

/-! ## Part 8: Child A (unique benchmark price) (session 3) -/

lemma iθ {t x : ℝ} (ht : t < 1) (hx1 : x ≤ 1) :
    ∫ θ, (if 0 ≤ θ - x then (1 : ℝ) else 0) ∂(unifIcc t 1) = 1 - max (x - t) 0 / (1 - t) := by
  have h : unifIcc t 1 = (ENNReal.ofReal (1 - t))⁻¹ • volume.restrict (Set.Icc t 1) := by
    simp [unifIcc, ht]
  have hfun : (fun θ : ℝ => if 0 ≤ θ - x then (1 : ℝ) else 0) = (Set.Ici x).indicator 1 := by
    funext θ
    have e : (0 ≤ θ - x) ↔ x ≤ θ := by constructor <;> intro h <;> linarith
    simp only [Set.indicator_apply, Set.mem_Ici, Pi.one_apply, e]
  rw [hfun, h, integral_smul_measure, integral_indicator_one measurableSet_Ici, Measure.real,
    Measure.restrict_apply measurableSet_Ici]
  have hs : Set.Ici x ∩ Set.Icc t 1 = Set.Icc (max x t) 1 := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, max_le_iff]
    tauto
  have h1t : (1 - t) ≠ 0 := by linarith
  rw [hs, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [max_le hx1 ht.le] : (0 : ℝ) ≤ 1 - max x t),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - t), smul_eq_mul]
  rcases le_total x t with hxt | hxt
  · rw [max_eq_right hxt, max_eq_right (by linarith : x - t ≤ 0), inv_mul_cancel₀ h1t]
    simp
  · rw [max_eq_left hxt, max_eq_left (by linarith : (0 : ℝ) ≤ x - t), inv_mul_eq_div,
      eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h1t]
    ring

lemma iγ {r b θ : ℝ} (hr : r < 1) (hb : 0 < b) (hy : θ / b ≤ 1) :
    ∫ γ, (if 0 ≤ θ - γ * b then (1 : ℝ) else 0) ∂(unifIcc r 1) =
      max (θ / b - r) 0 / (1 - r) := by
  have h : unifIcc r 1 = (ENNReal.ofReal (1 - r))⁻¹ • volume.restrict (Set.Icc r 1) := by
    simp [unifIcc, hr]
  have hfun : (fun γ : ℝ => if 0 ≤ θ - γ * b then (1 : ℝ) else 0) =
      (Set.Iic (θ / b)).indicator 1 := by
    funext γ
    have e : (0 ≤ θ - γ * b) ↔ γ ≤ θ / b := by
      rw [le_div_iff₀ hb]; constructor <;> intro h <;> linarith
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply, e]
  rw [hfun, h, integral_smul_measure, integral_indicator_one measurableSet_Iic, Measure.real,
    Measure.restrict_apply measurableSet_Iic, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - r), smul_eq_mul]
  rcases le_total (θ / b) r with hyr | hyr
  · have hs : Set.Iic (θ / b) ∩ Set.Icc r 1 ⊆ {r} := by
      intro γ hγ
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc] at hγ
      simp only [Set.mem_singleton_iff]
      linarith [hγ.1, hγ.2.1]
    have h0 : volume (Set.Iic (θ / b) ∩ Set.Icc r 1) = 0 :=
      measure_mono_null hs (Real.volume_singleton)
    rw [h0, max_eq_right (by linarith)]
    simp
  · have hs : Set.Iic (θ / b) ∩ Set.Icc r 1 = Set.Icc r (θ / b) := by
      ext γ
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 hy⟩
    rw [hs, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), max_eq_left (by linarith),
      inv_mul_eq_div]

lemma E2_t1 (r : ℝ) (f : ℝ → ℝ → ℝ) : E2 r 1 f = ∫ γ, f 1 γ ∂(unifIcc r 1) := by
  unfold E2
  rw [show unifIcc 1 1 = Measure.dirac 1 by simp [unifIcc], integral_dirac]

lemma E2_r1 (t : ℝ) (f : ℝ → ℝ → ℝ) : E2 1 t f = ∫ θ, f θ 1 ∂(unifIcc t 1) := by
  unfold E2
  simp_rw [show unifIcc 1 1 = Measure.dirac 1 by simp [unifIcc], integral_dirac]

/-- Expected hinge `E (γ b - t)⁺` under `γ ~ U[r,1]`. -/
noncomputable def Lf (r t b : ℝ) : ℝ := ∫ γ, max (γ * b - t) 0 ∂(unifIcc r 1)
/-- `P(t ≤ γ a)` under `γ ~ U[r,1]`. -/
noncomputable def Pf (r t a : ℝ) : ℝ := ∫ γ, (if t ≤ γ * a then (1 : ℝ) else 0) ∂(unifIcc r 1)

lemma intL {r t c : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hc : 0 ≤ c) :
    Integrable (fun γ => max (γ * c - t) 0) (unifIcc r 1) :=
  int_bdd hr1 (C := c + |t|) (by fun_prop) (fun γ hγ => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by nlinarith [hγ.2, neg_abs_le t, le_trans hr0.le hγ.1])
      (by positivity))

lemma intP {r t a : ℝ} (hr1 : r ≤ 1) :
    Integrable (fun γ => if t ≤ γ * a then (1 : ℝ) else 0) (unifIcc r 1) :=
  int_bdd hr1 (C := 1)
    (Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
      measurable_const)
    (fun γ _ => by split_ifs <;> norm_num)

lemma D_formula {r t b : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : E2 r t (fD b) * (1 - t) = 1 - t - Lf r t b := by
  have := unif_prob hr1
  have h1t : (1 - t) ≠ 0 := by linarith
  rw [E2_swap hr1 ht1.le (niceq (mD b) (bD b) hr0.le ht0),
    integral_unifIcc_congr hr1 (g := fun γ => 1 - max (γ * b - t) 0 / (1 - t)) (fun γ hγ => by
      simp only [fD]
      rw [iθ ht1 (by nlinarith [hγ.2, le_trans hr0.le hγ.1])]),
    integral_sub (integrable_const 1) ((intL hr0 hr1 hb0).div_const _), integral_const,
    integral_div]
  unfold Lf
  simp only [probReal_univ, smul_eq_mul, mul_one]
  rw [sub_mul, div_mul_cancel₀ _ h1t, one_mul]

lemma L_sub {r t a b : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a) (hb : 0 ≤ b) :
    Lf r t a + (b - a) / a * (Lf r t a + t * Pf r t a) ≤ Lf r t b := by
  have := unif_prob hr1
  have I1 := intL (t := t) hr0 hr1 ha.le
  have IP := intP (t := t) (a := a) hr1
  have I2 : Integrable (fun γ => (b - a) / a *
      (max (γ * a - t) 0 + t * (if t ≤ γ * a then (1 : ℝ) else 0))) (unifIcc r 1) :=
    (I1.add (IP.const_mul t)).const_mul ((b - a) / a)
  have I3 : Integrable (fun γ => max (γ * a - t) 0 + (b - a) / a *
      (max (γ * a - t) 0 + t * (if t ≤ γ * a then (1 : ℝ) else 0))) (unifIcc r 1) :=
    I1.add I2
  have I4 : Integrable (fun γ => max (γ * a - t) 0 + t * (if t ≤ γ * a then (1 : ℝ) else 0))
      (unifIcc r 1) := I1.add (IP.const_mul t)
  have hint : ∫ γ, (max (γ * a - t) 0 + (b - a) / a *
      (max (γ * a - t) 0 + t * (if t ≤ γ * a then (1 : ℝ) else 0))) ∂(unifIcc r 1) =
      Lf r t a + (b - a) / a * (Lf r t a + t * Pf r t a) := by
    unfold Lf Pf
    rw [integral_add I1 I2, integral_const_mul, integral_add I1 (IP.const_mul t),
      integral_const_mul]
  rw [← hint]
  unfold Lf
  apply integral_mono I3 (intL hr0 hr1 hb)
  intro γ
  dsimp only
  split_ifs with h
  · rw [max_eq_left (by linarith)]
    have e : (b - a) / a * (γ * a - t + t * 1) = (b - a) * γ := by
      field_simp
      try ring
    rw [e]
    exact le_max_of_le_left (by nlinarith)
  · rw [max_eq_right (by linarith)]
    simp

/-- The finishing argument: a supergradient bound gives strict uniqueness. -/
lemma finishA {r t a : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hfoc : 2 * Lf r t a + t * Pf r t a = 1 - t)
    (hK : 0 < Lf r t a + t * Pf r t a) :
    ∀ b : ℝ, 0 ≤ b → b ≠ a → b * E2 r t (fD b) < a * E2 r t (fD a) := by
  have h1t : 0 < 1 - t := by linarith
  have hDa := D_formula hr0 hr1.le ht0 ht1 ha0.le ha1.le
  have key : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → b ≠ a → b * E2 r t (fD b) < a * E2 r t (fD a) := by
    intro b hb0 hb1 hba
    have hDb := D_formula hr0 hr1.le ht0 ht1 hb0 hb1
    have hs := mul_le_mul_of_nonneg_left (L_sub (t := t) hr0 hr1.le ha0 hb0) hb0
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (b - a) / a := ⟨_, rfl⟩
    rw [← hk] at hs
    have hka : k * a = b - a := by rw [hk]; field_simp
    have hne : a - b ≠ 0 := sub_ne_zero.2 (Ne.symm hba)
    have hsq : 0 < (a - b) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    have e1 : a * ((a - b) * (Lf r t a + t * Pf r t a) + b * k * (Lf r t a + t * Pf r t a)) =
        (Lf r t a + t * Pf r t a) * (a - b) ^ 2 := by
      linear_combination (b * (Lf r t a + t * Pf r t a)) * hka
    have e2 : 0 < (a - b) * (Lf r t a + t * Pf r t a) + b * k * (Lf r t a + t * Pf r t a) := by
      have := mul_pos hK hsq
      rw [← e1] at this
      exact pos_of_mul_pos_right this ha0.le
    have hb' : b * (E2 r t (fD b) * (1 - t)) = b * (1 - t - Lf r t b) := by rw [hDb]
    have ha' : a * (E2 r t (fD a) * (1 - t)) = a * (1 - t - Lf r t a) := by rw [hDa]
    have hf1 : a * (2 * Lf r t a + t * Pf r t a) = a * (1 - t) := by rw [hfoc]
    have hf2 : b * (2 * Lf r t a + t * Pf r t a) = b * (1 - t) := by rw [hfoc]
    have : b * E2 r t (fD b) * (1 - t) < a * E2 r t (fD a) * (1 - t) := by
      linarith
    exact lt_of_mul_lt_mul_right this h1t.le
  intro b hb0 hba
  rcases le_or_gt b 1 with hb1 | hb1
  · exact key b hb0 hb1 hba
  · have h1 := key 1 zero_le_one le_rfl (ne_of_gt ha1)
    rw [one_mul] at h1
    refine lt_of_le_of_lt ?_ h1
    -- b * D(b) ≤ D(1) for b ≥ 1
    have := unif_prob ht1.le
    have hb0' : 0 < b := by linarith
    unfold E2
    rw [← integral_const_mul,
      integral_unifIcc_congr ht1.le (f := fun θ => b * ∫ γ, fD b θ γ ∂(unifIcc r 1))
        (g := fun θ => max (θ - r * b) 0 / (1 - r)) (fun θ hθ => by
        simp only [fD]
        rw [iγ hr1 hb0' (by rw [div_le_one hb0']; linarith [hθ.2]), ← mul_div_assoc,
          mul_max_of_nonneg _ _ hb0'.le, mul_zero]
        congr 2
        rw [mul_sub]
        field_simp
        try ring),
      integral_unifIcc_congr ht1.le (f := fun θ => ∫ γ, fD 1 θ γ ∂(unifIcc r 1))
        (g := fun θ => max (θ - r) 0 / (1 - r)) (fun θ hθ => by
        simp only [fD]
        rw [iγ hr1 one_pos (by rw [div_one]; exact hθ.2), div_one])]
    apply integral_mono (int_bdd ht1.le (C := 1 / (1 - r)) (by fun_prop) (fun θ hθ => by
        rw [abs_of_nonneg (by apply div_nonneg (le_max_right _ _); linarith)]
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact max_le (by nlinarith [hθ.2]) zero_le_one))
      (int_bdd ht1.le (C := 1 / (1 - r)) (by fun_prop) (fun θ hθ => by
        rw [abs_of_nonneg (by apply div_nonneg (le_max_right _ _); linarith)]
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact max_le (by nlinarith [hθ.2]) zero_le_one))
    intro θ
    dsimp only
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact max_le_max (by nlinarith) le_rfl

lemma childA_gen {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ b : ℝ, 0 ≤ b → b ≠ a → b * E2 r t (fD b) < a * E2 r t (fD a) := by
  have := unif_prob hr1.le
  have h1r : 0 < 1 - r := by linarith
  have h1t : 0 < 1 - t := by linarith
  by_cases hreg : t * (1 + r) ≤ r
  · -- interior regime: a = 1/(1+r), no kink
    obtain ⟨a, had⟩ : ∃ a : ℝ, a = 1 / (1 + r) := ⟨_, rfl⟩
    have hau : a * (1 + r) = 1 := by rw [had]; field_simp
    have ha0 : 0 < a := by rw [had]; positivity
    have ha1 : a < 1 := by nlinarith
    have hra : t ≤ r * a := by nlinarith [mul_le_mul_of_nonneg_right hreg ha0.le]
    have hL : Lf r t a = 1 / 2 - t := by
      unfold Lf
      rw [integral_unifIcc_congr hr1.le (g := fun γ => -t + a * γ + 0 * γ ^ 2 + 0 * γ ^ 3)
        (fun γ hγ => by
          rw [max_eq_left (by nlinarith [hγ.1, mul_le_mul_of_nonneg_right hγ.1 ha0.le])]
          ring), unif_poly hr1.le]
      linear_combination (1 / 2 : ℝ) * hau
    have hP : Pf r t a = 1 := by
      unfold Pf
      rw [integral_unifIcc_congr hr1.le (g := fun γ => 1 + 0 * γ + 0 * γ ^ 2 + 0 * γ ^ 3)
        (fun γ hγ => by
          rw [if_pos (by nlinarith [hγ.1, mul_le_mul_of_nonneg_right hγ.1 ha0.le])]
          ring), unif_poly hr1.le]
      ring
    refine ⟨a, ha0, ha1.le, finishA hr0 hr1 ht0 ht1 ha0 ha1 ?_ ?_⟩
    · rw [hL, hP]; ring
    · rw [hL, hP]; linarith
  · -- kink regime: a = 1 - r (1 - t)
    push_neg at hreg
    obtain ⟨a, had⟩ : ∃ a : ℝ, a = 1 - r * (1 - t) := ⟨_, rfl⟩
    have ha1 : a < 1 := by rw [had]; nlinarith
    have hat : t < a := by rw [had]; nlinarith
    have ha0 : 0 < a := by linarith
    have hra : r * a ≤ t := by
      rw [had]
      nlinarith [mul_pos h1r (by linarith : (0 : ℝ) < t * (1 + r) - r)]
    obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = t / a := ⟨_, rfl⟩
    have hca : c * a = t := by rw [hcd]; field_simp
    have hrc : r ≤ c := by
      rw [hcd, le_div_iff₀ ha0]; linarith
    have hc1 : c ≤ 1 := by rw [hcd, div_le_one ha0]; linarith
    have hL : Lf r t a = a * (1 - c) ^ 2 / 2 / (1 - r) := by
      unfold Lf
      rw [unif_int hr1, split_at (f := fun γ => max (γ * a - t) 0) (by fun_prop) c,
        congr_poly (f := fun γ => max (γ * a - t) 0) hrc 0 0 0 0 (fun γ hγ => by
          show max (γ * a - t) 0 = _
          rw [max_eq_right (by nlinarith [hγ.2, mul_le_mul_of_nonneg_right hγ.2 ha0.le])]
          ring),
        congr_poly (f := fun γ => max (γ * a - t) 0) hc1 (-t) a 0 0 (fun γ hγ => by
          show max (γ * a - t) 0 = _
          rw [max_eq_left (by nlinarith [hγ.1, mul_le_mul_of_nonneg_right hγ.1 ha0.le])]
          ring)]
      unfold Fp
      rw [← hca]
      congr 1
      ring
    have hP : Pf r t a = (1 - c) / (1 - r) := by
      unfold Pf
      rw [integral_unifIcc_congr hr1.le (g := fun γ => if 0 ≤ γ - c then (1 : ℝ) else 0)
        (fun γ _ => by
          have e : (t ≤ γ * a) ↔ (0 ≤ γ - c) := by
            rw [← hca]; constructor <;> intro h <;> nlinarith
          simp only [e]),
        iθ hr1 hc1, max_eq_left (by linarith)]
      field_simp
      try ring
    refine ⟨a, ha0, ha1.le, finishA hr0 hr1 ht0 ht1 ha0 ha1 ?_ ?_⟩
    · rw [hL, hP]
      have e : 2 * (a * (1 - c) ^ 2 / 2 / (1 - r)) + t * ((1 - c) / (1 - r)) =
          (a * (1 - c) ^ 2 + t * (1 - c)) / (1 - r) := by ring
      have e2 : a * (1 - c) ^ 2 + t * (1 - c) = (1 - t) * (1 - r) := by
        linear_combination (c - 2) * hca + had
      rw [e, e2, mul_div_assoc, div_self h1r.ne', mul_one]
    · rw [hL, hP]
      have : 0 < 1 - c := by
        rw [hcd, sub_pos, div_lt_one ha0]; exact hat
      have h2 : 0 < a * (1 - c) ^ 2 / 2 / (1 - r) :=
        div_pos (div_pos (mul_pos ha0 (pow_pos this 2)) two_pos) h1r
      have h3 : 0 ≤ t * ((1 - c) / (1 - r)) := mul_nonneg ht0 (div_nonneg this.le h1r.le)
      linarith

lemma childA_t1 {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ b : ℝ, 0 ≤ b → b ≠ a → b * E2 r 1 (fD b) < a * E2 r 1 (fD a) := by
  have := unif_prob hr1
  have hD : ∀ b, 0 ≤ b → b ≤ 1 → E2 r 1 (fD b) = 1 := fun b hb0 hb1 => by
    rw [E2_t1, integral_unifIcc_congr hr1 (g := fun _ => (1 : ℝ)) (fun γ hγ => by
      simp only [fD]
      exact if_pos (by nlinarith [hγ.1, hγ.2, mul_le_mul hγ.2 hb1 hb0 zero_le_one]))]
    simp
  refine ⟨1, one_pos, le_rfl, fun b hb0 hba => ?_⟩
  rw [hD 1 zero_le_one le_rfl, mul_one]
  rcases lt_or_gt_of_ne hba with hb | hb
  · rw [hD b hb0 hb.le, mul_one]; exact hb
  · rcases hr1.lt_or_eq with hr | hr
    · rw [E2_t1]
      simp only [fD]
      rw [iγ hr (by linarith) (by rw [div_le_one (by linarith)]; linarith)]
      rcases le_total (1 / b - r) 0 with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_left h, ← mul_div_assoc, div_lt_one (by linarith)]
        have e : b * (1 / b - r) = 1 - r * b := by
          rw [mul_sub, mul_one_div_cancel (by linarith : (0 : ℝ) < b).ne']
          ring
        rw [e]
        nlinarith
    · subst hr
      rw [E2_t1, integral_unifIcc_congr le_rfl (g := fun _ => (0 : ℝ)) (fun γ hγ => by
        simp only [fD]
        exact if_neg (by nlinarith [hγ.1, hγ.2]))]
      simp

lemma childA_r1 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ b : ℝ, 0 ≤ b → b ≠ a → b * E2 1 t (fD b) < a * E2 1 t (fD a) := by
  have h1t : 0 < 1 - t := by linarith
  have hD : ∀ b, b ≤ 1 → E2 1 t (fD b) * (1 - t) = 1 - t - max (b - t) 0 := fun b hb1 => by
    rw [E2_r1]
    simp only [fD, one_mul]
    rw [iθ ht1 hb1]
    field_simp
  have hD0 : ∀ b, 1 < b → E2 1 t (fD b) = 0 := fun b hb => by
    have := unif_prob ht1.le
    rw [E2_r1, integral_unifIcc_congr ht1.le (g := fun _ => (0 : ℝ)) (fun θ hθ => by
      simp only [fD, one_mul]
      exact if_neg (by linarith [hθ.2]))]
    simp
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = max t (1 / 2) := ⟨_, rfl⟩
  have hat : t ≤ a := had ▸ le_max_left _ _
  have ha2 : 1 / 2 ≤ a := had ▸ le_max_right _ _
  have ha1 : a < 1 := had ▸ max_lt ht1 (by norm_num)
  have hcase : a = t ∨ a = 1 / 2 := by
    rw [had]; rcases le_total t (1 / 2) with h | h
    · right; exact max_eq_right h
    · left; exact max_eq_left h
  have hRa := hD a ha1.le
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ a - t)] at hRa
  have hRa' : a * (E2 1 t (fD a) * (1 - t)) = a * (1 - a) := by rw [hRa]; ring
  refine ⟨a, by linarith, ha1.le, fun b hb0 hba => ?_⟩
  rcases le_or_gt b 1 with hb1 | hb1
  · have hRb := hD b hb1
    apply lt_of_mul_lt_mul_right _ h1t.le
    rcases le_total b t with hbt | hbt
    · rw [max_eq_right (by linarith : b - t ≤ 0), sub_zero] at hRb
      have hRb' : b * (E2 1 t (fD b) * (1 - t)) = b * (1 - t) := by rw [hRb]
      have hbt' : b < a ∨ (b = t ∧ a = 1 / 2) := by
        rcases hcase with h | h
        · left; exact lt_of_le_of_ne (h ▸ hbt) hba
        · rcases lt_or_eq_of_le hbt with h' | h'
          · left; linarith
          · right; exact ⟨h', h⟩
      rcases hbt' with h | ⟨h1, h2⟩
      · rcases hcase with hc | hc
        · rw [hc] at hRa' h ⊢
          nlinarith [mul_lt_mul_of_pos_right h h1t]
        · rw [hc] at hRa' h ⊢
          nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - t ≤ 1 - b) hb0,
            mul_pos (by linarith : (0 : ℝ) < 1 / 2 - b) (by linarith : (0 : ℝ) < 1 / 2 - b)]
      · subst h1
        have : b ≠ 1 / 2 := h2 ▸ hba
        have hsq : 0 < (b - 1 / 2) ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 this)))
        rw [h2] at hRa'
        nlinarith
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ b - t)] at hRb
      have hRb' : b * (E2 1 t (fD b) * (1 - t)) = b * (1 - b) := by rw [hRb]; ring
      have hne : b - a ≠ 0 := sub_ne_zero.2 hba
      have hsq : 0 < (b - a) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      rcases hcase with h | h
      · have ht2 : 1 / 2 ≤ t := by rw [← h]; exact ha2
        rw [h] at hRa' hsq hba ⊢
        have hbt2 : t < b := lt_of_le_of_ne hbt (Ne.symm hba)
        nlinarith [mul_pos (by linarith : (0 : ℝ) < b - t) (by linarith : (0 : ℝ) < b + t - 1)]
      · rw [h] at hRa' hsq ⊢
        nlinarith
  · rw [hD0 b hb1, mul_zero]
    have : 0 < E2 1 t (fD a) := by
      have h3 : 0 < E2 1 t (fD a) * (1 - t) := by rw [hRa]; linarith
      exact pos_of_mul_pos_left h3 h1t.le
    positivity

theorem childA : ChildA := by
  intro r t hr0 hr1 ht0 ht1
  suffices h : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      ∀ b : ℝ, 0 ≤ b → b ≠ a → b * E2 r t (fD b) < a * E2 r t (fD a) by
    obtain ⟨a, h0, h1, h2⟩ := h
    refine ⟨a, h0, h1, fun b hb hba => ?_⟩
    rw [demand_one, demand_one]
    exact h2 b hb hba
  rcases ht1.lt_or_eq with ht1 | ht1
  · rcases hr1.lt_or_eq with hr1 | hr1
    · exact childA_gen hr0 hr1 ht0 ht1
    · subst hr1
      exact childA_r1 ht0 ht1
  · subst ht1
    exact childA_t1 hr0 hr1
/-! ## Part 9: Child V (session 4) -/

/-- `E[(θ - x)⁺]` for `θ ~ U[t,1]`. -/
noncomputable def hS (t x : ℝ) : ℝ := (1 + t) / 2 - x + (max (x - t) 0) ^ 2 / (2 * (1 - t))

/-- `P(θ ≥ x)` for `θ ~ U[t,1]`. -/
noncomputable def pS (t x : ℝ) : ℝ := 1 - max (x - t) 0 / (1 - t)

lemma iS {t x : ℝ} (ht1 : t ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ θ, max (θ - x) 0 ∂(unifIcc t 1) = hS t x := by
  rcases ht1.lt_or_eq with ht | ht
  · have h1t : (1 - t) ≠ 0 := by linarith
    rw [unif_int ht]
    unfold hS
    rcases le_total x t with hxt | hxt
    · rw [congr_poly (f := fun θ => max (θ - x) 0) ht.le (-x) 1 0 0 (fun θ hθ => by
        show max (θ - x) 0 = _
        rw [max_eq_left (by linarith [hθ.1])]; ring), max_eq_right (by linarith : x - t ≤ 0)]
      unfold Fp
      field_simp
      ring
    · rw [split_at (f := fun θ => max (θ - x) 0) (by fun_prop) x,
        congr_poly (f := fun θ => max (θ - x) 0) hxt 0 0 0 0 (fun θ hθ => by
          show max (θ - x) 0 = _
          rw [max_eq_right (by linarith [hθ.2])]; ring),
        congr_poly (f := fun θ => max (θ - x) 0) hx1 (-x) 1 0 0 (fun θ hθ => by
          show max (θ - x) 0 = _
          rw [max_eq_left (by linarith [hθ.1])]; ring),
        max_eq_left (by linarith : 0 ≤ x - t)]
      unfold Fp
      field_simp
      ring
  · subst ht
    rw [show unifIcc 1 1 = Measure.dirac 1 by simp [unifIcc], integral_dirac]
    unfold hS
    rw [max_eq_left (by linarith : 0 ≤ 1 - x), max_eq_right (by linarith : x - 1 ≤ 0)]
    norm_num

lemma gain_split {θ γ a w : ℝ} (hγ : 0 ≤ γ) :
    max (θ - γ * w - max (θ - γ * a) 0) 0 = max (θ - γ * min w a) 0 - max (θ - γ * a) 0 := by
  rcases le_total w a with hwa | hwa
  · rw [min_eq_left hwa]
    have := mul_le_mul_of_nonneg_left hwa hγ
    rcases le_total (θ - γ * a) 0 with h1 | h1
    · rw [max_eq_right h1, sub_zero, sub_zero]
    · rw [max_eq_left h1, max_eq_left (by linarith), max_eq_left (by linarith)]
  · rw [min_eq_right hwa, sub_self]
    have := mul_le_mul_of_nonneg_left hwa hγ
    apply max_eq_right
    rcases le_total (θ - γ * a) 0 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; linarith

lemma int_cont {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (unifIcc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact int_bdd hab hf.measurable (fun x hx => by rw [← Real.norm_eq_abs]; exact hC x hx)

lemma inner_gain {t a γ w : ℝ} (ht1 : t ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hw : 0 ≤ w)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ θ, max (θ - γ * w - max (θ - γ * a) 0) 0 ∂(unifIcc t 1) =
      hS t (γ * min w a) - hS t (γ * a) := by
  simp_rw [gain_split hγ0]
  rw [integral_sub (int_cont ht1 (by fun_prop)) (int_cont ht1 (by fun_prop)),
    iS ht1 (mul_nonneg hγ0 (le_min hw ha0))
      (mul_le_one₀ hγ1 (le_min hw ha0) ((min_le_right _ _).trans ha1)),
    iS ht1 (mul_nonneg hγ0 ha0) (mul_le_one₀ hγ1 ha0 ha1)]

noncomputable def Kf (t a γ w : ℝ) : ℝ := w * (hS t (γ * min w a) - hS t (γ * a))

noncomputable def kf (t a γ w : ℝ) : ℝ := w * (hS t (γ * w) - hS t (γ * a))

noncomputable def Phi (r t a w : ℝ) : ℝ := ∫ γ, Kf t a γ w ∂(unifIcc r 1)

lemma Gf_repr {r t a w : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hw : 0 ≤ w) : w * Gf r t a w = Phi r t a w := by
  unfold Gf Phi Kf
  rw [E2_swap hr1 ht1 (nice_gp hr0 ht0 hw), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [unif_ae hr1] with γ hγ
  rw [inner_gain ht1 (by linarith [hγ.1]) hγ.2 hw ha0.le ha1]

lemma hS_cont (t : ℝ) : Continuous (hS t) := by
  unfold hS; fun_prop

lemma dsq_ne (t y : ℝ) (hy : y ≠ t) :
    HasDerivAt (fun z : ℝ => (max (z - t) 0) ^ 2) (2 * max (y - t) 0) y := by
  rcases lt_or_gt_of_ne hy with h | h
  · have hev : (fun z : ℝ => (max (z - t) 0) ^ 2) =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with z hz
      rw [max_eq_right (by linarith [Set.mem_Iio.mp hz])]; ring
    rw [max_eq_right (by linarith : y - t ≤ 0), mul_zero]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
  · have hev : (fun z : ℝ => (max (z - t) 0) ^ 2) =ᶠ[nhds y] fun z => (z - t) ^ 2 := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      rw [max_eq_left (by linarith [Set.mem_Ioi.mp hz])]
    have h2 : HasDerivAt (fun z : ℝ => (z - t) ^ 2) (2 * (y - t)) y := by
      exact (((hasDerivAt_id' y).sub_const t).pow 2).congr_deriv (by norm_num)
    rw [max_eq_left (by linarith : 0 ≤ y - t)]
    exact h2.congr_of_eventuallyEq hev

lemma dsq (t y : ℝ) : HasDerivAt (fun z : ℝ => (max (z - t) 0) ^ 2) (2 * max (y - t) 0) y := by
  rcases eq_or_ne y t with h | h
  · subst h
    exact hasDerivAt_of_hasDerivAt_of_ne (fun z hz => dsq_ne _ z hz) (by fun_prop) (by fun_prop)
  · exact dsq_ne t y h

lemma hS_deriv (t x : ℝ) : HasDerivAt (hS t) (-pS t x) x := by
  have h1 : HasDerivAt (fun x : ℝ => (1 + t) / 2 - x) (-1) x := (hasDerivAt_id' x).const_sub _
  have := h1.add ((dsq t x).div_const (2 * (1 - t)))
  refine this.congr_deriv ?_
  unfold pS
  rw [mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  ring

lemma kf_deriv (t a γ w : ℝ) :
    HasDerivAt (kf t a γ) ((hS t (γ * w) - hS t (γ * a)) - γ * w * pS t (γ * w)) w := by
  have h1 : HasDerivAt (fun w : ℝ => γ * w) γ w := by
    simpa using (hasDerivAt_id w).const_mul γ
  have h2 := (hS_deriv t (γ * w)).comp w h1
  have h3 := (hasDerivAt_id' w).mul (h2.sub_const (hS t (γ * a)))
  refine h3.congr_deriv ?_
  show 1 * (hS t (γ * w) - hS t (γ * a)) + w * (-pS t (γ * w) * γ) = _
  ring

lemma algJ {t x1 x2 : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx1 : 0 ≤ x1) (h12 : x1 < x2)
    (hx2 : x2 ≤ 1 / 2) :
    hS t x2 - x2 * pS t x2 < hS t x1 - x1 * pS t x1 := by
  unfold hS pS
  rcases ht1.lt_or_eq with ht | ht
  · set k : ℝ := 1 / (1 - t) with hkdef
    have hk : k * (1 - t) = 1 := by rw [hkdef]; field_simp
    have hk0 : 0 < k := by rw [hkdef]; apply div_pos one_pos; linarith
    have r1 : ∀ e : ℝ, e ^ 2 / (2 * (1 - t)) = k * e ^ 2 / 2 := fun e => by
      rw [hkdef]; field_simp
    have r2 : ∀ e : ℝ, e / (1 - t) = k * e := fun e => by
      rw [hkdef]; field_simp
    simp only [r1, r2]
    rcases le_total x2 t with h2 | h2
    · rw [max_eq_right (by linarith : x2 - t ≤ 0), max_eq_right (by linarith : x1 - t ≤ 0)]
      nlinarith
    · rcases le_total x1 t with h1 | h1
      · rw [max_eq_left (by linarith : 0 ≤ x2 - t), max_eq_right (by linarith : x1 - t ≤ 0)]
        set u := x2 - t with hu
        set M := k * (u / 2 + x2) with hM
        have hM0 : 0 ≤ M := by rw [hM]; exact mul_nonneg hk0.le (by rw [hu]; linarith)
        have hM2 : M < 2 := by
          have : M = 2 - k * (2 - 3 / 2 * t - 3 / 2 * x2) := by
            rw [hM, hu]; linear_combination (2 : ℝ) * hk
          rw [this]
          have : 0 < k * (2 - 3 / 2 * t - 3 / 2 * x2) := mul_pos hk0 (by linarith)
          linarith
        have e1 : (1 + t) / 2 - x2 + k * u ^ 2 / 2 - x2 * (1 - k * u) =
            (1 + t) / 2 - 2 * x2 + u * M := by rw [hM]; ring
        rw [e1]
        have := mul_pos (by linarith : 0 < x2 - x1) (by linarith : 0 < 2 - M)
        have := mul_nonneg hM0 (by linarith : 0 ≤ x2 - x1 - u)
        nlinarith
      · rw [max_eq_left (by linarith : 0 ≤ x2 - t), max_eq_left (by linarith : 0 ≤ x1 - t)]
        have := mul_pos (mul_pos hk0 (by linarith : 0 < x2 - x1))
          (by linarith : 0 < 2 - 3 / 2 * (x1 + x2))
        nlinarith
  · subst ht
    rw [max_eq_right (by linarith : x2 - 1 ≤ 0), max_eq_right (by linarith : x1 - 1 ≤ 0)]
    norm_num
    linarith

lemma algN {t x c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 < x) (hcx : c < 2 * x)
    (hxc : x < c) (hc1 : c ≤ 1) :
    hS t x - hS t c - x * pS t x < 0 := by
  unfold hS pS
  rcases ht1.lt_or_eq with ht | ht
  · set k : ℝ := 1 / (1 - t) with hkdef
    have hk : k * (1 - t) = 1 := by rw [hkdef]; field_simp
    have hk0 : 0 < k := by rw [hkdef]; apply div_pos one_pos; linarith
    have r1 : ∀ e : ℝ, e ^ 2 / (2 * (1 - t)) = k * e ^ 2 / 2 := fun e => by
      rw [hkdef]; field_simp
    have r2 : ∀ e : ℝ, e / (1 - t) = k * e := fun e => by
      rw [hkdef]; field_simp
    simp only [r1, r2]
    rcases le_total c t with h2 | h2
    · rw [max_eq_right (by linarith : c - t ≤ 0), max_eq_right (by linarith : x - t ≤ 0)]
      nlinarith
    · rcases le_total x t with h1 | h1
      · rw [max_eq_left (by linarith : 0 ≤ c - t), max_eq_right (by linarith : x - t ≤ 0)]
        nlinarith [mul_nonneg hk0.le (sq_nonneg (c - t))]
      · rw [max_eq_left (by linarith : 0 ≤ c - t), max_eq_left (by linarith : 0 ≤ x - t)]
        have e1 : (1 + t) / 2 - x + k * (x - t) ^ 2 / 2 - ((1 + t) / 2 - c + k * (c - t) ^ 2 / 2)
            - x * (1 - k * (x - t)) = (c - 2 * x) * (k * (1 - x)) - k * (c - x) ^ 2 / 2 := by
          linear_combination (-(c - 2 * x)) * hk
        rw [e1]
        have := mul_pos (by linarith : 0 < 2 * x - c) (mul_pos hk0 (by linarith : 0 < 1 - x))
        nlinarith [mul_nonneg hk0.le (sq_nonneg (c - x))]
  · subst ht
    rw [max_eq_right (by linarith : x - 1 ≤ 0), max_eq_right (by linarith : c - 1 ≤ 0)]
    norm_num
    linarith

lemma kf_conc {t a γ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (ha1 : a ≤ 1) : StrictConcaveOn ℝ (Set.Icc 0 (a / 2)) (kf t a γ) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _)
    (fun w _ => (kf_deriv t a γ w).continuousAt.continuousWithinAt)
  rw [interior_Icc]
  intro x hx y hy hxy
  rw [(kf_deriv t a γ x).deriv, (kf_deriv t a γ y).deriv]
  have hb : γ * y ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hγ1 hy.1.le, hy.2]
  have := algJ ht0 ht1 (mul_nonneg hγ0.le hx.1.le) (mul_lt_mul_of_pos_left hxy hγ0) hb
  linarith

lemma kf_anti {t a γ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) : StrictAntiOn (kf t a γ) (Set.Icc (a / 2) a) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun w _ => (kf_deriv t a γ w).continuousAt.continuousWithinAt)
  rw [interior_Icc]
  intro w hw
  rw [(kf_deriv t a γ w).deriv]
  have hc1 : γ * a ≤ 1 := mul_le_one₀ hγ1 ha0.le ha1
  have h1 := mul_lt_mul_of_pos_left hw.1 hγ0
  have h2 := mul_lt_mul_of_pos_left hw.2 hγ0
  exact algN ht0 ht1 (mul_pos hγ0 (by linarith [hw.1])) (by linarith) h2 hc1

lemma Kf_eq {t a γ w : ℝ} (hw : w ≤ a) : Kf t a γ w = kf t a γ w := by
  unfold Kf kf; rw [min_eq_left hw]

lemma Kf_big {t a γ w : ℝ} (hw : a ≤ w) : Kf t a γ w = 0 := by
  unfold Kf; rw [min_eq_right hw, sub_self, mul_zero]

lemma Kf_cont (t a w : ℝ) : Continuous fun γ => Kf t a γ w := by
  unfold Kf
  exact continuous_const.mul (((hS_cont t).comp (continuous_id.mul continuous_const)).sub
    ((hS_cont t).comp (continuous_id.mul continuous_const)))

lemma Phi_cont {r t a : ℝ} (hr1 : r ≤ 1) : Continuous (Phi r t a) := by
  have hj : Continuous (Function.uncurry fun w γ => Kf t a γ w) := by
    have e : (Function.uncurry fun w γ => Kf t a γ w) =
        fun p : ℝ × ℝ => p.1 * (hS t (p.2 * min p.1 a) - hS t (p.2 * a)) := by
      funext p; rfl
    rw [e]
    exact continuous_fst.mul (((hS_cont t).comp (continuous_snd.mul
      (continuous_fst.min continuous_const))).sub
      ((hS_cont t).comp (continuous_snd.mul continuous_const)))
  rcases hr1.lt_or_eq with hr | hr
  · have e : Phi r t a = fun w => (∫ γ in r..1, Kf t a γ w) / (1 - r) := by
      funext w; unfold Phi; exact unif_int hr _
    rw [e]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hj r 1).div_const _
  · subst hr
    have e : Phi 1 t a = fun w => Kf t a 1 w := by
      funext w; unfold Phi
      rw [show unifIcc 1 1 = Measure.dirac 1 by simp [unifIcc], integral_dirac]
    rw [e]
    exact hj.comp (continuous_id.prodMk continuous_const)

lemma int_pos {r : ℝ} (hr1 : r ≤ 1) {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ γ ∈ Set.Icc r 1, 0 < f γ) : 0 < ∫ γ, f γ ∂(unifIcc r 1) := by
  rcases hr1.lt_or_eq with hr | hr
  · rw [unif_int hr]
    exact div_pos (intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable _ _)
      (fun x hx => h x (Set.Ioo_subset_Icc_self hx)) hr) (by linarith)
  · subst hr
    rw [show unifIcc 1 1 = Measure.dirac 1 by simp [unifIcc], integral_dirac]
    exact h 1 ⟨le_rfl, le_rfl⟩

lemma Phi_sub {r t a : ℝ} (hr1 : r ≤ 1) (x y : ℝ) :
    Phi r t a x - Phi r t a y = ∫ γ, (Kf t a γ x - Kf t a γ y) ∂(unifIcc r 1) := by
  unfold Phi
  rw [integral_sub (int_cont hr1 (Kf_cont t a x)) (int_cont hr1 (Kf_cont t a y))]

lemma Phi_mid {r t a : ℝ} (hr1 : r ≤ 1) (x y : ℝ) :
    Phi r t a ((1 / 2) * x + (1 / 2) * y) - (1 / 2) * Phi r t a x - (1 / 2) * Phi r t a y =
      ∫ γ, (Kf t a γ ((1 / 2) * x + (1 / 2) * y) - (1 / 2) * Kf t a γ x - (1 / 2) * Kf t a γ y)
        ∂(unifIcc r 1) := by
  unfold Phi
  have h1 : Integrable (fun γ => Kf t a γ ((1 / 2) * x + (1 / 2) * y)) (unifIcc r 1) :=
    int_cont hr1 (Kf_cont t a _)
  have h2 : Integrable (fun γ => (1 / 2) * Kf t a γ x) (unifIcc r 1) :=
    (int_cont hr1 (Kf_cont t a x)).const_mul _
  have h3 : Integrable (fun γ => (1 / 2) * Kf t a γ y) (unifIcc r 1) :=
    (int_cont hr1 (Kf_cont t a y)).const_mul _
  have h12 : Integrable (fun γ => Kf t a γ ((1 / 2) * x + (1 / 2) * y) - (1 / 2) * Kf t a γ x)
    (unifIcc r 1) := h1.sub h2
  rw [integral_sub h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul]

theorem childV : ChildV := by
  intro r t a hr0 hr1 ht0 ht1 ha0 ha1
  have hγ : ∀ γ ∈ Set.Icc r 1, 0 < γ ∧ γ ≤ 1 := fun γ hγ => ⟨by linarith [hγ.1], hγ.2⟩
  have hanti : ∀ γ ∈ Set.Icc r 1, ∀ w, a / 2 < w → w ≤ a → Kf t a γ w < Kf t a γ (a / 2) := by
    intro γ hγm w hw1 hw2
    rw [Kf_eq hw2, Kf_eq (by linarith)]
    exact kf_anti ht0 ht1 (hγ γ hγm).1 (hγ γ hγm).2 ha0 ha1 ⟨le_rfl, by linarith⟩
      ⟨hw1.le, hw2⟩ hw1
  have hpos : 0 < Phi r t a (a / 2) := by
    unfold Phi
    apply int_pos hr1 (Kf_cont t a _)
    intro γ hγm
    have := hanti γ hγm a (by linarith) le_rfl
    rw [Kf_big le_rfl] at this
    exact this
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (by linarith))
    (Phi_cont (t := t) (a := a) hr1).continuousOn (s := Set.Icc 0 (a / 2))
  have hmax' := isMaxOn_iff.mp hmax
  have hPa2 : Phi r t a (a / 2) ≤ Phi r t a v := hmax' _ ⟨by linarith, le_rfl⟩
  refine ⟨v, hv.1, fun w hw hwv => ?_⟩
  rw [Gf_repr hr0 hr1 ht0 ht1 ha0 ha1 hw, Gf_repr hr0 hr1 ht0 ht1 ha0 ha1 hv.1]
  rcases le_or_gt w (a / 2) with h1 | h1
  · by_contra hcon
    push_neg at hcon
    have hm : (1 / 2) * w + (1 / 2) * v ∈ Set.Icc 0 (a / 2) :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hlt := int_pos hr1 (f := fun γ => Kf t a γ ((1 / 2) * w + (1 / 2) * v) -
        (1 / 2) * Kf t a γ w - (1 / 2) * Kf t a γ v)
      (((Kf_cont t a _).sub (continuous_const.mul (Kf_cont t a w))).sub
        (continuous_const.mul (Kf_cont t a v)))
      (fun γ hγm => by
        have hc := (kf_conc ht0 ht1 (hγ γ hγm).1 (hγ γ hγm).2 ha1).2 ⟨hw, h1⟩ hv hwv
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        simp only [smul_eq_mul] at hc
        rw [Kf_eq (by linarith [hv.2, hm.2]), Kf_eq (by linarith [hv.2, hm.2]),
          Kf_eq (by linarith [hv.2, hm.2])]
        linarith)
    rw [← Phi_mid hr1] at hlt
    have := hmax' _ hm
    linarith
  · rcases le_or_gt w a with h2 | h2
    · have := int_pos hr1 (f := fun γ => Kf t a γ (a / 2) - Kf t a γ w)
        ((Kf_cont t a _).sub (Kf_cont t a w)) (fun γ hγm => by
          have := hanti γ hγm w h1 h2
          linarith)
      rw [← Phi_sub hr1] at this
      linarith
    · have : Phi r t a w = 0 := by
        unfold Phi
        simp_rw [Kf_big h2.le]
        simp
      linarith

end AdBlocking.Surplus.F55

open AdBlocking.Surplus in
theorem solution :
    (∃ ε : ℝ, 0 < ε ∧ ∀ pa c r t : ℝ, Standing pa c r t →
      (r < ε ∨ t < ε) →
      ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
        ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
          IsBenchEq pa c r t Asel qN →
          IsABEq pa c r t κbar Asel Vsel qA →
          csAB r t κbar qA (Asel qA) (Vsel qA) <
            csNA r t qN (Asel qN)) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ pa c r t : ℝ, Standing pa c r t →
      1 - δ < r → 1 - δ < t →
      ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
        ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
          IsBenchEq pa c r t Asel qN →
          IsABEq pa c r t κbar Asel Vsel qA →
          csNA r t qN (Asel qN) <
            csAB r t κbar qA (Asel qA) (Vsel qA)) := by
  exact AdBlocking.Surplus.F55.glue AdBlocking.Surplus.F55.childA AdBlocking.Surplus.F55.childV
    AdBlocking.Surplus.F55.childNeg AdBlocking.Surplus.F55.childPos
