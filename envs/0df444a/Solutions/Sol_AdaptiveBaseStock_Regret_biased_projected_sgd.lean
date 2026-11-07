-- Prove2me | solution 1 for AdaptiveBaseStock.Regret.biased_projected_sgd
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:09:58.444737+00:00
-- url     : https://prove2.me/submissions/0623f615-688e-4cbb-8520-06ce785b79a9

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ABSAux11

/-- `Σ_{t<T} 1/(t+1)^α ≤ T^{1-α}/(1-α)`. -/
lemma sum_inv_rpow_le (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ α ≤ (T : ℝ) ^ (1 - α) / (1 - α) := by
  have h1α : 0 < 1 - α := by linarith
  induction T with
  | zero => simp [Real.zero_rpow (ne_of_gt h1α)]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    -- Bernoulli: T^{1-α} ≤ (T+1)^{1-α} - (1-α) (T+1)^{-α}
    have hb : (T : ℝ) ^ (1 - α) ≤ ((T : ℝ) + 1) ^ (1 - α) - (1 - α) / ((T : ℝ) + 1) ^ α := by
      have hs : (-1 : ℝ) ≤ -1 / ((T : ℝ) + 1) := by
        rw [le_div_iff₀ hT1]; have : (0 : ℝ) ≤ T := by positivity
        linarith
      have hbern := rpow_one_add_le_one_add_mul_self hs h1α.le (by linarith : 1 - α ≤ 1)
      have hTeq : (T : ℝ) = ((T : ℝ) + 1) * (1 + -1 / ((T : ℝ) + 1)) := by
        field_simp; ring
      have hpow : (T : ℝ) ^ (1 - α) = ((T : ℝ) + 1) ^ (1 - α) * (1 + -1 / ((T : ℝ) + 1)) ^ (1 - α) := by
        conv_lhs => rw [hTeq]
        rw [Real.mul_rpow hT1.le]
        have : (0 : ℝ) ≤ 1 + -1 / ((T : ℝ) + 1) := by linarith
        exact this
      have hpos : 0 ≤ ((T : ℝ) + 1) ^ (1 - α) := Real.rpow_nonneg hT1.le _
      have hsub : ((T : ℝ) + 1) ^ (1 - α) / ((T : ℝ) + 1) = 1 / ((T : ℝ) + 1) ^ α := by
        rw [Real.rpow_sub hT1, Real.rpow_one]
        have : 0 < ((T : ℝ) + 1) ^ α := Real.rpow_pos_of_pos hT1 α
        field_simp
      rw [hpow]
      calc ((T : ℝ) + 1) ^ (1 - α) * (1 + -1 / ((T : ℝ) + 1)) ^ (1 - α)
          ≤ ((T : ℝ) + 1) ^ (1 - α) * (1 + (1 - α) * (-1 / ((T : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hbern hpos
        _ = ((T : ℝ) + 1) ^ (1 - α) - (1 - α) * (((T : ℝ) + 1) ^ (1 - α) / ((T : ℝ) + 1)) := by
            ring
        _ = _ := by rw [hsub]; ring
    have : ((T : ℝ) ^ (1 - α)) / (1 - α) + 1 / ((T : ℝ) + 1) ^ α
        ≤ (((T + 1 : ℕ) : ℝ)) ^ (1 - α) / (1 - α) := by
      push_cast
      rw [div_add' _ _ _ (ne_of_gt h1α), div_le_div_iff_of_pos_right h1α]
      have : (1 - α) / ((T : ℝ) + 1) ^ α = 1 / ((T : ℝ) + 1) ^ α * (1 - α) := by ring
      linarith
    linarith

/-- Abel summation bound: with nondecreasing nonnegative weights and `0 ≤ a ≤ A`. -/
lemma abel_bound (w a : ℕ → ℝ) (A : ℝ) (hw : Monotone w) (hw0 : ∀ t, 0 ≤ w t)
    (haA : ∀ t, a t ≤ A) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), w t * (a t - a (t + 1)) ≤ w T * (A - a (T + 1)) := by
  induction T with
  | zero => simp; exact mul_le_mul_of_nonneg_left (by linarith [haA 0]) (hw0 0)
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h1 : w T * (A - a (T + 1)) ≤ w (T + 1) * (A - a (T + 1)) :=
      mul_le_mul_of_nonneg_right (hw (Nat.le_succ T)) (by linarith [haA (T + 1)])
    nlinarith

/-- Projection onto `[m, M]` is 1-Lipschitz and fixes `z ∈ [m, M]`. -/
lemma proj_dist (m M y z : ℝ) (hz : z ∈ Set.Icc m M) :
    |max m (min y M) - z| ≤ |y - z| := by
  obtain ⟨h1, h2⟩ := hz
  rw [abs_le]; constructor
  · rcases le_total y M with h | h
    · rw [min_eq_left h]
      rcases le_total m y with h' | h'
      · rw [max_eq_right h']; linarith [neg_abs_le (y - z)]
      · rw [max_eq_left h']
        have : y - z ≤ 0 := by linarith
        rw [abs_of_nonpos this]; linarith
    · rw [min_eq_right h, max_eq_right (by linarith)]; linarith [abs_nonneg (y - z)]
  · rcases le_total y M with h | h
    · rw [min_eq_left h]
      rcases le_total m y with h' | h'
      · rw [max_eq_right h']; linarith [le_abs_self (y - z)]
      · rw [max_eq_left h']
        have : y - z ≤ 0 := by linarith
        linarith [abs_nonneg (y - z), neg_abs_le (y - z)]
    · rw [min_eq_right h, max_eq_right (by linarith)]; linarith [le_abs_self (y - z)]


lemma convex_grad_ineq (m M : ℝ) (Φ Φ' : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc m M) Φ)
    (hderiv : ∀ z ∈ Set.Icc m M, HasDerivWithinAt Φ (Φ' z) (Set.Icc m M) z)
    (z zs : ℝ) (hz : z ∈ Set.Icc m M) (hzs : zs ∈ Set.Icc m M) :
    Φ z - Φ zs ≤ Φ' z * (z - zs) := by
  rcases lt_trichotomy zs z with h | h | h
  · have := hconv.slope_le_of_hasDerivWithinAt hzs hz h (hderiv z hz)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hconv.le_slope_of_hasDerivWithinAt hz hzs h (hderiv z hz)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

lemma deriv_mono (m M : ℝ) (Φ Φ' : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc m M) Φ)
    (hderiv : ∀ z ∈ Set.Icc m M, HasDerivWithinAt Φ (Φ' z) (Set.Icc m M) z) (hmM : m ≤ M) :
    Monotone (fun z => Φ' (max m (min z M))) := by
  intro z1 z2 hz
  have h1 : max m (min z1 M) ∈ Set.Icc m M := ⟨le_max_left _ _, max_le hmM (min_le_right _ _)⟩
  have h2 : max m (min z2 M) ∈ Set.Icc m M := ⟨le_max_left _ _, max_le hmM (min_le_right _ _)⟩
  have hle : max m (min z1 M) ≤ max m (min z2 M) := max_le_max le_rfl (min_le_min hz le_rfl)
  rcases eq_or_lt_of_le hle with he | hlt
  · simp only; rw [he]
  · simp only
    exact (hconv.le_slope_of_hasDerivWithinAt h1 h2 hlt (hderiv _ h1)).trans
      (hconv.slope_le_of_hasDerivWithinAt h1 h2 hlt (hderiv _ h2))

end ABSAux11

open ABSAux11 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (m M : ℝ) (hmM : m ≤ M) (Φ Φ' : ℝ → ℝ)
    (hconv : ConvexOn ℝ (Set.Icc m M) Φ)
    (hderiv : ∀ z ∈ Set.Icc m M, HasDerivWithinAt Φ (Φ' z) (Set.Icc m M) z)
    (zstar : ℝ) (hzstar : zstar ∈ Set.Icc m M) (hmin : IsMinOn Φ (Set.Icc m M) zstar)
    (Bbar ζ α : ℝ) (hB : 0 < Bbar) (hζ : 0 < ζ) (hα0 : 0 < α) (hα1 : α < 1)
    (Z H : ℕ → Ω → ℝ)
    (hZ0 : ∀ ω, Z 0 ω ∈ Set.Icc m M)
    (hZadapt : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hHmeas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (H t))
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (hHbound : ∀ t, ∫ ω, H t ω ^ 2 ∂P ≤ Bbar ^ 2)
    (hrec : ∀ t ω, Z (t + 1) ω =
      max m (min (Z t ω - ζ * (M - m) / (Bbar * ((t : ℝ) + 1) ^ α) * H t ω) M))
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, ∫ ω, (Φ (Z t ω) - Φ zstar) ∂P
      ≤ (M - m) * (Bbar * ((T : ℝ) ^ α / (2 * ζ) + ζ * (T : ℝ) ^ (1 - α) / (2 * (1 - α)))
          + ∑ t ∈ Finset.range T, ∫ ω, |P[H t | ℱ t] ω - Φ' (Z t ω)| ∂P) := by
  have hZb : ∀ t ω, Z t ω ∈ Set.Icc m M := by
    intro t ω
    induction t with
    | zero => exact hZ0 ω
    | succ t _ => rw [hrec]; exact ⟨le_max_left _ _, max_le hmM (min_le_right _ _)⟩
  rcases eq_or_lt_of_le hmM with hEq | hlt
  · -- degenerate interval
    have hZ : ∀ t ω, Z t ω = zstar := by
      intro t ω
      have h1 := hZb t ω; have h2 := hzstar
      rw [← hEq] at h1 h2
      exact (le_antisymm h1.2 h1.1).trans (le_antisymm h2.2 h2.1).symm
    have hl : ∑ t ∈ Finset.range T, ∫ ω, (Φ (Z t ω) - Φ zstar) ∂P = 0 := by simp [hZ]
    rw [hl, ← hEq]; simp
  -- main case
  have hMm : 0 < M - m := by linarith
  set ε : ℕ → ℝ := fun t => ζ * (M - m) / (Bbar * ((t : ℝ) + 1) ^ α) with hε
  have hεpos : ∀ t, 0 < ε t := fun t => by
    have : 0 < ((t : ℝ) + 1) ^ α := Real.rpow_pos_of_pos (by positivity) α
    simp only [hε]; positivity
  set w : ℕ → ℝ := fun t => 1 / (2 * ε t) with hw
  have hZm : ∀ t, Measurable (Z t) := fun t => ((hZadapt t).mono (ℱ.le t)).measurable
  have hbdd : ∀ {f : Ω → ℝ} (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → Integrable f P :=
    fun C hf hC => Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hC ω))
  have hδb : ∀ t ω, |Z t ω - zstar| ≤ M - m := by
    intro t ω; obtain ⟨a1, a2⟩ := hZb t ω; obtain ⟨b1, b2⟩ := hzstar
    rw [abs_le]; constructor <;> linarith
  have hδm : ∀ t, Measurable (fun ω => Z t ω - zstar) := fun t => (hZm t).sub measurable_const
  have hδi : ∀ t, Integrable (fun ω => Z t ω - zstar) P := fun t => hbdd _ (hδm t) (hδb t)
  have hδ2i : ∀ t, Integrable (fun ω => (Z t ω - zstar) ^ 2) P := fun t =>
    hbdd ((M - m) ^ 2) ((hδm t).pow_const 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hδb t ω) 2)
  have hHi : ∀ t, Integrable (H t) P := fun t => (hH2 t).integrable one_le_two
  have hH2i : ∀ t, Integrable (fun ω => H t ω ^ 2) P := fun t => (hH2 t).integrable_sq
  have hHδi : ∀ t, Integrable (fun ω => (Z t ω - zstar) * H t ω) P := fun t =>
    (hHi t).bdd_mul (hδm t).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hδb t ω))
  -- derivative composed with Z
  have hΦ'mono := deriv_mono m M Φ Φ' hconv hderiv hmM
  have hproj : ∀ t ω, max m (min (Z t ω) M) = Z t ω := fun t ω => by
    obtain ⟨a1, a2⟩ := hZb t ω; rw [min_eq_left a2, max_eq_right a1]
  have hΦ'Zm : ∀ t, Measurable (fun ω => Φ' (Z t ω)) := by
    intro t
    have := hΦ'mono.measurable.comp (hZm t)
    convert this using 1; funext ω; simp [Function.comp, hproj]
  have hΦ'b : ∀ t ω, |Φ' (Z t ω)| ≤ |Φ' m| + |Φ' M| := by
    intro t ω
    have hl := hΦ'mono (show m ≤ Z t ω from (hZb t ω).1)
    have hu := hΦ'mono (show Z t ω ≤ M from (hZb t ω).2)
    simp only [hproj] at hl hu
    rw [min_eq_left hmM, max_eq_left le_rfl] at hl
    rw [min_eq_left le_rfl, max_eq_right hmM] at hu
    rw [abs_le]; constructor
    · linarith [neg_abs_le (Φ' m), abs_nonneg (Φ' M)]
    · linarith [le_abs_self (Φ' M), abs_nonneg (Φ' m)]
  have hΦ'δi : ∀ t, Integrable (fun ω => Φ' (Z t ω) * (Z t ω - zstar)) P := fun t =>
    (hδi t).bdd_mul (hΦ'Zm t).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hΦ'b t ω))
  -- Φ composed with Z
  have hcont : ContinuousOn Φ (Set.Icc m M) := fun z hz => (hderiv z hz).continuousWithinAt
  have hΦc : Continuous (fun z => Φ (max m (min z M))) :=
    hcont.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      (fun z => ⟨le_max_left _ _, max_le hmM (min_le_right _ _)⟩)
  have hfm : ∀ t, Measurable (fun ω => Φ (Z t ω) - Φ zstar) := by
    intro t
    have := (hΦc.measurable.comp (hZm t)).sub (measurable_const (a := Φ zstar))
    convert this using 1; funext ω; simp [Function.comp, hproj]
  have hfb : ∀ t ω, |Φ (Z t ω) - Φ zstar| ≤ max (Φ m) (Φ M) - Φ zstar := by
    intro t ω
    have hseg : Z t ω ∈ segment ℝ m M := by rw [segment_eq_Icc hmM]; exact hZb t ω
    have hup := hconv.le_on_segment ⟨le_rfl, hmM⟩ ⟨hmM, le_rfl⟩ hseg
    have hlo := hmin (hZb t ω)
    simp only [Set.mem_ofPred_eq] at hlo
    rw [abs_of_nonneg (by linarith)]; linarith
  have hfi : ∀ t, Integrable (fun ω => Φ (Z t ω) - Φ zstar) P := fun t => hbdd _ (hfm t) (hfb t)
  -- conditional expectations
  set G : ℕ → Ω → ℝ := fun t => P[H t | ℱ t] with hG
  have hGi : ∀ t, Integrable (G t) P := fun t => integrable_condExp
  have hGδ : ∀ t, ∫ ω, (Z t ω - zstar) * H t ω ∂P = ∫ ω, (Z t ω - zstar) * G t ω ∂P := by
    intro t
    have hsm : StronglyMeasurable[ℱ t] (fun ω => Z t ω - zstar) :=
      (hZadapt t).sub stronglyMeasurable_const
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := P) hsm (hHδi t) (hHi t)
    rw [← integral_condExp (ℱ.le t)]
    exact integral_congr_ae hpull
  have hGδi : ∀ t, Integrable (fun ω => (Z t ω - zstar) * G t ω) P := fun t =>
    (hGi t).bdd_mul (hδm t).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hδb t ω))
  have hηi : ∀ t, Integrable (fun ω => G t ω - Φ' (Z t ω)) P := fun t =>
    (hGi t).sub (hbdd _ (hΦ'Zm t) (hΦ'b t))
  have hηδi : ∀ t, Integrable (fun ω => (G t ω - Φ' (Z t ω)) * (Z t ω - zstar)) P := fun t =>
    (hηi t).mul_bdd (hδm t).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hδb t ω))
  -- per-step bound
  have key : ∀ t, ∫ ω, (Φ (Z t ω) - Φ zstar) ∂P ≤
      w t * (∫ ω, (Z t ω - zstar) ^ 2 ∂P - ∫ ω, (Z (t + 1) ω - zstar) ^ 2 ∂P)
        + ε t / 2 * Bbar ^ 2 + (M - m) * ∫ ω, |G t ω - Φ' (Z t ω)| ∂P := by
    intro t
    have s1 : ∫ ω, (Φ (Z t ω) - Φ zstar) ∂P ≤ ∫ ω, Φ' (Z t ω) * (Z t ω - zstar) ∂P :=
      integral_mono (hfi t) (hΦ'δi t)
        (fun ω => convex_grad_ineq m M Φ Φ' hconv hderiv _ _ (hZb t ω) hzstar)
    have s2 : ∫ ω, Φ' (Z t ω) * (Z t ω - zstar) ∂P =
        ∫ ω, (Z t ω - zstar) * G t ω ∂P - ∫ ω, (G t ω - Φ' (Z t ω)) * (Z t ω - zstar) ∂P := by
      rw [← integral_sub (hGδi t) (hηδi t)]
      congr 1; funext ω; ring
    have s3 : -∫ ω, (G t ω - Φ' (Z t ω)) * (Z t ω - zstar) ∂P ≤
        (M - m) * ∫ ω, |G t ω - Φ' (Z t ω)| ∂P := by
      rw [← integral_neg, ← integral_const_mul]
      refine integral_mono (hηδi t).neg ((hηi t).abs.const_mul _) (fun ω => ?_)
      simp only
      have h1 := neg_abs_le ((G t ω - Φ' (Z t ω)) * (Z t ω - zstar))
      rw [abs_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left (hδb t ω) (abs_nonneg (G t ω - Φ' (Z t ω)))
      linarith
    have s4 : ∫ ω, (Z t ω - zstar) * H t ω ∂P ≤
        ∫ ω, (w t * ((Z t ω - zstar) ^ 2 - (Z (t + 1) ω - zstar) ^ 2) + ε t / 2 * H t ω ^ 2) ∂P := by
      refine integral_mono (hHδi t) ((((hδ2i t).sub (hδ2i (t + 1))).const_mul _).add
        ((hH2i t).const_mul _)) (fun ω => ?_)
      simp only
      have hp := proj_dist m M (Z t ω - ε t * H t ω) zstar hzstar
      rw [← hrec] at hp
      have hsq : (Z (t + 1) ω - zstar) ^ 2 ≤ (Z t ω - ε t * H t ω - zstar) ^ 2 := by
        rw [← sq_abs, ← sq_abs (Z t ω - ε t * H t ω - zstar)]
        exact pow_le_pow_left₀ (abs_nonneg _) hp 2
      have hwε : w t * (2 * ε t) = 1 := by
        simp only [hw]; field_simp [ne_of_gt (hεpos t)]
      have hw0 : 0 ≤ w t := by simp only [hw]; have := hεpos t; positivity
      have hid : w t * ((Z t ω - zstar) ^ 2 - (Z (t + 1) ω - zstar) ^ 2) + ε t / 2 * H t ω ^ 2
          - (Z t ω - zstar) * H t ω
          = w t * ((Z t ω - ε t * H t ω - zstar) ^ 2 - (Z (t + 1) ω - zstar) ^ 2) := by
        have : ε t / 2 = w t * (ε t) ^ 2 := by
          have := hεpos t; simp only [hw]; field_simp
        rw [this]
        linear_combination (Z t ω - zstar) * H t ω * hwε
      have : 0 ≤ w t * ((Z t ω - ε t * H t ω - zstar) ^ 2 - (Z (t + 1) ω - zstar) ^ 2) :=
        mul_nonneg hw0 (by linarith)
      linarith
    have s5 : ∫ ω, (w t * ((Z t ω - zstar) ^ 2 - (Z (t + 1) ω - zstar) ^ 2)
        + ε t / 2 * H t ω ^ 2) ∂P
        = w t * (∫ ω, (Z t ω - zstar) ^ 2 ∂P - ∫ ω, (Z (t + 1) ω - zstar) ^ 2 ∂P)
          + ε t / 2 * ∫ ω, H t ω ^ 2 ∂P := by
      have i1 : Integrable (fun ω => w t * ((Z t ω - zstar) ^ 2 - (Z (t + 1) ω - zstar) ^ 2)) P :=
        ((hδ2i t).sub (hδ2i (t + 1))).const_mul _
      have i2 : Integrable (fun ω => ε t / 2 * H t ω ^ 2) P := (hH2i t).const_mul _
      have i3 : Integrable (fun ω => (Z t ω - zstar) ^ 2 - (Z (t + 1) ω - zstar) ^ 2) P :=
        (hδ2i t).sub (hδ2i (t + 1))
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_sub (hδ2i t) (hδ2i (t + 1))]
    have s6 : ε t / 2 * ∫ ω, H t ω ^ 2 ∂P ≤ ε t / 2 * Bbar ^ 2 :=
      mul_le_mul_of_nonneg_left (hHbound t) (by have := hεpos t; positivity)
    linarith [hGδ t]
  -- summation
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range (T' + 1)) => key t)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  -- telescoping part
  set a : ℕ → ℝ := fun t => ∫ ω, (Z t ω - zstar) ^ 2 ∂P with ha
  have haA : ∀ t, a t ≤ (M - m) ^ 2 := by
    intro t
    calc a t ≤ ∫ _ω, (M - m) ^ 2 ∂P := integral_mono (hδ2i t) (integrable_const _) (fun ω => by
          simp only; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hδb t ω) 2)
      _ = (M - m) ^ 2 := by simp
  have ha0 : ∀ t, 0 ≤ a t := fun t => integral_nonneg (fun ω => sq_nonneg _)
  have hwformula : ∀ t, w t = Bbar * ((t : ℝ) + 1) ^ α / (2 * ζ * (M - m)) := by
    intro t
    have : 0 < ((t : ℝ) + 1) ^ α := Real.rpow_pos_of_pos (by positivity) α
    simp only [hw, hε]; field_simp
  have hwmono : Monotone w := by
    intro s t hst
    rw [hwformula, hwformula]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hB.le
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hst 1) hα0.le
  have hw0 : ∀ t, 0 ≤ w t := fun t => by simp only [hw]; have := hεpos t; positivity
  have htel := abel_bound w a ((M - m) ^ 2) hwmono hw0 haA T'
  have htel2 : ∑ t ∈ Finset.range (T' + 1), w t * (a t - a (t + 1))
      ≤ (M - m) * (Bbar * (((T' + 1 : ℕ) : ℝ) ^ α / (2 * ζ))) := by
    refine htel.trans ?_
    have : w T' * ((M - m) ^ 2 - a (T' + 1)) ≤ w T' * (M - m) ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith [ha0 (T' + 1)]) (hw0 T')
    refine this.trans (le_of_eq ?_)
    rw [hwformula]; push_cast; field_simp
  -- step-size part
  have hstep : ∑ t ∈ Finset.range (T' + 1), ε t / 2 * Bbar ^ 2
      ≤ (M - m) * (Bbar * (ζ * (((T' + 1 : ℕ) : ℝ)) ^ (1 - α) / (2 * (1 - α)))) := by
    have he : ∀ t, ε t / 2 * Bbar ^ 2 = ζ * (M - m) * Bbar / 2 * (1 / ((t : ℝ) + 1) ^ α) := by
      intro t
      have : 0 < ((t : ℝ) + 1) ^ α := Real.rpow_pos_of_pos (by positivity) α
      simp only [hε]; field_simp
    simp only [he]
    rw [← Finset.mul_sum]
    have hs := sum_inv_rpow_le α hα0 hα1 (T' + 1)
    have hc : 0 ≤ ζ * (M - m) * Bbar / 2 := by positivity
    refine (mul_le_mul_of_nonneg_left hs hc).trans (le_of_eq ?_)
    have : (1 - α) ≠ 0 := by linarith
    field_simp
  have hη : ∑ t ∈ Finset.range (T' + 1), (M - m) * ∫ ω, |G t ω - Φ' (Z t ω)| ∂P
      = (M - m) * ∑ t ∈ Finset.range (T' + 1), ∫ ω, |P[H t | ℱ t] ω - Φ' (Z t ω)| ∂P := by
    rw [Finset.mul_sum]
  have : ∑ t ∈ Finset.range (T' + 1), w t * (∫ ω, (Z t ω - zstar) ^ 2 ∂P
      - ∫ ω, (Z (t + 1) ω - zstar) ^ 2 ∂P) = ∑ t ∈ Finset.range (T' + 1), w t * (a t - a (t + 1)) :=
    rfl
  rw [this, hη] at hsum
  calc _ ≤ _ := hsum
    _ ≤ (M - m) * (Bbar * (((T' + 1 : ℕ) : ℝ) ^ α / (2 * ζ)))
        + (M - m) * (Bbar * (ζ * (((T' + 1 : ℕ) : ℝ)) ^ (1 - α) / (2 * (1 - α))))
        + (M - m) * ∑ t ∈ Finset.range (T' + 1), ∫ ω, |P[H t | ℱ t] ω - Φ' (Z t ω)| ∂P := by
        linarith
    _ = _ := by ring
