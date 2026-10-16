-- Prove2me | solution 1 for AnalyticGeometry.evalR_ker_principal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T18:58:07.04509+00:00
-- url     : https://prove2.me/submissions/15964099-4c4c-40b7-addb-8dd54d097fbf

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

set_option autoImplicit false

open Filter Topology Metric

/-! Analytic core for the archimedean generators (H3 / sibling 082dbd9d).
Coefficient sequences `ℕ → ℂ` with geometric bounds `‖a k‖ * t ^ k ≤ C`. -/

/-- (B) The formal inverse of a series that is bounded at radius `t > r`, has constant term 1
and no zero on the closed disc of radius `r`, is bounded at some radius `t' > r`. -/
theorem h3_inv_bound (r : ℝ) (hr0 : 0 < r) (u : ℕ → ℂ) (t C : ℝ) (htr : r < t)
    (hC : ∀ k, ‖u k‖ * t ^ k ≤ C)
    (hz : ∀ z : ℂ, ‖z‖ ≤ r → ∑' k, u k * z ^ k ≠ 0) :
    ∃ v : ℕ → ℂ, PowerSeries.mk u * PowerSeries.mk v = 1 ∧
      ∃ t' > r, ∃ C', ∀ k, ‖v k‖ * t' ^ k ≤ C' := by
  have ht0 : 0 < t := hr0.trans htr
  set pF : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ u with hpF
  set sN : NNReal := ⟨t, ht0.le⟩ with hsN
  have hsN0 : (0 : ENNReal) < (sN : ENNReal) :=
    ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact ht0)
  have hradF : (sN : ENNReal) ≤ pF.radius := by
    refine pF.le_radius_of_bound C (fun n => ?_)
    rw [hpF, FormalMultilinearSeries.ofScalars_norm]
    exact hC n
  set F : ℂ → ℂ := pF.sum with hFdef
  have hF : HasFPowerSeriesOnBall F pF 0 sN :=
    (pF.hasFPowerSeriesOnBall (lt_of_lt_of_le hsN0 hradF)).mono hsN0 hradF
  have hFeval : ∀ z : ℂ, F z = ∑' k, u k * z ^ k := by
    intro z
    show ∑' k : ℕ, pF k (fun _ => z) = _
    congr 1
    funext k
    rw [hpF, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hFne : ∀ z : ℂ, ‖z‖ ≤ r → F z ≠ 0 := fun z hz' => by rw [hFeval]; exact hz z hz'
  have hdiffF : DifferentiableOn ℂ F (ball (0:ℂ) t) := by
    have := hF.differentiableOn
    rw [Metric.eball_coe] at this
    exact this
  have hU : IsOpen (ball (0:ℂ) t ∩ F ⁻¹' {0}ᶜ) :=
    hdiffF.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hKU : closedBall (0:ℂ) r ⊆ ball (0:ℂ) t ∩ F ⁻¹' {0}ᶜ := by
    intro z hz'
    rw [mem_closedBall, dist_zero_right] at hz'
    refine ⟨?_, hFne z hz'⟩
    rw [mem_ball, dist_zero_right]; linarith
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0:ℂ) r).exists_cthickening_subset_open hU hKU
  rw [cthickening_closedBall hδ.le hr0.le] at hδU
  set R' := δ + r with hR'
  have hR'0 : 0 < R' := by linarith
  have hR'r : r < R' := by linarith
  set H : ℂ → ℂ := fun z => (F z)⁻¹ with hHdef
  have hdiffH : DifferentiableOn ℂ H (closedBall (0:ℂ) R') := by
    have h1 : DifferentiableOn ℂ F (closedBall (0:ℂ) R') :=
      hdiffF.mono (fun z hz' => (hδU hz').1)
    exact h1.inv (fun z hz' => (hδU hz').2)
  have hR't : R' < t := by
    have hmem : ((R' : ℝ) : ℂ) ∈ closedBall (0:ℂ) R' := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR'0]
    have := (hδU hmem).1
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR'0] at this
    exact this
  set RN : NNReal := ⟨R', hR'0.le⟩ with hRN
  have hRN0 : (0 : NNReal) < RN := by rw [← NNReal.coe_pos]; exact hR'0
  have hH : HasFPowerSeriesOnBall H (cauchyPowerSeries H 0 RN) 0 RN :=
    hdiffH.hasFPowerSeriesOnBall hRN0
  set pH := cauchyPowerSeries H 0 RN with hpH
  set q : ℕ → ℂ := fun n => pH.coeff n with hq
  set e : ℕ → ℂ := fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, u kl.1 * q kl.2
    with he
  have hprod : ∀ y : ℂ, ‖y‖ < R' →
      Summable (fun n => ‖e n * y ^ n‖) ∧ HasSum (fun n => e n * y ^ n) 1 := by
    intro y hy
    have hyRN : y ∈ eball (0:ℂ) (RN : ENNReal) := by
      rw [Metric.eball_coe, mem_ball, dist_zero_right]; exact hy
    have hysN : y ∈ eball (0:ℂ) (sN : ENNReal) := by
      rw [Metric.eball_coe, mem_ball, dist_zero_right]; show ‖y‖ < t; linarith
    have hyF : y ∈ eball (0:ℂ) pF.radius := Metric.eball_subset_eball hradF hysN
    have hyH : y ∈ eball (0:ℂ) pH.radius := Metric.eball_subset_eball hH.r_le hyRN
    have hsF := pF.summable_norm_apply hyF
    have hsH := pH.summable_norm_apply hyH
    have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        pF kl.1 (fun _ => y) * pH kl.2 (fun _ => y) = e n * y ^ n := by
      intro n
      simp only [he, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun kl hkl => ?_)
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      rw [hpF, FormalMultilinearSeries.ofScalars_apply_eq,
        FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, smul_eq_mul, ← hkl,
        pow_add]
      simp only [hq]
      ring
    have hsum' := summable_norm_sum_mul_antidiagonal_of_summable_norm hsF hsH
    have htsum := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsF hsH
    simp only [hterm] at hsum' htsum
    refine ⟨hsum', ?_⟩
    have hFy : ∑' n, pF n (fun _ => y) = F y := rfl
    have hHy : ∑' n, pH n (fun _ => y) = H y := by
      have := (hH.hasSum hyRN).tsum_eq
      rw [zero_add] at this
      exact this
    have hyc : y ∈ closedBall (0:ℂ) R' := by
      rw [mem_closedBall, dist_zero_right]; exact hy.le
    have hFH : F y * H y = 1 := mul_inv_cancel₀ (hδU hyc).2
    rw [hFy, hHy, hFH] at htsum
    rw [htsum]
    exact hsum'.of_norm.hasSum
  set rN : NNReal := ⟨r, hr0.le⟩ with hrN
  set pE : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ e with hpE
  have hE : HasFPowerSeriesOnBall (fun _ : ℂ => (1:ℂ)) pE 0 rN := by
    refine ⟨?_, ?_, ?_⟩
    · refine pE.le_radius_of_summable_norm ?_
      have := (hprod (r : ℂ) (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; linarith)).1
      refine this.congr (fun n => ?_)
      rw [hpE, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr0]
      rfl
    · exact ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hr0)
    · intro y hy
      rw [Metric.eball_coe, mem_ball, dist_zero_right] at hy
      have := (hprod y (by change ‖y‖ < r at hy; linarith)).2
      have hfun : (fun n => pE n (fun _ => y)) = fun n => e n * y ^ n := by
        funext n
        rw [hpE, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      show HasSum (fun n => pE n fun _ => y) 1
      rw [hfun]
      exact this
  have hEq : pE = constFormalMultilinearSeries ℂ ℂ (1:ℂ) :=
    hE.hasFPowerSeriesAt.eq_formalMultilinearSeries hasFPowerSeriesAt_const
  have he_val : ∀ n, e n = if n = 0 then 1 else 0 := by
    intro n
    have h1 : e n = pE n (fun _ => 1) := by
      rw [hpE, FormalMultilinearSeries.ofScalars_apply_eq]; simp
    rw [h1, hEq]
    rcases n with _ | n
    · simp
    · simp
  refine ⟨q, ?_, ?_⟩
  · ext n
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, ← he_val n]
    simp only [he, PowerSeries.coeff_mk]
  · set t2 : ℝ := (r + R') / 2 with ht2
    have ht2r : r < t2 := by linarith
    have ht2R : t2 < R' := by linarith
    set tN : NNReal := ⟨t2, by linarith⟩ with htN
    have htrad : (tN : ENNReal) < pH.radius := by
      refine lt_of_lt_of_le ?_ hH.r_le
      exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe]; exact ht2R)
    have hsumH := pH.summable_norm_mul_pow htrad
    refine ⟨t2, ht2r, ∑' n, ‖pH n‖ * (tN : ℝ) ^ n, fun k => ?_⟩
    have := hsumH.le_tsum k (fun j _ => by positivity)
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef] at this
    exact this

/-- (A) Division by the linear factor `1 - T/y` of a series vanishing at `y`. -/
theorem h3_div_lin (a : ℕ → ℂ) (y : ℂ) (hy0 : y ≠ 0) (t C : ℝ) (hyt : ‖y‖ < t)
    (hC : ∀ k, ‖a k‖ * t ^ k ≤ C) (hsum : ∑' k, a k * y ^ k = 0) :
    ∃ b : ℕ → ℂ, PowerSeries.mk a =
        (1 - PowerSeries.C y⁻¹ * PowerSeries.X) * PowerSeries.mk b ∧
      ∃ C', ∀ k, ‖b k‖ * t ^ k ≤ C' := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have ht0 : 0 < t := hyn.trans hyt
  set ρ : ℝ := ‖y‖ / t with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one ht0]; exact hyt
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbd : ∀ j, ‖a j * y ^ j‖ ≤ C * ρ ^ j := by
    intro j
    rw [norm_mul, norm_pow, hρ, div_pow]
    have htj : 0 < t ^ j := pow_pos ht0 j
    rw [mul_div_assoc', le_div_iff₀ htj]
    calc ‖a j‖ * ‖y‖ ^ j * t ^ j = (‖a j‖ * t ^ j) * ‖y‖ ^ j := by ring
      _ ≤ C * ‖y‖ ^ j := mul_le_mul_of_nonneg_right (hC j) (by positivity)
  have hgeo : Summable (fun j : ℕ => C * ρ ^ j) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left C
  have hsa : Summable (fun j => a j * y ^ j) := Summable.of_norm_bounded hgeo hbd
  set S : ℕ → ℂ := fun k => ∑ j ∈ Finset.range (k + 1), a j * y ^ j with hS
  refine ⟨fun k => (y⁻¹) ^ k * S k, ?_, ?_⟩
  · ext n
    rw [PowerSeries.coeff_mk, sub_mul, one_mul, map_sub, PowerSeries.coeff_mk]
    rcases n with _ | n
    · simp [hS]
    · rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_mk]
      simp only [hS]
      rw [Finset.sum_range_succ _ (n + 1)]
      have key : y⁻¹ ^ (n + 1) * y ^ (n + 1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hy0, one_pow]
      linear_combination (-(a (n + 1))) * key
  · refine ⟨C / (1 - ρ), fun k => ?_⟩
    -- the partial sum is minus the tail
    have htail : S k = -∑' j, a (j + (k + 1)) * y ^ (j + (k + 1)) := by
      have h := hsa.sum_add_tsum_nat_add (k + 1)
      rw [hsum] at h
      simp only [hS]
      linear_combination h
    have hsa' : Summable (fun j => ‖a (j + (k + 1)) * y ^ (j + (k + 1))‖) :=
      (hgeo.comp_injective (add_left_injective (k + 1))).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun j => hbd _)
    have hnS : ‖S k‖ ≤ C * ρ ^ (k + 1) / (1 - ρ) := by
      rw [htail, norm_neg]
      refine (norm_tsum_le_tsum_norm hsa').trans ?_
      have hle : ∀ j, ‖a (j + (k + 1)) * y ^ (j + (k + 1))‖ ≤ C * ρ ^ (k + 1) * ρ ^ j := by
        intro j
        refine (hbd _).trans (le_of_eq ?_)
        rw [pow_add]; ring
      have hg2 : Summable (fun j : ℕ => C * ρ ^ (k + 1) * ρ ^ j) :=
        (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
      refine (hsa'.tsum_le_tsum hle hg2).trans (le_of_eq ?_)
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
      ring
    have hyk : ‖y⁻¹ ^ k‖ * t ^ k = 1 / ρ ^ k := by
      rw [norm_pow, norm_inv, hρ, div_pow, inv_pow]
      have : 0 < ‖y‖ ^ k := pow_pos hyn k
      have : 0 < t ^ k := pow_pos ht0 k
      field_simp
    rw [norm_mul, mul_comm (‖y⁻¹ ^ k‖), mul_assoc, hyk]
    have hρk : 0 < ρ ^ k ∨ ρ = 0 := by
      rcases hρ0.lt_or_eq with h | h
      · exact Or.inl (pow_pos h k)
      · exact Or.inr h.symm
    have h1ρ : 0 < 1 - ρ := by linarith
    rcases hρk with h | h
    · rw [mul_one_div, div_le_iff₀ h]
      calc ‖S k‖ ≤ C * ρ ^ (k + 1) / (1 - ρ) := hnS
        _ ≤ C / (1 - ρ) * ρ ^ k := by
          rw [pow_succ]
          have : C * (ρ ^ k * ρ) / (1 - ρ) = C / (1 - ρ) * ρ ^ k * ρ := by ring
          rw [this]
          have hcρ : 0 ≤ C / (1 - ρ) * ρ ^ k := by positivity
          nlinarith
    · exact absurd h (by positivity)

/-- (C) Product of two bounded sequences is bounded at any smaller radius. -/
theorem h3_mul_bound (a b : ℕ → ℂ) (t t' C D : ℝ) (ht' : 0 < t') (htt : t' < t)
    (ha : ∀ k, ‖a k‖ * t ^ k ≤ C) (hb : ∀ k, ‖b k‖ * t ^ k ≤ D) :
    ∃ E, ∀ k, ‖PowerSeries.coeff k (PowerSeries.mk a * PowerSeries.mk b)‖ * t' ^ k ≤ E := by
  have ht0 : 0 < t := ht'.trans htt
  set q : ℝ := t' / t with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one ht0]; exact htt
  have hC0 : 0 ≤ C := le_trans (by positivity) (ha 0)
  have hD0 : 0 ≤ D := le_trans (by positivity) (hb 0)
  obtain ⟨M, hM⟩ := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).bddAbove_range
  have hM' : ∀ k : ℕ, (k : ℝ) * q ^ k ≤ M := fun k => hM ⟨k, rfl⟩
  refine ⟨C * D * (M + 1), fun k => ?_⟩
  rw [PowerSeries.coeff_mul]
  have hterm : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal k,
      ‖PowerSeries.coeff kl.1 (PowerSeries.mk a) * PowerSeries.coeff kl.2 (PowerSeries.mk b)‖
        * t ^ k ≤ C * D := by
    intro kl hkl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, norm_mul, ← hkl, pow_add]
    calc ‖a kl.1‖ * ‖b kl.2‖ * (t ^ kl.1 * t ^ kl.2)
        = (‖a kl.1‖ * t ^ kl.1) * (‖b kl.2‖ * t ^ kl.2) := by ring
      _ ≤ C * D := mul_le_mul (ha _) (hb _) (by positivity) hC0
  have hsum : ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal k,
      PowerSeries.coeff kl.1 (PowerSeries.mk a) * PowerSeries.coeff kl.2 (PowerSeries.mk b)‖
        * t ^ k ≤ (k + 1) * (C * D) := by
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    push_cast; ring
  have htk : t' ^ k = t ^ k * q ^ k := by
    rw [← mul_pow, hq]; congr 1; field_simp
  rw [htk, ← mul_assoc]
  calc _ ≤ (k + 1) * (C * D) * q ^ k := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = C * D * ((k : ℝ) * q ^ k + q ^ k) := by ring
    _ ≤ C * D * (M + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : q ^ k ≤ 1 := pow_le_one₀ hq0 hq1.le
        linarith [hM' k]


open Polynomial in
theorem h3_pow_step (a : ℝ) (m : ℕ) : ∀ K : ℕ, ∃ s : Polynomial ℝ,
    (1 - C a * X ^ m) ^ K = 1 - C ((K : ℝ) * a) * X ^ m + X ^ (2 * m) * s := by
  intro K
  induction K with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨C ((k : ℝ) * a * a) + s * (1 - C a * X ^ m), ?_⟩
    rw [pow_succ, hs]
    have h2 : (X : Polynomial ℝ) ^ (2 * m) = X ^ m * X ^ m := by rw [two_mul, pow_add]
    rw [h2]
    push_cast
    simp only [map_mul, map_add, map_one, map_natCast]
    ring

/- (P1) For a real polynomial `Q` with `Q(0) = 1` there is a real polynomial `V`, zero-free on
the closed disc of radius `r`, with `Q * V ≡ 1 mod X^(m+1)`. -/
open Polynomial in
theorem h3_poly (r : ℝ) (hr : 0 < r) (Q : Polynomial ℝ) (hQ : Q.coeff 0 = 1) :
    ∀ m : ℕ, ∃ V : Polynomial ℝ, X ^ (m + 1) ∣ Q * V - 1 ∧
      ∀ z : ℂ, ‖z‖ ≤ r → aeval z V ≠ 0 := by
  intro m
  induction m with
  | zero =>
    refine ⟨1, ?_, fun z _ => by simp⟩
    rw [mul_one, zero_add, pow_one, X_dvd_iff]
    simp [hQ]
  | succ k ih =>
    obtain ⟨V, ⟨q, hq⟩, hz⟩ := ih
    set c := q.coeff 0 with hc
    obtain ⟨K, hK⟩ := exists_nat_gt (|c| * r ^ (k + 1))
    have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
    set a := c / K with ha
    obtain ⟨s, hs⟩ := h3_pow_step a (k + 1) K
    refine ⟨V * (1 - C a * X ^ (k + 1)) ^ K, ?_, ?_⟩
    · have hKa : (K : ℝ) * a = c := by
        rw [ha]; field_simp
      rw [← mul_assoc, hs, hKa]
      have hg : Q * V = 1 + X ^ (k + 1) * q := by rw [← hq]; ring
      have hX : X ∣ q - C c := by
        rw [X_dvd_iff]; simp [hc]
      obtain ⟨t, ht⟩ := hX
      have hq' : q = C c + X * t := by rw [← ht]; ring
      rw [hg, hq']
      refine ⟨t + X ^ k * (s - (C c + X * t) * C c + X ^ (k + 1) * (C c + X * t) * s), ?_⟩
      ring
    · intro y hy
      have hp : aeval y ((1 - C a * X ^ (k + 1)) ^ K) ≠ 0 := by
        simp only [map_pow, map_sub, map_one, map_mul, aeval_C, aeval_X]
        apply pow_ne_zero
        intro h0
        have h1 : algebraMap ℝ ℂ a * y ^ (k + 1) = 1 := by linear_combination -h0
        have h2 := congrArg norm h1
        rw [norm_mul, norm_pow, norm_one] at h2
        have ha' : ‖algebraMap ℝ ℂ a‖ = |a| := by
          rw [Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
        rw [ha'] at h2
        have h3 : |a| * ‖y‖ ^ (k + 1) ≤ |a| * r ^ (k + 1) := by gcongr
        have h4 : |a| * r ^ (k + 1) < 1 := by
          rw [ha, abs_div, abs_of_pos hKpos, div_mul_eq_mul_div, div_lt_one hKpos]
          exact hK
        linarith
      rw [map_mul]
      exact mul_ne_zero (hz y hy) hp

/-- The rounding recursion: `f 0 = 1`, `f (k+1) = -round (∑_{j ≤ k} f j * π (k+1-j))`. -/
noncomputable def h3_seq (π : ℕ → ℝ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => -round (∑ j : Fin (k + 1), (h3_seq π j : ℝ) * π (k + 1 - j))
decreasing_by exact j.isLt

theorem h3_seq_zero (π : ℕ → ℝ) : h3_seq π 0 = 1 := by
  rw [h3_seq]

theorem h3_seq_succ (π : ℕ → ℝ) (k : ℕ) :
    h3_seq π (k + 1) = -round (∑ j ∈ Finset.range (k + 1), (h3_seq π j : ℝ) * π (k + 1 - j)) := by
  rw [h3_seq, Fin.sum_univ_eq_sum_range (fun j => (h3_seq π j : ℝ) * π (k + 1 - j))]

theorem h3_seq_vanish (π : ℕ → ℝ) (n : ℕ) (hπ : ∀ j, 0 < j → j < n → π j = 0) :
    ∀ k, 0 < k → k < n → h3_seq π k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hkn
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [h3_seq_succ]
    have : ∑ j ∈ Finset.range (k + 1), (h3_seq π j : ℝ) * π (k + 1 - j) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, hπ (k + 1 - 0) (by omega) (by omega), mul_zero]
      · rw [ih j (by omega) hpos (by omega)]; simp
    rw [this]; simp

/-- (P2) Integer rounding: given a power series `P` with `P ≡ 1 mod X^n`, an integer series
`f = P * w` with `w 0 = 1`, `w k = 0` for `0 < k < n`, and `|w k| ≤ 1/2` for `k > 0`. -/
theorem h3_round (P : PowerSeries ℝ) (n : ℕ) (hn : 0 < n) (hP : PowerSeries.X ^ n ∣ P - 1) :
    ∃ f : ℕ → ℤ, ∃ w : ℕ → ℝ,
      P * PowerSeries.mk w = PowerSeries.mk (fun k => (f k : ℝ)) ∧ f 0 = 1 ∧
      w 0 = 1 ∧ (∀ k, 0 < k → k < n → w k = 0) ∧ (∀ k, 0 < k → |w k| ≤ 1 / 2) := by
  have hP0 : PowerSeries.constantCoeff P = 1 := by
    obtain ⟨d, hd⟩ := hP
    have := congrArg PowerSeries.constantCoeff hd
    simp [map_sub, map_pow, PowerSeries.constantCoeff_X, zero_pow hn.ne'] at this
    linear_combination this
  have hP0' : PowerSeries.constantCoeff P ≠ 0 := by rw [hP0]; exact one_ne_zero
  set π : ℕ → ℝ := fun k => PowerSeries.coeff k P⁻¹ with hπdef
  have hπ0 : π 0 = 1 := by
    simp only [hπdef, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
      hP0, inv_one]
  have hπv : ∀ j, 0 < j → j < n → π j = 0 := by
    intro j hj hjn
    have hdvd : PowerSeries.X ^ n ∣ P⁻¹ - 1 := by
      have : P⁻¹ - 1 = P⁻¹ * (-(P - 1)) := by
        rw [mul_neg, mul_sub, PowerSeries.inv_mul_cancel P hP0', mul_one]; ring
      rw [this]
      exact Dvd.dvd.mul_left (Dvd.dvd.neg_right hP) _
    have := PowerSeries.X_pow_dvd_iff.1 hdvd j hjn
    rw [map_sub, PowerSeries.coeff_one, if_neg hj.ne', sub_zero] at this
    exact this
  set f : ℕ → ℤ := h3_seq π with hfdef
  set w : ℕ → ℝ := fun k => ∑ j ∈ Finset.range (k + 1), (f j : ℝ) * π (k - j) with hwdef
  have hmk : PowerSeries.mk w = PowerSeries.mk (fun k => (f k : ℝ)) * P⁻¹ := by
    ext k
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (PowerSeries.mk (fun k => (f k : ℝ))) *
          PowerSeries.coeff j P⁻¹)]
    simp only [PowerSeries.coeff_mk, hwdef, hπdef]
  refine ⟨f, w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmk, mul_comm, mul_assoc, PowerSeries.inv_mul_cancel P hP0', mul_one]
  · rw [hfdef]; exact h3_seq_zero π
  · simp [hwdef, hfdef, h3_seq_zero, hπ0]
  · intro k hk hkn
    simp only [hwdef]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, Nat.sub_zero, hπv k hk hkn, mul_zero]
    · rw [hfdef, h3_seq_vanish π n hπv j hpos (by omega)]; simp
  · intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [hwdef]
    rw [Finset.sum_range_succ, Nat.sub_self, hπ0, mul_one, hfdef, h3_seq_succ]
    have hS : ∑ x ∈ Finset.range (k + 1), (h3_seq π x : ℝ) * π (k + 1 - x) =
        ∑ j ∈ Finset.range (k + 1), (h3_seq π j : ℝ) * π (k + 1 - j) := rfl
    push_cast
    rw [← sub_eq_add_neg]
    exact abs_sub_round _


/-- summability from a geometric bound -/
theorem h3_summ (a : ℕ → ℂ) (t C : ℝ) (z : ℂ) (hzt : ‖z‖ < t)
    (ha : ∀ k, ‖a k‖ * t ^ k ≤ C) :
    Summable (fun k => ‖a k * z ^ k‖) ∧ ∀ k, ‖a k * z ^ k‖ ≤ C * (‖z‖ / t) ^ k := by
  have ht0 : 0 < t := lt_of_le_of_lt (norm_nonneg z) hzt
  have hρ0 : 0 ≤ ‖z‖ / t := by positivity
  have hρ1 : ‖z‖ / t < 1 := by rw [div_lt_one ht0]; exact hzt
  have hbd : ∀ k, ‖a k * z ^ k‖ ≤ C * (‖z‖ / t) ^ k := by
    intro j
    rw [norm_mul, norm_pow, div_pow]
    have htj : 0 < t ^ j := pow_pos ht0 j
    rw [mul_div_assoc', le_div_iff₀ htj]
    calc ‖a j‖ * ‖z‖ ^ j * t ^ j = (‖a j‖ * t ^ j) * ‖z‖ ^ j := by ring
      _ ≤ C * ‖z‖ ^ j := mul_le_mul_of_nonneg_right (ha j) (by positivity)
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left C), hbd⟩

/-- (D) evaluation of a product of bounded series is the product of evaluations. -/
theorem h3_eval_mul (a b : ℕ → ℂ) (t C D : ℝ) (z : ℂ) (hzt : ‖z‖ < t)
    (ha : ∀ k, ‖a k‖ * t ^ k ≤ C) (hb : ∀ k, ‖b k‖ * t ^ k ≤ D) :
    ∑' k, PowerSeries.coeff k (PowerSeries.mk a * PowerSeries.mk b) * z ^ k =
      (∑' k, a k * z ^ k) * (∑' k, b k * z ^ k) := by
  have hsa := (h3_summ a t C z hzt ha).1
  have hsb := (h3_summ b t D z hzt hb).1
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb]
  congr 1
  funext k
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun kl hkl => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← hkl, pow_add]
  ring

/-- bounds pass to smaller radii -/
theorem h3_bound_mono (a : ℕ → ℂ) (t t' C : ℝ) (ht' : 0 ≤ t') (htt : t' ≤ t)
    (ha : ∀ k, ‖a k‖ * t ^ k ≤ C) : ∀ k, ‖a k‖ * t' ^ k ≤ C := fun k =>
  le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht' htt k) (norm_nonneg _)) (ha k)

/-- polynomial coefficients are bounded -/
theorem h3_poly_coeff_bound (P : Polynomial ℝ) : ∃ C, ∀ k, |P.coeff k| ≤ C := by
  refine ⟨∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j|, fun k => ?_⟩
  by_cases hk : k ≤ P.natDegree
  · exact Finset.single_le_sum (f := fun j => |P.coeff j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]
    exact Finset.sum_nonneg (fun j _ => abs_nonneg _)

/-- (W) the rounding factor `w` is zero-free on the closed disc of radius `r` once `r^n < 1 - r`. -/
theorem h3_w_ne_zero (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) (hn : 0 < n)
    (hrn : r ^ n < 1 - r) (w : ℕ → ℝ) (hw0 : w 0 = 1) (hwv : ∀ k, 0 < k → k < n → w k = 0)
    (hwb : ∀ k, 0 < k → |w k| ≤ 1 / 2) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ∑' k, ((w k : ℝ) : ℂ) * z ^ k ≠ 0 := by
  have hwb' : ∀ k, ‖((w k : ℝ) : ℂ)‖ * 1 ^ k ≤ 1 := by
    intro k
    rw [one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, hw0, abs_one]
    · linarith [hwb k h]
  have hzt : ‖z‖ < 1 := lt_of_le_of_lt hz hr1
  have hs := (h3_summ (fun k => ((w k : ℝ) : ℂ)) 1 1 z hzt hwb').1
  have hs' : Summable (fun k => ((w k : ℝ) : ℂ) * z ^ k) := hs.of_norm
  have hsplit := hs'.sum_add_tsum_nat_add n
  have hfin : ∑ i ∈ Finset.range n, ((w i : ℝ) : ℂ) * z ^ i = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [hw0]
    · intro b hb hb0
      rw [Finset.mem_range] at hb
      rw [hwv b (Nat.pos_of_ne_zero hb0) hb]; simp
    · intro h; exact absurd (Finset.mem_range.2 hn) h
  have hr1' : 0 < 1 - r := by linarith
  have htail : ‖∑' i, ((w (i + n) : ℝ) : ℂ) * z ^ (i + n)‖ ≤ r ^ n / 2 / (1 - r) := by
    have hsn : Summable (fun i => ‖((w (i + n) : ℝ) : ℂ) * z ^ (i + n)‖) :=
      (hs.comp_injective (add_left_injective n))
    refine (norm_tsum_le_tsum_norm hsn).trans ?_
    have hle : ∀ i, ‖((w (i + n) : ℝ) : ℂ) * z ^ (i + n)‖ ≤ r ^ n / 2 * r ^ i := by
      intro i
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |w (i + n)| ≤ 1 / 2 := hwb _ (by omega)
      have h2 : ‖z‖ ^ (i + n) ≤ r ^ (i + n) := pow_le_pow_left₀ (norm_nonneg _) hz _
      calc |w (i + n)| * ‖z‖ ^ (i + n) ≤ 1 / 2 * r ^ (i + n) :=
            mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = r ^ n / 2 * r ^ i := by rw [pow_add]; ring
    have hg : Summable (fun i : ℕ => r ^ n / 2 * r ^ i) :=
      (summable_geometric_of_lt_one hr0.le hr1).mul_left _
    refine (hsn.tsum_le_tsum hle hg).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
    ring
  intro h0
  rw [h0, hfin] at hsplit
  have : ‖∑' i, ((w (i + n) : ℝ) : ℂ) * z ^ (i + n)‖ = 1 := by
    have : ∑' i, ((w (i + n) : ℝ) : ℂ) * z ^ (i + n) = -1 := by linear_combination hsplit
    rw [this, norm_neg, norm_one]
  have h3 : r ^ n / 2 / (1 - r) < 1 := by
    rw [div_lt_one hr1']; linarith [pow_pos hr0 n]
  linarith

/-- evaluation of a real polynomial as a `tsum` -/
theorem h3_tsum_poly (A : Polynomial ℝ) (z : ℂ) :
    ∑' k, ((A.coeff k : ℝ) : ℂ) * z ^ k = Polynomial.aeval z A := by
  rw [Polynomial.aeval_eq_sum_range, tsum_eq_sum (s := Finset.range (A.natDegree + 1))]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Algebra.smul_def, Complex.coe_algebraMap]
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem h3_map_poly (A : Polynomial ℝ) :
    PowerSeries.map Complex.ofRealHom (A : PowerSeries ℝ) =
      PowerSeries.mk (fun k => ((A.coeff k : ℝ) : ℂ)) := by
  ext k
  simp [PowerSeries.coeff_map, Polynomial.coeff_coe]

/-- (H3-real, power-series level) the generator of the kernel of evaluation at `0 < x ≤ r`. -/
theorem h3_gen_real (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hx0 : 0 < x) (hxr : x ≤ r) :
    ∃ F : PowerSeries ℤ, PowerSeries.constantCoeff F = 1 ∧
      (∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k F : ℤ) : ℂ)‖ * t ^ k ≤ C) ∧
      ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * (x : ℂ) ^ k = 0 ∧
      ∀ G : PowerSeries ℤ, (∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k G : ℤ) : ℂ)‖ * t ^ k ≤ C) →
        ∑' k, ((PowerSeries.coeff k G : ℤ) : ℂ) * (x : ℂ) ^ k = 0 →
        ∃ H : PowerSeries ℤ, G = F * H ∧
          ∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k H : ℤ) : ℂ)‖ * t ^ k ≤ C := by
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < 1 - r) hr1
  have hrn : r ^ (n0 + 1) < 1 - r :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (by omega)) hn0
  set Q : Polynomial ℝ := 1 - Polynomial.C x⁻¹ * Polynomial.X with hQdef
  have hQ0 : Q.coeff 0 = 1 := by simp [hQdef]
  obtain ⟨V, hVdvd, hVz⟩ := h3_poly r hr0 Q hQ0 n0
  set P : PowerSeries ℝ := ((Q * V : Polynomial ℝ) : PowerSeries ℝ) with hPdef
  have hP : PowerSeries.X ^ (n0 + 1) ∣ P - 1 := by
    obtain ⟨d, hd⟩ := hVdvd
    refine ⟨(d : PowerSeries ℝ), ?_⟩
    rw [hPdef, ← Polynomial.coe_one, ← Polynomial.coe_sub, hd, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X]
  obtain ⟨f, w, hPw, hf0, hw0, hwv, hwb⟩ := h3_round P (n0 + 1) (by omega) hP
  -- complexified sequences
  set Vc : ℕ → ℂ := fun k => ((V.coeff k : ℝ) : ℂ) with hVc
  set Pc : ℕ → ℂ := fun k => (((Q * V).coeff k : ℝ) : ℂ) with hPc
  set wc : ℕ → ℂ := fun k => ((w k : ℝ) : ℂ) with hwc
  set fc : ℕ → ℂ := fun k => ((f k : ℤ) : ℂ) with hfc
  set L : PowerSeries ℂ := 1 - PowerSeries.C ((x : ℂ)⁻¹) * PowerSeries.X with hL
  have hQc : PowerSeries.map Complex.ofRealHom (Q : PowerSeries ℝ) = L := by
    simp [hQdef, hL, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X,
      PowerSeries.map_C, PowerSeries.map_X]
  have hPcm : PowerSeries.mk Pc = L * PowerSeries.mk Vc := by
    rw [hPc, ← h3_map_poly (Q * V), Polynomial.coe_mul, map_mul, hQc, h3_map_poly V]
  have hfPw : PowerSeries.mk fc = PowerSeries.mk Pc * PowerSeries.mk wc := by
    have h1 := congrArg (PowerSeries.map Complex.ofRealHom) hPw
    rw [map_mul] at h1
    have h2 : PowerSeries.map Complex.ofRealHom P = PowerSeries.mk Pc := h3_map_poly (Q * V)
    have h3 : PowerSeries.map Complex.ofRealHom (PowerSeries.mk w) = PowerSeries.mk wc := by
      ext k; simp [PowerSeries.coeff_map, hwc]
    have h4 : PowerSeries.map Complex.ofRealHom (PowerSeries.mk (fun k => (f k : ℝ))) =
        PowerSeries.mk fc := by
      ext k; simp [PowerSeries.coeff_map, hfc]
    rw [h2, h3, h4] at h1
    exact h1.symm
  -- bounds at radius 1
  obtain ⟨CV, hCV⟩ := h3_poly_coeff_bound V
  obtain ⟨CP, hCP⟩ := h3_poly_coeff_bound (Q * V)
  have hVb : ∀ k, ‖Vc k‖ * 1 ^ k ≤ CV := fun k => by
    simp only [hVc, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hCV k
  have hPb : ∀ k, ‖Pc k‖ * 1 ^ k ≤ CP := fun k => by
    simp only [hPc, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hCP k
  have hwb1 : ∀ k, ‖wc k‖ * 1 ^ k ≤ 1 := by
    intro k
    simp only [hwc, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, hw0, abs_one]
    · linarith [hwb k h]
  set F : PowerSeries ℤ := PowerSeries.mk (fun k => f k) with hFdef
  have hFc : ∀ k, ((PowerSeries.coeff k F : ℤ) : ℂ) = fc k := fun k => by
    simp [hFdef, hfc]
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hFdef, PowerSeries.coeff_mk, hf0]
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
  refine ⟨F, hF0, ?_, ?_, ?_⟩
  · -- bound for `F`
    obtain ⟨E, hE⟩ := h3_mul_bound Pc wc 1 ((r + 1) / 2) CP 1 (by linarith) (by linarith) hPb hwb1
    refine ⟨(r + 1) / 2, by linarith, E, fun k => ?_⟩
    rw [hFc, ← PowerSeries.coeff_mk k fc, hfPw]
    exact hE k
  · -- `F (x) = 0`
    have h1 : ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * (x : ℂ) ^ k =
        ∑' k, PowerSeries.coeff k (PowerSeries.mk Pc * PowerSeries.mk wc) * (x : ℂ) ^ k := by
      congr 1; funext k; rw [hFc, ← hfPw, PowerSeries.coeff_mk]
    rw [h1, h3_eval_mul Pc wc 1 CP 1 (x : ℂ) hxn hPb hwb1,
      show (∑' k, Pc k * (x : ℂ) ^ k) = Polynomial.aeval (x : ℂ) (Q * V) from
        h3_tsum_poly (Q * V) (x : ℂ)]
    have hQx : Polynomial.aeval (x : ℂ) Q = 0 := by
      have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      simp [hQdef, hx']
    rw [map_mul, hQx, zero_mul, zero_mul]
  · -- division
    rintro G ⟨tG, htG, CG, hCG⟩ hGx
    set Gc : ℕ → ℂ := fun k => ((PowerSeries.coeff k G : ℤ) : ℂ) with hGc
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hxtG : ‖(x : ℂ)‖ < tG := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
    obtain ⟨b, hb, Cb, hCb⟩ := h3_div_lin Gc (x : ℂ) hx0' tG CG hxtG hCG hGx
    -- inverse of `V`
    obtain ⟨vV, hvV, t1, ht1, C1, hC1⟩ := h3_inv_bound r hr0 Vc 1 CV hr1 hVb
      (fun z hz => by
        rw [show (∑' k, Vc k * z ^ k) = Polynomial.aeval z V from h3_tsum_poly V z]
        exact hVz z hz)
    -- inverse of `w`
    obtain ⟨vW, hvW, t2, ht2, C2, hC2⟩ := h3_inv_bound r hr0 wc 1 1 hr1 hwb1
      (fun z hz => h3_w_ne_zero r hr0 hr1 (n0 + 1) (by omega) hrn w hw0 hwv hwb z hz)
    set τ : ℝ := min tG (min t1 t2) with hτ
    have hτr : r < τ := lt_min htG (lt_min ht1 ht2)
    have hτ0 : 0 < τ := hr0.trans hτr
    have hbτ := h3_bound_mono b tG τ Cb hτ0.le (min_le_left _ _) hCb
    have hvVτ := h3_bound_mono vV t1 τ C1 hτ0.le
      (le_trans (min_le_right _ _) (min_le_left _ _)) hC1
    have hvWτ := h3_bound_mono vW t2 τ C2 hτ0.le
      (le_trans (min_le_right _ _) (min_le_right _ _)) hC2
    set τ1 : ℝ := (r + τ) / 2 with hτ1
    obtain ⟨E1, hE1⟩ := h3_mul_bound b vV τ τ1 Cb C1 (by linarith) (by linarith) hbτ hvVτ
    set bv : ℕ → ℂ := fun k => PowerSeries.coeff k (PowerSeries.mk b * PowerSeries.mk vV)
      with hbv
    have hbvmk : PowerSeries.mk bv = PowerSeries.mk b * PowerSeries.mk vV := by
      ext k; simp [hbv]
    have hvWτ1 := h3_bound_mono vW τ τ1 C2 (by linarith) (by linarith) hvWτ
    set τ2 : ℝ := (r + τ1) / 2 with hτ2
    obtain ⟨E2, hE2⟩ := h3_mul_bound bv vW τ1 τ2 E1 C2 (by linarith) (by linarith) hE1 hvWτ1
    set h : PowerSeries ℂ := PowerSeries.mk bv * PowerSeries.mk vW with hh
    -- formal identity `F * h = G` over `ℂ`
    have hFh : PowerSeries.mk fc * h = PowerSeries.mk Gc := by
      rw [hh, hbvmk, hfPw, hPcm, hb]
      linear_combination (L * PowerSeries.mk b * PowerSeries.mk wc * PowerSeries.mk vW) * hvV +
        (L * PowerSeries.mk b) * hvW
    -- integral quotient
    have hFu : PowerSeries.constantCoeff F = ((1 : ℤˣ) : ℤ) := by rw [hF0, Units.val_one]
    set Finv : PowerSeries ℤ := PowerSeries.invOfUnit F 1 with hFinv
    have hFFinv : F * Finv = 1 := PowerSeries.mul_invOfUnit F 1 hFu
    refine ⟨G * Finv, ?_, τ2, by linarith, E2, fun k => ?_⟩
    · rw [mul_comm G, ← mul_assoc, hFFinv, one_mul]
    · set φ : ℤ →+* ℂ := Int.castRingHom ℂ
      have hmF : PowerSeries.map φ F = PowerSeries.mk fc := by
        ext k; simp [hFdef, hfc, PowerSeries.coeff_map, φ]
      have hmG : PowerSeries.map φ G = PowerSeries.mk Gc := by
        ext k; simp [hGc, PowerSeries.coeff_map, φ]
      have hmFi : PowerSeries.map φ F * PowerSeries.map φ Finv = 1 := by
        rw [← map_mul, hFFinv, map_one]
      have hq : PowerSeries.map φ (G * Finv) = h := by
        rw [map_mul, hmG, ← hFh, ← hmF]
        calc PowerSeries.map φ F * h * PowerSeries.map φ Finv
            = h * (PowerSeries.map φ F * PowerSeries.map φ Finv) := by ring
          _ = h := by rw [hmFi, mul_one]
      have hk := congrArg (PowerSeries.coeff k) hq
      rw [PowerSeries.coeff_map] at hk
      have : ((PowerSeries.coeff k (G * Finv) : ℤ) : ℂ) = PowerSeries.coeff k h := by
        rw [← hk]; rfl
      rw [this, hh]
      exact hE2 k

namespace AnalyticGeometry

/-- shifting by a power of `T` preserves decay (with the same `s`). -/
theorem h1_decays_shift {s : ℝ} (hs : 0 < s) {f : LaurentSeries ℤ} (k : ℤ)
    (hf : DecaysAt s f) : DecaysAt s (HahnSeries.single (-k) (1 : ℤ) * f) := by
  unfold DecaysAt at *
  have h2 : Tendsto (fun n : ℤ => |(f.coeff n : ℝ)| * s ^ n) atTop (𝓝 0) := hf
  have h3 : Tendsto (fun n : ℤ => (|(f.coeff (n + k) : ℝ)| * s ^ (n + k)) * s ^ (-k)) atTop (𝓝 0) := by
    have := (h2.comp (tendsto_atTop_add_const_right atTop k tendsto_id)).mul_const (s ^ (-k))
    simpa using this
  refine h3.congr (fun n => ?_)
  have hc : (HahnSeries.single (-k) (1 : ℤ) * f).coeff n = f.coeff (n + k) := by
    have := HahnSeries.coeff_single_mul_add (r := (1 : ℤ)) (x := f) (a := n + k) (b := -k)
    rw [show n + k + -k = n by ring] at this
    simpa using this
  rw [hc, mul_assoc, ← zpow_add₀ hs.ne']
  congr 2
  ring

/-- (L0) a power series bounded past `r` lies in `ℤ((T))_{>r}`. -/
theorem h3_mem_of_bound (r : ℝ) (hr0 : 0 < r) (G : PowerSeries ℤ)
    (hG : ∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k G : ℤ) : ℂ)‖ * t ^ k ≤ C) :
    (G : LaurentSeries ℤ) ∈ zLaurentGT r := by
  obtain ⟨t, htr, C, hC⟩ := hG
  have ht0 : 0 < t := hr0.trans htr
  set s := (r + t) / 2 with hs
  refine ⟨s, by linarith, ?_⟩
  have hs0 : 0 < s := by linarith
  have hq0 : 0 ≤ s / t := by positivity
  have hq1 : s / t < 1 := by rw [div_lt_one ht0]; linarith
  have hlim : Tendsto (fun n : ℕ => C * (s / t) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hnat : Tendsto (fun n : ℕ => |((G : LaurentSeries ℤ).coeff (n : ℤ) : ℝ)| * s ^ n)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
    rw [LaurentSeries.coeff_coe_powerSeries]
    have h1 := hC n
    rw [Complex.norm_intCast] at h1
    have hsn : s ^ n = t ^ n * (s / t) ^ n := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hsn, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  unfold DecaysAt
  have ht : Tendsto (fun n : ℤ => n.toNat) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun n hn => by omega⟩)
  refine (hnat.comp ht).congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℤ)] with n hn
  simp only [Function.comp_apply]
  rw [← zpow_natCast, Int.toNat_of_nonneg hn]

/-- (L1) the power-series part of an element of `ℤ((T))_{>r}` is bounded past `r`. -/
theorem h3_bound_of_mem (r : ℝ) (hr0 : 0 < r) (g : LaurentSeries ℤ) (hg : g ∈ zLaurentGT r) :
    ∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ)‖ * t ^ k ≤ C := by
  obtain ⟨s, hsr, hs⟩ := hg
  have hs0 : 0 < s := hr0.trans hsr
  have h1 : Tendsto (fun k : ℕ => |((g.coeff (g.order + k) : ℤ) : ℝ)| * s ^ (g.order + (k : ℤ)))
      atTop (𝓝 0) :=
    hs.comp (tendsto_atTop_add_const_left atTop g.order tendsto_natCast_atTop_atTop)
  obtain ⟨B, hB⟩ := h1.bddAbove_range
  refine ⟨s, hsr, B * s ^ (-g.order), fun k => ?_⟩
  rw [LaurentSeries.powerSeriesPart_coeff, Complex.norm_intCast]
  have := hB ⟨k, rfl⟩
  have hsz : s ^ k = s ^ (g.order + (k : ℤ)) * s ^ (-g.order) := by
    rw [← zpow_add₀ hs0.ne', ← zpow_natCast]; congr 1; ring
  rw [hsz, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- (L3) complex evaluation of `T^o * p`. -/
theorem h3_evalC_shift (z : ℂ) (hz : z ≠ 0) (o : ℤ) (p : PowerSeries ℤ) :
    evalC z (HahnSeries.single o (1 : ℤ) * (p : LaurentSeries ℤ)) =
      z ^ o * ∑' k : ℕ, ((PowerSeries.coeff k p : ℤ) : ℂ) * z ^ k := by
  unfold evalC
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + o) := fun a b h => by simpa using h
  rw [← hinj.tsum_eq (f := fun n : ℤ =>
    (((HahnSeries.single o (1 : ℤ) * (p : LaurentSeries ℤ)).coeff n : ℤ) : ℂ) * z ^ n)]
  · rw [← tsum_mul_left]
    congr 1
    funext k
    rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.coeff_coe_powerSeries,
      zpow_add₀ hz, zpow_natCast]
    ring
  · intro n hn
    refine ⟨(n - o).toNat, ?_⟩
    by_contra hne
    have hne' : ¬ (((n - o).toNat : ℤ) + o = n) := hne
    apply hn
    have hlt : n - o < 0 := by omega
    have hn' : n = (n - o) + o := by ring
    simp only
    rw [hn', HahnSeries.coeff_single_mul_add, PowerSeries.coeff_coe, if_pos hlt]
    simp

theorem h3_evalR_eq (x : ℝ) (g : LaurentSeries ℤ) : ((evalR x g : ℝ) : ℂ) = evalC (x : ℂ) g := by
  unfold evalR evalC
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  push_cast
  ring

/-- **Sibling 082dbd9d** (`evalR_ker_principal`): the kernel of real evaluation at `0 < x ≤ r`
is principal. -/
theorem h3_evalR_ker_principal (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hx0 : 0 < x)
    (hxr : x ≤ r) :
    ∃ f ∈ zLaurentGT r, ∀ g ∈ zLaurentGT r,
      (evalR x g = 0 ↔ ∃ h ∈ zLaurentGT r, g = f * h) := by
  obtain ⟨F, _hF0, hFb, hFx, hdiv⟩ := h3_gen_real r x hr0 hr1 hx0 hxr
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  refine ⟨(F : LaurentSeries ℤ), h3_mem_of_bound r hr0 F hFb, fun g hg => ?_⟩
  constructor
  · intro hgx
    have hdg := LaurentSeries.single_order_mul_powerSeriesPart g
    have hS : ∑' k, ((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ) * (x : ℂ) ^ k = 0 := by
      have h1 : evalC (x : ℂ) g = 0 := by rw [← h3_evalR_eq, hgx, Complex.ofReal_zero]
      have h2 : evalC (x : ℂ) g = (x : ℂ) ^ g.order *
          ∑' k, ((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ) * (x : ℂ) ^ k := by
        conv_lhs => rw [← hdg]
        exact h3_evalC_shift _ hxc _ _
      rw [h2] at h1
      exact (mul_eq_zero.1 h1).resolve_left (zpow_ne_zero _ hxc)
    obtain ⟨H, hpH, hHb⟩ := hdiv g.powerSeriesPart (h3_bound_of_mem r hr0 g hg) hS
    obtain ⟨s, hsr, hsd⟩ := h3_mem_of_bound r hr0 H hHb
    refine ⟨HahnSeries.single g.order (1 : ℤ) * (H : LaurentSeries ℤ), ⟨s, hsr, ?_⟩, ?_⟩
    · have := h1_decays_shift (hr0.trans hsr) (-g.order) hsd
      rwa [neg_neg] at this
    · conv_lhs => rw [← hdg]
      rw [hpH, PowerSeries.coe_mul]
      ring
  · rintro ⟨h, hh, rfl⟩
    have hdh := LaurentSeries.single_order_mul_powerSeriesPart h
    obtain ⟨tp, htp, Cp, hCp⟩ := h3_bound_of_mem r hr0 h hh
    obtain ⟨tF, htF, CF, hCF⟩ := hFb
    have heq : (F : LaurentSeries ℤ) * h = HahnSeries.single h.order (1 : ℤ) *
        ((F * h.powerSeriesPart : PowerSeries ℤ) : LaurentSeries ℤ) := by
      conv_lhs => rw [← hdh]
      rw [PowerSeries.coe_mul]
      ring
    rw [← Complex.ofReal_eq_zero, h3_evalR_eq, heq, h3_evalC_shift _ hxc]
    set φ : ℤ →+* ℂ := Int.castRingHom ℂ with hφ
    set a : ℕ → ℂ := fun k => ((PowerSeries.coeff k F : ℤ) : ℂ) with ha
    set b : ℕ → ℂ := fun k => ((PowerSeries.coeff k h.powerSeriesPart : ℤ) : ℂ) with hb
    have hmk : PowerSeries.mk a * PowerSeries.mk b = PowerSeries.map φ (F * h.powerSeriesPart) := by
      rw [map_mul]
      congr 1 <;> (ext k; simp [PowerSeries.coeff_map, ha, hb, hφ])
    have hxt : ‖(x : ℂ)‖ < min tF tp := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact lt_min (lt_of_le_of_lt hxr htF) (lt_of_le_of_lt hxr htp)
    have hm0 : 0 ≤ min tF tp := le_of_lt (lt_of_le_of_lt (norm_nonneg _) hxt)
    have hev := h3_eval_mul a b (min tF tp) CF Cp (x : ℂ) hxt
      (h3_bound_mono a tF _ CF hm0 (min_le_left _ _) hCF)
      (h3_bound_mono b tp _ Cp hm0 (min_le_right _ _) hCp)
    have hcoef : ∀ k, PowerSeries.coeff k (PowerSeries.mk a * PowerSeries.mk b) =
        ((PowerSeries.coeff k (F * h.powerSeriesPart) : ℤ) : ℂ) := by
      intro k; rw [hmk, PowerSeries.coeff_map]; rfl
    simp only [hcoef] at hev
    rw [hev]
    have hFx' : ∑' k, a k * (x : ℂ) ^ k = 0 := hFx
    rw [hFx', zero_mul, mul_zero]

end AnalyticGeometry

open AnalyticGeometry in
theorem solution (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hx0 : 0 < x) (hxr : x ≤ r) :
    ∃ f ∈ zLaurentGT r, ∀ g ∈ zLaurentGT r,
      (evalR x g = 0 ↔ ∃ h ∈ zLaurentGT r, g = f * h) := by
  exact AnalyticGeometry.h3_evalR_ker_principal r x hr0 hr1 hx0 hxr
