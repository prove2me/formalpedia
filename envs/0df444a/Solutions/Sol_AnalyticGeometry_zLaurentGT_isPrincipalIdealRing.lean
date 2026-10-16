-- Prove2me | solution 1 for AnalyticGeometry.zLaurentGT_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T19:29:24.068647+00:00
-- url     : https://prove2.me/submissions/30b064fe-5c0e-459c-abd4-6df0b8479db0

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
theorem h3_gen_real (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hx0 : x ≠ 0) (hxr : |x| ≤ r) :
    ∃ F : PowerSeries ℤ, PowerSeries.constantCoeff F = 1 ∧
      (∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k F : ℤ) : ℂ)‖ * t ^ k ≤ C) ∧
      ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * (x : ℂ) ^ k = 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ r → (∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * z ^ k = 0 ↔ z = (x : ℂ))) ∧
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
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  refine ⟨F, hF0, ?_, ?_, ?_, ?_⟩
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
      simp [hQdef, hx']
    rw [map_mul, hQx, zero_mul, zero_mul]
  · -- zeros of `F` on the closed disc
    intro z hz
    have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz hr1
    have h1 : ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * z ^ k =
        ∑' k, PowerSeries.coeff k (PowerSeries.mk Pc * PowerSeries.mk wc) * z ^ k := by
      congr 1; funext k; rw [hFc, ← hfPw, PowerSeries.coeff_mk]
    rw [h1, h3_eval_mul Pc wc 1 CP 1 z hz1 hPb hwb1,
      show (∑' k, Pc k * z ^ k) = Polynomial.aeval z (Q * V) from h3_tsum_poly (Q * V) z,
      map_mul]
    have hQz : Polynomial.aeval z Q = 1 - (x : ℂ)⁻¹ * z := by simp [hQdef]
    rw [hQz]
    have hVne := hVz z hz
    have hwne := h3_w_ne_zero r hr0 hr1 (n0 + 1) (by omega) hrn w hw0 hwv hwb z hz
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · have : (x : ℂ)⁻¹ * z = 1 := by linear_combination -h
          field_simp at this
          linear_combination this
        · exact absurd h hVne
      · exact absurd h hwne
    · intro h
      rw [h, inv_mul_cancel₀ hx', sub_self, zero_mul, zero_mul]
  · -- division
    rintro G ⟨tG, htG, CG, hCG⟩ hGx
    set Gc : ℕ → ℂ := fun k => ((PowerSeries.coeff k G : ℤ) : ℂ) with hGc
    have hx0' : (x : ℂ) ≠ 0 := hx'
    have hxtG : ‖(x : ℂ)‖ < tG := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
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

/-- complex polynomial coefficient bound at radius `t` -/
theorem h3_cpoly_bound (A : Polynomial ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ k, ‖A.coeff k‖ * t ^ k ≤ ∑ j ∈ Finset.range (A.natDegree + 1), ‖A.coeff j‖ * t ^ j := by
  intro k
  by_cases hk : k ≤ A.natDegree
  · exact Finset.single_le_sum (f := fun j => ‖A.coeff j‖ * t ^ j) (fun j _ => by positivity)
      (Finset.mem_range.2 (by omega))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, zero_mul]
    exact Finset.sum_nonneg (fun j _ => by positivity)

theorem h3_tsum_cpoly (A : Polynomial ℂ) (z : ℂ) :
    ∑' k, A.coeff k * z ^ k = A.eval z := by
  refine (tsum_eq_sum (s := Finset.range (A.natDegree + 1)) ?_).trans
    (Polynomial.eval_eq_sum_range z).symm
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

theorem h3_coe_cpoly (A : Polynomial ℂ) :
    (A : PowerSeries ℂ) = PowerSeries.mk (fun k => A.coeff k) := by
  ext k; simp [Polynomial.coeff_coe]

/-- evaluation of polynomial × bounded series -/
theorem h3_eval_cpoly_mul (A : Polynomial ℂ) (b : ℕ → ℂ) (t D : ℝ) (z : ℂ) (hzt : ‖z‖ < t)
    (hb : ∀ k, ‖b k‖ * t ^ k ≤ D) :
    ∑' k, PowerSeries.coeff k ((A : PowerSeries ℂ) * PowerSeries.mk b) * z ^ k =
      A.eval z * ∑' k, b k * z ^ k := by
  have ht0 : 0 ≤ t := le_trans (norm_nonneg _) hzt.le
  rw [h3_coe_cpoly, h3_eval_mul _ b t _ D z hzt (h3_cpoly_bound A t ht0) hb, h3_tsum_cpoly]

theorem h3_lin_eq (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X : PowerSeries ℂ) =
      ((1 - Polynomial.C c * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ) := by
  simp [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X]

/-- (H3-complex, power-series level) generator for a non-real `y` with `0 < ‖y‖ ≤ r`. -/
theorem h3_gen_cplx (r : ℝ) (y : ℂ) (hr0 : 0 < r) (hr1 : r < 1) (hy0 : y ≠ 0) (hyr : ‖y‖ ≤ r)
    (hyi : y.im ≠ 0) :
    ∃ F : PowerSeries ℤ, PowerSeries.constantCoeff F = 1 ∧
      (∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k F : ℤ) : ℂ)‖ * t ^ k ≤ C) ∧
      (∀ z : ℂ, ‖z‖ ≤ r → (∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * z ^ k = 0 ↔
        z = y ∨ z = (starRingEnd ℂ) y)) ∧
      ∀ G : PowerSeries ℤ, (∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k G : ℤ) : ℂ)‖ * t ^ k ≤ C) →
        ∑' k, ((PowerSeries.coeff k G : ℤ) : ℂ) * y ^ k = 0 →
        ∃ H : PowerSeries ℤ, G = F * H ∧
          ∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k H : ℤ) : ℂ)‖ * t ^ k ≤ C := by
  set yb : ℂ := (starRingEnd ℂ) y with hyb
  have hyb0 : yb ≠ 0 := by rw [hyb]; exact (map_ne_zero _).2 hy0
  have hyyb : y ≠ yb := by
    intro h; apply hyi
    have := congrArg Complex.im h
    rw [hyb, Complex.conj_im] at this; linarith
  set a : ℝ := 2 * (y⁻¹).re with ha
  set b : ℝ := Complex.normSq y⁻¹ with hb
  have ha' : (a : ℂ) = y⁻¹ + yb⁻¹ := by
    rw [hyb, ← map_inv₀, Complex.add_conj, ha]
  have hb' : (b : ℂ) = y⁻¹ * yb⁻¹ := by
    rw [hyb, ← map_inv₀, Complex.mul_conj, hb]
  have hlin : ∀ c z : ℂ, c ≠ 0 → (1 - c⁻¹ * z = 0 ↔ z = c) := by
    intro c z hc
    constructor
    · intro h
      have : c⁻¹ * z = 1 := by linear_combination -h
      field_simp at this
      linear_combination this
    · intro h; rw [h, inv_mul_cancel₀ hc, sub_self]
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < 1 - r) hr1
  have hrn : r ^ (n0 + 1) < 1 - r :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (by omega)) hn0
  set Q : Polynomial ℝ :=
    1 - Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2 with hQdef
  have hQ0 : Q.coeff 0 = 1 := by simp [hQdef]
  have hQz : ∀ z : ℂ, Polynomial.aeval z Q = (1 - y⁻¹ * z) * (1 - yb⁻¹ * z) := by
    intro z
    simp only [hQdef, map_add, map_sub, map_one, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X, Complex.coe_algebraMap, ha', hb']
    ring
  obtain ⟨V, hVdvd, hVz⟩ := h3_poly r hr0 Q hQ0 n0
  set P : PowerSeries ℝ := ((Q * V : Polynomial ℝ) : PowerSeries ℝ) with hPdef
  have hP : PowerSeries.X ^ (n0 + 1) ∣ P - 1 := by
    obtain ⟨d, hd⟩ := hVdvd
    refine ⟨(d : PowerSeries ℝ), ?_⟩
    rw [hPdef, ← Polynomial.coe_one, ← Polynomial.coe_sub, hd, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X]
  obtain ⟨f, w, hPw, hf0, hw0, hwv, hwb⟩ := h3_round P (n0 + 1) (by omega) hP
  set Vc : ℕ → ℂ := fun k => ((V.coeff k : ℝ) : ℂ) with hVc
  set Pc : ℕ → ℂ := fun k => (((Q * V).coeff k : ℝ) : ℂ) with hPc
  set wc : ℕ → ℂ := fun k => ((w k : ℝ) : ℂ) with hwc
  set fc : ℕ → ℂ := fun k => ((f k : ℤ) : ℂ) with hfc
  set L1 : PowerSeries ℂ := 1 - PowerSeries.C y⁻¹ * PowerSeries.X with hL1
  set L2 : PowerSeries ℂ := 1 - PowerSeries.C yb⁻¹ * PowerSeries.X with hL2
  have hQc : PowerSeries.map Complex.ofRealHom (Q : PowerSeries ℝ) = L1 * L2 := by
    rw [h3_map_poly Q]
    ext k
    rw [PowerSeries.coeff_mk, hL1, hL2]
    have e : (1 - PowerSeries.C y⁻¹ * PowerSeries.X) * (1 - PowerSeries.C yb⁻¹ * PowerSeries.X) =
        (1 - PowerSeries.C (a : ℂ) * PowerSeries.X + PowerSeries.C (b : ℂ) * PowerSeries.X ^ 2 :
          PowerSeries ℂ) := by
      rw [ha', hb', map_add, map_mul]; ring
    rw [e]
    rcases k with _ | _ | _ | k
    · simp [hQdef]
    · simp [hQdef, PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul, Polynomial.coeff_one]
    · simp [hQdef, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_C_mul,
        Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_C_mul]
    · simp [hQdef, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_C_mul,
        Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hPcm : PowerSeries.mk Pc = L1 * L2 * PowerSeries.mk Vc := by
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
  -- evaluation of `F`
  have hFev : ∀ z : ℂ, ‖z‖ ≤ r → ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * z ^ k =
      Polynomial.aeval z Q * Polynomial.aeval z V * ∑' k, wc k * z ^ k := by
    intro z hz
    have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz hr1
    have h1 : ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * z ^ k =
        ∑' k, PowerSeries.coeff k (PowerSeries.mk Pc * PowerSeries.mk wc) * z ^ k := by
      congr 1; funext k; rw [hFc, ← hfPw, PowerSeries.coeff_mk]
    rw [h1, h3_eval_mul Pc wc 1 CP 1 z hz1 hPb hwb1,
      show (∑' k, Pc k * z ^ k) = Polynomial.aeval z (Q * V) from h3_tsum_poly (Q * V) z,
      map_mul]
  refine ⟨F, hF0, ?_, ?_, ?_⟩
  · obtain ⟨E, hE⟩ := h3_mul_bound Pc wc 1 ((r + 1) / 2) CP 1 (by linarith) (by linarith) hPb hwb1
    refine ⟨(r + 1) / 2, by linarith, E, fun k => ?_⟩
    rw [hFc, ← PowerSeries.coeff_mk k fc, hfPw]
    exact hE k
  · intro z hz
    rw [hFev z hz, hQz z]
    have hVne := hVz z hz
    have hwne := h3_w_ne_zero r hr0 hr1 (n0 + 1) (by omega) hrn w hw0 hwv hwb z hz
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact Or.inl ((hlin y z hy0).1 h)
          · exact Or.inr ((hlin yb z hyb0).1 h)
        · exact absurd h hVne
      · exact absurd h hwne
    · rintro (h | h)
      · rw [(hlin y z hy0).2 h]; simp
      · rw [(hlin yb z hyb0).2 h]; simp
  · rintro G ⟨tG, htG, CG, hCG⟩ hGy
    set Gc : ℕ → ℂ := fun k => ((PowerSeries.coeff k G : ℤ) : ℂ) with hGc
    have hytG : ‖y‖ < tG := lt_of_le_of_lt hyr htG
    have hybn : ‖yb‖ = ‖y‖ := by rw [hyb, Complex.norm_conj]
    have hybtG : ‖yb‖ < tG := by rw [hybn]; exact hytG
    obtain ⟨b1, hb1, Cb1, hCb1⟩ := h3_div_lin Gc y hy0 tG CG hytG hCG hGy
    have hGyb : ∑' k, Gc k * yb ^ k = 0 := by
      have := congrArg (starRingEnd ℂ) hGy
      rw [Complex.conj_tsum, map_zero] at this
      rw [← this]
      congr 1
      funext k
      simp [hGc, hyb]
    have hB1 : ∑' k, b1 k * yb ^ k = 0 := by
      have h1 : ∑' k, Gc k * yb ^ k = (1 - y⁻¹ * yb) * ∑' k, b1 k * yb ^ k := by
        have := h3_eval_cpoly_mul (1 - Polynomial.C y⁻¹ * Polynomial.X) b1 tG Cb1 yb hybtG hCb1
        rw [← h3_lin_eq, ← hb1] at this
        simp only [PowerSeries.coeff_mk] at this
        rw [this]
        simp
      have hne : (1 - y⁻¹ * yb) ≠ 0 := fun h => hyyb ((hlin y yb hy0).1 h).symm
      rw [hGyb] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left hne
    obtain ⟨b2, hb2, Cb2, hCb2⟩ := h3_div_lin b1 yb hyb0 tG Cb1 hybtG hCb1 hB1
    obtain ⟨vV, hvV, t1, ht1, C1, hC1⟩ := h3_inv_bound r hr0 Vc 1 CV hr1 hVb
      (fun z hz => by
        rw [show (∑' k, Vc k * z ^ k) = Polynomial.aeval z V from h3_tsum_poly V z]
        exact hVz z hz)
    obtain ⟨vW, hvW, t2, ht2, C2, hC2⟩ := h3_inv_bound r hr0 wc 1 1 hr1 hwb1
      (fun z hz => h3_w_ne_zero r hr0 hr1 (n0 + 1) (by omega) hrn w hw0 hwv hwb z hz)
    set τ : ℝ := min tG (min t1 t2) with hτ
    have hτr : r < τ := lt_min htG (lt_min ht1 ht2)
    have hτ0 : 0 < τ := hr0.trans hτr
    have hbτ := h3_bound_mono b2 tG τ Cb2 hτ0.le (min_le_left _ _) hCb2
    have hvVτ := h3_bound_mono vV t1 τ C1 hτ0.le
      (le_trans (min_le_right _ _) (min_le_left _ _)) hC1
    have hvWτ := h3_bound_mono vW t2 τ C2 hτ0.le
      (le_trans (min_le_right _ _) (min_le_right _ _)) hC2
    set τ1 : ℝ := (r + τ) / 2 with hτ1
    obtain ⟨E1, hE1⟩ := h3_mul_bound b2 vV τ τ1 Cb2 C1 (by linarith) (by linarith) hbτ hvVτ
    set bv : ℕ → ℂ := fun k => PowerSeries.coeff k (PowerSeries.mk b2 * PowerSeries.mk vV)
      with hbv
    have hbvmk : PowerSeries.mk bv = PowerSeries.mk b2 * PowerSeries.mk vV := by
      ext k; simp [hbv]
    have hvWτ1 := h3_bound_mono vW τ τ1 C2 (by linarith) (by linarith) hvWτ
    set τ2 : ℝ := (r + τ1) / 2 with hτ2
    obtain ⟨E2, hE2⟩ := h3_mul_bound bv vW τ1 τ2 E1 C2 (by linarith) (by linarith) hE1 hvWτ1
    set h : PowerSeries ℂ := PowerSeries.mk bv * PowerSeries.mk vW with hh
    have hFh : PowerSeries.mk fc * h = PowerSeries.mk Gc := by
      rw [hh, hbvmk, hfPw, hPcm, hb1, hb2]
      linear_combination
        (L1 * L2 * PowerSeries.mk b2 * PowerSeries.mk wc * PowerSeries.mk vW) * hvV +
        (L1 * L2 * PowerSeries.mk b2) * hvW
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
  obtain ⟨F, _hF0, hFb, hFx, _hFz, hdiv⟩ :=
    h3_gen_real r x hr0 hr1 hx0.ne' (by rw [abs_of_pos hx0]; exact hxr)
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

namespace AnalyticGeometry

/-- the evaluation series of an element of the ring is summable on the punctured closed disc -/
theorem h4_summable (r : ℝ) (hr0 : 0 < r) (z : ℂ) (hz0 : z ≠ 0) (hzr : ‖z‖ ≤ r)
    (g : LaurentSeries ℤ) (hg : g ∈ zLaurentGT r) :
    Summable (fun n : ℤ => ((g.coeff n : ℤ) : ℂ) * z ^ n) := by
  obtain ⟨t, htr, C, hC⟩ := h3_bound_of_mem r hr0 g hg
  have hzt : ‖z‖ < t := lt_of_le_of_lt hzr htr
  have hs := (h3_summ (fun k => ((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ)) t C z hzt hC).1
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + g.order) := fun a b h => by simpa using h
  rw [← hinj.summable_iff]
  · have : (fun n : ℤ => ((g.coeff n : ℤ) : ℂ) * z ^ n) ∘ (fun k : ℕ => (k : ℤ) + g.order) =
        fun k => (((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ) * z ^ k) * z ^ g.order := by
      funext k
      simp only [Function.comp_apply]
      rw [LaurentSeries.powerSeriesPart_coeff, add_comm g.order (k : ℤ), zpow_add₀ hz0,
        zpow_natCast]
      ring
    rw [this]
    exact hs.of_norm.mul_right _
  · intro n hn
    have hlt : n < g.order := by
      by_contra hle
      have hle' : g.order ≤ n := not_lt.1 hle
      exact hn ⟨(n - g.order).toNat, by show ((n - g.order).toNat : ℤ) + g.order = n; omega⟩
    rw [HahnSeries.coeff_eq_zero_of_lt_order hlt]
    simp

theorem h4_evalC_add (r : ℝ) (hr0 : 0 < r) (z : ℂ) (hz0 : z ≠ 0) (hzr : ‖z‖ ≤ r)
    (f g : LaurentSeries ℤ) (hf : f ∈ zLaurentGT r) (hg : g ∈ zLaurentGT r) :
    evalC z (f + g) = evalC z f + evalC z g := by
  unfold evalC
  rw [← (h4_summable r hr0 z hz0 hzr f hf).tsum_add (h4_summable r hr0 z hz0 hzr g hg)]
  congr 1
  funext n
  rw [HahnSeries.coeff_add]
  push_cast
  ring

theorem h4_evalC_mul (r : ℝ) (hr0 : 0 < r) (z : ℂ) (hz0 : z ≠ 0) (hzr : ‖z‖ ≤ r)
    (f g : LaurentSeries ℤ) (hf : f ∈ zLaurentGT r) (hg : g ∈ zLaurentGT r) :
    evalC z (f * g) = evalC z f * evalC z g := by
  have hdf := LaurentSeries.single_order_mul_powerSeriesPart f
  have hdg := LaurentSeries.single_order_mul_powerSeriesPart g
  obtain ⟨tf, htf, Cf, hCf⟩ := h3_bound_of_mem r hr0 f hf
  obtain ⟨tg, htg, Cg, hCg⟩ := h3_bound_of_mem r hr0 g hg
  have heq : f * g = HahnSeries.single (f.order + g.order) (1 : ℤ) *
      ((f.powerSeriesPart * g.powerSeriesPart : PowerSeries ℤ) : LaurentSeries ℤ) := by
    conv_lhs => rw [← hdf, ← hdg]
    rw [show HahnSeries.single (f.order + g.order) (1 : ℤ) =
        HahnSeries.single f.order (1 : ℤ) * HahnSeries.single g.order (1 : ℤ) by
      rw [HahnSeries.single_mul_single, one_mul], PowerSeries.coe_mul]
    ring
  have hef : evalC z f = z ^ f.order *
      ∑' k, ((PowerSeries.coeff k f.powerSeriesPart : ℤ) : ℂ) * z ^ k := by
    conv_lhs => rw [← hdf]
    exact h3_evalC_shift _ hz0 _ _
  have heg : evalC z g = z ^ g.order *
      ∑' k, ((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ) * z ^ k := by
    conv_lhs => rw [← hdg]
    exact h3_evalC_shift _ hz0 _ _
  rw [heq, h3_evalC_shift _ hz0, hef, heg]
  set φ : ℤ →+* ℂ := Int.castRingHom ℂ with hφ
  set a : ℕ → ℂ := fun k => ((PowerSeries.coeff k f.powerSeriesPart : ℤ) : ℂ) with ha
  set b : ℕ → ℂ := fun k => ((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ) with hb
  have hmk : PowerSeries.mk a * PowerSeries.mk b =
      PowerSeries.map φ (f.powerSeriesPart * g.powerSeriesPart) := by
    rw [map_mul]
    congr 1 <;> (ext k; simp [PowerSeries.coeff_map, ha, hb, hφ])
  have hzt : ‖z‖ < min tf tg := lt_min (lt_of_le_of_lt hzr htf) (lt_of_le_of_lt hzr htg)
  have hm0 : 0 ≤ min tf tg := le_of_lt (lt_of_le_of_lt (norm_nonneg _) hzt)
  have hev := h3_eval_mul a b (min tf tg) Cf Cg z hzt
    (h3_bound_mono a tf _ Cf hm0 (min_le_left _ _) hCf)
    (h3_bound_mono b tg _ Cg hm0 (min_le_right _ _) hCg)
  have hcoef : ∀ k, PowerSeries.coeff k (PowerSeries.mk a * PowerSeries.mk b) =
      ((PowerSeries.coeff k (f.powerSeriesPart * g.powerSeriesPart) : ℤ) : ℂ) := by
    intro k; rw [hmk, PowerSeries.coeff_map]; rfl
  simp only [hcoef] at hev
  rw [hev, zpow_add₀ hz0]
  ring

theorem h4_evalC_one (z : ℂ) : evalC z (1 : LaurentSeries ℤ) = 1 := by
  unfold evalC
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    rw [show (1 : LaurentSeries ℤ) = HahnSeries.single 0 1 from rfl, HahnSeries.coeff_single_of_ne hn]
    simp

theorem h4_evalC_zero (z : ℂ) : evalC z (0 : LaurentSeries ℤ) = 0 := by
  unfold evalC
  simp

/-- evaluation at `z` (with `0 < ‖z‖ ≤ r`) as a ring homomorphism on `R`. -/
noncomputable def h4_ev (r : ℝ) (hr0 : 0 < r) (R : Subring (LaurentSeries ℤ))
    (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r) (z : ℂ) (hz0 : z ≠ 0) (hzr : ‖z‖ ≤ r) :
    R →+* ℂ where
  toFun f := evalC z (f : LaurentSeries ℤ)
  map_one' := by simp only [OneMemClass.coe_one]; exact h4_evalC_one z
  map_mul' f g := by
    have hf : (f : LaurentSeries ℤ) ∈ zLaurentGT r := by rw [← hR]; exact f.2
    have hg : (g : LaurentSeries ℤ) ∈ zLaurentGT r := by rw [← hR]; exact g.2
    simp only [MulMemClass.coe_mul]
    exact h4_evalC_mul r hr0 z hz0 hzr _ _ hf hg
  map_zero' := by simp only [ZeroMemClass.coe_zero]; exact h4_evalC_zero z
  map_add' f g := by
    have hf : (f : LaurentSeries ℤ) ∈ zLaurentGT r := by rw [← hR]; exact f.2
    have hg : (g : LaurentSeries ℤ) ∈ zLaurentGT r := by rw [← hR]; exact g.2
    simp only [AddMemClass.coe_add]
    exact h4_evalC_add r hr0 z hz0 hzr _ _ hf hg

end AnalyticGeometry

namespace AnalyticGeometry

/-- real coordinates of `c` in the `ℝ`-basis `{1, y}` of `ℂ` (for non-real `y`) -/
noncomputable def h4_v (y c : ℂ) : ℝ := c.im / y.im
noncomputable def h4_u (y c : ℂ) : ℝ := c.re - h4_v y c * y.re

theorem h4_uv (y c : ℂ) (hyi : y.im ≠ 0) : c = (h4_u y c : ℂ) + (h4_v y c : ℂ) * y := by
  apply Complex.ext
  · simp [h4_u, h4_v]
  · simp [h4_u, h4_v]; field_simp

/-- remainders of the two-digit greedy expansion of `w` in powers of `y` -/
noncomputable def h4_rho (y w : ℂ) : ℕ → ℂ
  | 0 => w
  | j + 1 => h4_rho y w j - (round (h4_u y (h4_rho y w j / y ^ (2 * j))) : ℂ) * y ^ (2 * j)
      - (round (h4_v y (h4_rho y w j / y ^ (2 * j))) : ℂ) * y ^ (2 * j + 1)

/-- the digits -/
noncomputable def h4_dig (y w : ℂ) (k : ℕ) : ℤ :=
  if k % 2 = 0 then round (h4_u y (h4_rho y w (k / 2) / y ^ (2 * (k / 2))))
  else round (h4_v y (h4_rho y w (k / 2) / y ^ (2 * (k / 2))))

theorem h4_rho_succ_eq (y w : ℂ) (hy0 : y ≠ 0) (hyi : y.im ≠ 0) (j : ℕ) :
    h4_rho y w (j + 1) = y ^ (2 * j) *
      (((h4_u y (h4_rho y w j / y ^ (2 * j)) - round (h4_u y (h4_rho y w j / y ^ (2 * j))) : ℝ) : ℂ)
      + ((h4_v y (h4_rho y w j / y ^ (2 * j)) - round (h4_v y (h4_rho y w j / y ^ (2 * j))) : ℝ) : ℂ)
        * y) := by
  set c := h4_rho y w j / y ^ (2 * j) with hc
  have hyj : y ^ (2 * j) ≠ 0 := pow_ne_zero _ hy0
  have hρ : h4_rho y w j = y ^ (2 * j) * c := by rw [hc]; field_simp
  have huv := h4_uv y c hyi
  rw [h4_rho, ← hc, hρ]
  push_cast
  linear_combination (y ^ (2 * j)) * huv

theorem h4_rho_bound (y w : ℂ) (hy0 : y ≠ 0) (hyi : y.im ≠ 0) (hy1 : ‖y‖ ≤ 1) (j : ℕ) :
    ‖h4_rho y w (j + 1)‖ ≤ ‖y‖ ^ (2 * j) := by
  rw [h4_rho_succ_eq y w hy0 hyi j, norm_mul, norm_pow]
  have h1 := abs_sub_round (h4_u y (h4_rho y w j / y ^ (2 * j)))
  have h2 := abs_sub_round (h4_v y (h4_rho y w j / y ^ (2 * j)))
  have h3 : ‖(((h4_u y (h4_rho y w j / y ^ (2 * j)) - round (h4_u y (h4_rho y w j / y ^ (2 * j))) : ℝ) : ℂ)
      + ((h4_v y (h4_rho y w j / y ^ (2 * j)) - round (h4_v y (h4_rho y w j / y ^ (2 * j))) : ℝ) : ℂ)
        * y)‖ ≤ 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have : |h4_v y (h4_rho y w j / y ^ (2 * j)) - round (h4_v y (h4_rho y w j / y ^ (2 * j)))|
        * ‖y‖ ≤ 1 / 2 := by
      calc _ ≤ 1 / 2 * 1 := mul_le_mul h2 hy1 (norm_nonneg _) (by norm_num)
        _ = 1 / 2 := by ring
    linarith
  calc ‖y‖ ^ (2 * j) * _ ≤ ‖y‖ ^ (2 * j) * 1 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ‖y‖ ^ (2 * j) := mul_one _

theorem h4_partial (y w : ℂ) (J : ℕ) :
    ∑ k ∈ Finset.range (2 * J), ((h4_dig y w k : ℤ) : ℂ) * y ^ k = w - h4_rho y w J := by
  induction J with
  | zero => simp [h4_rho]
  | succ J ih =>
    rw [show 2 * (J + 1) = 2 * J + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have e1 : (2 * J) % 2 = 0 := by omega
    have e2 : (2 * J + 1) % 2 = 1 := by omega
    have e3 : (2 * J) / 2 = J := by omega
    have e4 : (2 * J + 1) / 2 = J := by omega
    simp only [h4_dig, e1, e2, e3, e4, if_true, one_ne_zero, if_false]
    rw [h4_rho]
    ring

/-- the digit coefficients are bounded -/
theorem h4_dig_bound (y w : ℂ) (hy0 : y ≠ 0) (hyi : y.im ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ M : ℝ, ∀ k, |((h4_dig y w k : ℤ) : ℝ)| ≤ M := by
  set B : ℝ := max ‖w‖ (‖y‖ ^ 2)⁻¹ with hB
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hc : ∀ j, ‖h4_rho y w j / y ^ (2 * j)‖ ≤ B := by
    intro j
    rcases j with _ | j
    · simp [h4_rho, hB]
    · rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
      calc ‖h4_rho y w (j + 1)‖ ≤ ‖y‖ ^ (2 * j) := h4_rho_bound y w hy0 hyi hy1 j
        _ = (‖y‖ ^ 2)⁻¹ * ‖y‖ ^ (2 * (j + 1)) := by
            rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]; field_simp
        _ ≤ B * ‖y‖ ^ (2 * (j + 1)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hyim : 0 < |y.im| := abs_pos.2 hyi
  have hv : ∀ c : ℂ, |h4_v y c| ≤ ‖c‖ / |y.im| := by
    intro c
    rw [h4_v, abs_div]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm c) hyim.le
  have hu : ∀ c : ℂ, |h4_u y c| ≤ ‖c‖ + ‖c‖ / |y.im| := by
    intro c
    rw [h4_u]
    refine (abs_sub _ _).trans (add_le_add (Complex.abs_re_le_norm c) ?_)
    rw [abs_mul]
    calc |h4_v y c| * |y.re| ≤ ‖c‖ / |y.im| * 1 :=
          mul_le_mul (hv c) ((Complex.abs_re_le_norm y).trans hy1) (abs_nonneg _) (by positivity)
      _ = ‖c‖ / |y.im| := mul_one _
  refine ⟨B + B / |y.im| + 1, fun k => ?_⟩
  have hround : ∀ a : ℝ, |((round a : ℤ) : ℝ)| ≤ |a| + 1 := by
    intro a
    have := abs_sub_round a
    have h2 : |((round a : ℤ) : ℝ)| ≤ |a| + |a - round a| := by
      calc |((round a : ℤ) : ℝ)| = |a - (a - round a)| := by ring_nf
        _ ≤ |a| + |a - round a| := abs_sub _ _
    linarith
  set c := h4_rho y w (k / 2) / y ^ (2 * (k / 2))
  have hcB := hc (k / 2)
  have hBd : ‖c‖ / |y.im| ≤ B / |y.im| := div_le_div_of_nonneg_right hcB hyim.le
  unfold h4_dig
  split_ifs
  · have := hround (h4_u y c); have := hu c; linarith
  · have := hround (h4_v y c); have := hv c
    have : 0 ≤ B := le_trans (norm_nonneg _) (le_max_left _ _)
    linarith

/-- complex evaluation at a non-real point of the punctured disc is surjective -/
theorem h4_evalC_surj (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (y : ℂ) (hy0 : y ≠ 0)
    (hyr : ‖y‖ ≤ r) (hyi : y.im ≠ 0) (w : ℂ) :
    ∃ f ∈ zLaurentGT r, evalC y f = w := by
  have hy1 : ‖y‖ ≤ 1 := by linarith
  obtain ⟨M, hM⟩ := h4_dig_bound y w hy0 hyi hy1
  set p : PowerSeries ℤ := PowerSeries.mk (fun k => h4_dig y w k) with hp
  have hpb : ∀ k, ‖((PowerSeries.coeff k p : ℤ) : ℂ)‖ * ((r + 1) / 2) ^ k ≤ M := by
    intro k
    rw [hp, PowerSeries.coeff_mk, Complex.norm_intCast]
    have h1 : ((r + 1) / 2) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    calc |((h4_dig y w k : ℤ) : ℝ)| * ((r + 1) / 2) ^ k ≤ |((h4_dig y w k : ℤ) : ℝ)| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ M := by rw [mul_one]; exact hM k
  refine ⟨(p : LaurentSeries ℤ), h3_mem_of_bound r hr0 p ⟨(r + 1) / 2, by linarith, M, hpb⟩, ?_⟩
  have hev : evalC y (p : LaurentSeries ℤ) =
      ∑' k, ((PowerSeries.coeff k p : ℤ) : ℂ) * y ^ k := by
    have := h3_evalC_shift y hy0 0 p
    rw [show HahnSeries.single (0 : ℤ) (1 : ℤ) = (1 : LaurentSeries ℤ) from rfl, one_mul,
      zpow_zero, one_mul] at this
    exact this
  rw [hev]
  have hyt : ‖y‖ < (r + 1) / 2 := by linarith
  have hs := (h3_summ _ _ M y hyt hpb).1
  have hlim := hs.of_norm.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun J : ℕ => ∑ k ∈ Finset.range (2 * J),
      ((PowerSeries.coeff k p : ℤ) : ℂ) * y ^ k) atTop
      (𝓝 (∑' k, ((PowerSeries.coeff k p : ℤ) : ℂ) * y ^ k)) :=
    hlim.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have h3 : Tendsto (fun J : ℕ => ∑ k ∈ Finset.range (2 * J),
      ((PowerSeries.coeff k p : ℤ) : ℂ) * y ^ k) atTop (𝓝 w) := by
    have hρ : Tendsto (fun J => h4_rho y w J) atTop (𝓝 0) := by
      have hq : Tendsto (fun j : ℕ => ‖y‖ ^ (2 * j)) atTop (𝓝 0) := by
        have : Tendsto (fun j : ℕ => (‖y‖ ^ 2) ^ j) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
            (by nlinarith [norm_nonneg y])
        refine this.congr (fun j => ?_)
        rw [← pow_mul]
      rw [← tendsto_add_atTop_iff_nat 1]
      refine squeeze_zero_norm (fun j => h4_rho_bound y w hy0 hyi hy1 j) hq
    have := (tendsto_const_nhds (x := w)).sub hρ
    rw [sub_zero] at this
    refine this.congr (fun J => ?_)
    rw [← h4_partial y w J]
    simp [hp]
  exact tendsto_nhds_unique h2 h3

end AnalyticGeometry

namespace AnalyticGeometry

/-- greedy real remainders (any real `x ≠ 0`) -/
noncomputable def h4_rrem (x y : ℝ) : ℕ → ℝ
  | 0 => y
  | n + 1 => (h4_rrem x y n - ⌊h4_rrem x y n⌋) / x

theorem h4_rrem_abs (x y : ℝ) (n : ℕ) : |h4_rrem x y n| ≤ |y| + 1 / |x| := by
  cases n with
  | zero =>
    have : 0 ≤ 1 / |x| := by positivity
    simp only [h4_rrem]; linarith
  | succ n =>
    rw [h4_rrem, abs_div]
    have h1 := Int.floor_le (h4_rrem x y n)
    have h2 := Int.lt_floor_add_one (h4_rrem x y n)
    have h3 : |h4_rrem x y n - ⌊h4_rrem x y n⌋| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ 1 / |x| := div_le_div_of_nonneg_right h3 (abs_nonneg x)
      _ ≤ |y| + 1 / |x| := by linarith [abs_nonneg y]

theorem h4_rpartial (x y : ℝ) (hx : x ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((⌊h4_rrem x y k⌋ : ℤ) : ℝ) * x ^ k = y - h4_rrem x y n * x ^ n := by
  induction n with
  | zero => simp [h4_rrem]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, h4_rrem, pow_succ]
    field_simp
    ring

/-- complex evaluation at a nonzero real point of the disc hits every real number -/
theorem h4_evalR_surj (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) (hx : x ≠ 0) (hxr : |x| ≤ r)
    (y : ℝ) : ∃ f ∈ zLaurentGT r, evalC (x : ℂ) f = (y : ℂ) := by
  set a : ℕ → ℤ := fun n => ⌊h4_rrem x y n⌋ with ha
  set M : ℝ := |y| + 1 / |x| + 1 with hM
  have hab : ∀ k, |((a k : ℤ) : ℝ)| ≤ M := by
    intro k
    have h1 := Int.floor_le (h4_rrem x y k)
    have h2 := Int.lt_floor_add_one (h4_rrem x y k)
    obtain ⟨h3a, h3b⟩ := abs_le.1 (h4_rrem_abs x y k)
    rw [abs_le]
    constructor <;> simp only [ha] <;> linarith
  set p : PowerSeries ℤ := PowerSeries.mk (fun k => a k) with hp
  have hpb : ∀ k, ‖((PowerSeries.coeff k p : ℤ) : ℂ)‖ * ((r + 1) / 2) ^ k ≤ M := by
    intro k
    rw [hp, PowerSeries.coeff_mk, Complex.norm_intCast]
    have h1 : ((r + 1) / 2) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    calc |((a k : ℤ) : ℝ)| * ((r + 1) / 2) ^ k ≤ |((a k : ℤ) : ℝ)| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ M := by rw [mul_one]; exact hab k
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  refine ⟨(p : LaurentSeries ℤ), h3_mem_of_bound r hr0 p ⟨(r + 1) / 2, by linarith, M, hpb⟩, ?_⟩
  have hev : evalC (x : ℂ) (p : LaurentSeries ℤ) =
      ∑' k, ((PowerSeries.coeff k p : ℤ) : ℂ) * (x : ℂ) ^ k := by
    have := h3_evalC_shift (x : ℂ) hxc 0 p
    rw [show HahnSeries.single (0 : ℤ) (1 : ℤ) = (1 : LaurentSeries ℤ) from rfl, one_mul,
      zpow_zero, one_mul] at this
    exact this
  rw [hev]
  have hxn : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hyt : ‖(x : ℂ)‖ < (r + 1) / 2 := by rw [hxn]; linarith
  have hs := (h3_summ _ _ M (x : ℂ) hyt hpb).1
  have h2 := hs.of_norm.hasSum.tendsto_sum_nat
  have h3 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      ((PowerSeries.coeff k p : ℤ) : ℂ) * (x : ℂ) ^ k) atTop (𝓝 (y : ℂ)) := by
    have hx1 : |x| < 1 := by linarith
    have hrem : Tendsto (fun n : ℕ => h4_rrem x y n * x ^ n) atTop (𝓝 0) := by
      have hlim : Tendsto (fun n : ℕ => (|y| + 1 / |x|) * |x| ^ n) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg x) hx1).const_mul
          (|y| + 1 / |x|)
      refine squeeze_zero_norm (fun n => ?_) hlim
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right (h4_rrem_abs x y n) (by positivity)
    have hR : Tendsto (fun n : ℕ => y - h4_rrem x y n * x ^ n) atTop (𝓝 y) := by
      have := (tendsto_const_nhds (x := y)).sub hrem
      rwa [sub_zero] at this
    have hC := (Complex.continuous_ofReal.tendsto y).comp hR
    refine hC.congr (fun n => ?_)
    simp only [Function.comp_apply]
    rw [← h4_rpartial x y hx n]
    push_cast
    simp [hp, ha]
  exact tendsto_nhds_unique h2 h3

/-- a kernel is maximal once nonzero values have inverses in the image -/
theorem h4_ker_maximal {A : Type} [CommRing A] (φ : A →+* ℂ)
    (hinv : ∀ a, φ a ≠ 0 → ∃ b, φ a * φ b = 1) : (RingHom.ker φ).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J a hJ haJ ha => ?_⟩
  · rw [RingHom.mem_ker, map_one] at h
    exact one_ne_zero h
  · have ha' : φ a ≠ 0 := fun h => haJ (RingHom.mem_ker.2 h)
    obtain ⟨b, hb⟩ := hinv a ha'
    have h1 : a * b - 1 ∈ J := hJ (by rw [RingHom.mem_ker, map_sub, map_mul, hb, map_one, sub_self])
    have h2 : a * b ∈ J := J.mul_mem_right b ha
    have := J.sub_mem h2 h1
    simpa using this

/-- the Laurent-level kernel statement from a power-series generator -/
theorem h4_ker_laurent (r : ℝ) (hr0 : 0 < r) (y : ℂ) (hy0 : y ≠ 0) (hyr : ‖y‖ ≤ r)
    (F : PowerSeries ℤ)
    (hFb : ∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k F : ℤ) : ℂ)‖ * t ^ k ≤ C)
    (hFy : ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * y ^ k = 0)
    (hdiv : ∀ G : PowerSeries ℤ,
      (∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k G : ℤ) : ℂ)‖ * t ^ k ≤ C) →
      ∑' k, ((PowerSeries.coeff k G : ℤ) : ℂ) * y ^ k = 0 →
      ∃ H : PowerSeries ℤ, G = F * H ∧
        ∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k H : ℤ) : ℂ)‖ * t ^ k ≤ C)
    (g : LaurentSeries ℤ) (hg : g ∈ zLaurentGT r) :
    evalC y g = 0 ↔ ∃ h ∈ zLaurentGT r, g = (F : LaurentSeries ℤ) * h := by
  have hFm := h3_mem_of_bound r hr0 F hFb
  constructor
  · intro hgy
    have hdg := LaurentSeries.single_order_mul_powerSeriesPart g
    have hS : ∑' k, ((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ) * y ^ k = 0 := by
      have h2 : evalC y g = y ^ g.order *
          ∑' k, ((PowerSeries.coeff k g.powerSeriesPart : ℤ) : ℂ) * y ^ k := by
        conv_lhs => rw [← hdg]
        exact h3_evalC_shift _ hy0 _ _
      rw [h2] at hgy
      exact (mul_eq_zero.1 hgy).resolve_left (zpow_ne_zero _ hy0)
    obtain ⟨H, hpH, hHb⟩ := hdiv g.powerSeriesPart (h3_bound_of_mem r hr0 g hg) hS
    obtain ⟨s, hsr, hsd⟩ := h3_mem_of_bound r hr0 H hHb
    refine ⟨HahnSeries.single g.order (1 : ℤ) * (H : LaurentSeries ℤ), ⟨s, hsr, ?_⟩, ?_⟩
    · have := h1_decays_shift (hr0.trans hsr) (-g.order) hsd
      rwa [neg_neg] at this
    · conv_lhs => rw [← hdg]
      rw [hpH, PowerSeries.coe_mul]
      ring
  · rintro ⟨h, hh, rfl⟩
    rw [h4_evalC_mul r hr0 y hy0 hyr _ _ hFm hh]
    have hF : evalC y (F : LaurentSeries ℤ) = 0 := by
      have := h3_evalC_shift y hy0 0 F
      rw [show HahnSeries.single (0 : ℤ) (1 : ℤ) = (1 : LaurentSeries ℤ) from rfl, one_mul,
        zpow_zero, one_mul] at this
      rw [this, hFy]
    rw [hF, zero_mul]

/-- **Archimedean maximal ideals.** For `0 < ‖y‖ ≤ r` the kernel of evaluation at `y` is the
maximal ideal generated by an integral power series with constant term `1` whose zeros on the
closed disc are exactly `y` and `ȳ`. -/
theorem h4_arch (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (R : Subring (LaurentSeries ℤ))
    (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r) (y : ℂ) (hy0 : y ≠ 0) (hyr : ‖y‖ ≤ r) :
    ∃ F : PowerSeries ℤ, PowerSeries.constantCoeff F = 1 ∧
      (∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k F : ℤ) : ℂ)‖ * t ^ k ≤ C) ∧
      (∀ z : ℂ, ‖z‖ ≤ r → (∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * z ^ k = 0 ↔
        z = y ∨ z = (starRingEnd ℂ) y)) ∧
      (∀ g ∈ zLaurentGT r, evalC y g = 0 ↔ ∃ h ∈ zLaurentGT r, g = (F : LaurentSeries ℤ) * h) ∧
      (RingHom.ker (h4_ev r hr0 R hR y hy0 hyr)).IsMaximal := by
  have hmax : (RingHom.ker (h4_ev r hr0 R hR y hy0 hyr)).IsMaximal := by
    apply h4_ker_maximal
    intro a ha
    have hval : ∀ b : R, h4_ev r hr0 R hR y hy0 hyr b = evalC y (b : LaurentSeries ℤ) :=
      fun b => rfl
    rw [hval] at ha
    by_cases hyi : y.im = 0
    · have hyx : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyi])
      have hx0 : y.re ≠ 0 := fun h => hy0 (by rw [hyx, h, Complex.ofReal_zero])
      have hxr : |y.re| ≤ r := by
        have : ‖y‖ = |y.re| := by rw [hyx, Complex.norm_real, Real.norm_eq_abs]; simp
        rw [← this]; exact hyr
      have ha_mem : (a : LaurentSeries ℤ) ∈ zLaurentGT r := by rw [← hR]; exact a.2
      have hreal : evalC y (a : LaurentSeries ℤ) = ((evalR y.re (a : LaurentSeries ℤ) : ℝ) : ℂ) := by
        rw [h3_evalR_eq, ← hyx]
      obtain ⟨f, hf, hfv⟩ := h4_evalR_surj r hr0 hr1 y.re hx0 hxr (evalR y.re a)⁻¹
      refine ⟨⟨f, by rw [← SetLike.mem_coe, hR]; exact hf⟩, ?_⟩
      rw [hval, hreal]
      show _ * evalC y f = 1
      have hfv' : evalC y f = (((evalR y.re (a : LaurentSeries ℤ))⁻¹ : ℝ) : ℂ) := by
        rw [← hfv, ← hyx]
      rw [hfv', ← Complex.ofReal_mul, mul_inv_cancel₀, Complex.ofReal_one]
      intro h0
      apply ha
      rw [hreal, h0, Complex.ofReal_zero]
    · obtain ⟨f, hf, hfv⟩ := h4_evalC_surj r hr0 hr1 y hy0 hyr hyi (evalC y a)⁻¹
      refine ⟨⟨f, by rw [← SetLike.mem_coe, hR]; exact hf⟩, ?_⟩
      rw [hval]
      show _ * evalC y f = 1
      rw [hfv, mul_inv_cancel₀ ha]
  by_cases hyi : y.im = 0
  · have hyx : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyi])
    have hx0 : y.re ≠ 0 := fun h => hy0 (by rw [hyx, h, Complex.ofReal_zero])
    have hxr : |y.re| ≤ r := by
      have : ‖y‖ = |y.re| := by rw [hyx, Complex.norm_real, Real.norm_eq_abs]; simp
      rw [← this]; exact hyr
    obtain ⟨F, hF0, hFb, hFx, hFz, hdiv⟩ := h3_gen_real r y.re hr0 hr1 hx0 hxr
    rw [← hyx] at hFx hFz hdiv
    have hconj : (starRingEnd ℂ) y = y := by
      apply Complex.ext <;> simp [hyi]
    refine ⟨F, hF0, hFb, fun z hz => ?_, h4_ker_laurent r hr0 y hy0 hyr F hFb hFx hdiv, hmax⟩
    rw [hFz z hz, hconj, or_self]
  · obtain ⟨F, hF0, hFb, hFz, hdiv⟩ := h3_gen_cplx r y hr0 hr1 hy0 hyr hyi
    have hFy : ∑' k, ((PowerSeries.coeff k F : ℤ) : ℂ) * y ^ k = 0 :=
      (hFz y hyr).2 (Or.inl rfl)
    exact ⟨F, hF0, hFb, hFz, h4_ker_laurent r hr0 y hy0 hyr F hFb hFy hdiv, hmax⟩

end AnalyticGeometry

open Filter Topology

namespace AnalyticGeometry

/-- H5 (maximality). -/
theorem h5_span_maximal (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (R : Subring (LaurentSeries ℤ)) (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r)
    (K : Type) [Field K] (φ : R →+* K) (hφ : Function.Surjective φ) (g : R)
    (hker : ∀ f : R, φ f = 0 ↔ ∃ h : R, f = g * h) :
    (Ideal.span {g}).IsMaximal := by
  have hk : RingHom.ker φ = Ideal.span {g} := by
    ext f
    rw [RingHom.mem_ker, hker, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨h, mul_comm _ _⟩
    · rintro ⟨h, rfl⟩; exact ⟨h, mul_comm _ _⟩
  rw [← hk]
  exact RingHom.ker_isMaximal_of_surjective φ hφ

theorem h1_content (f : LaurentSeries ℤ) (h0 : f.coeff 0 ≠ 0) :
    ∃ (c : ℤ) (g : LaurentSeries ℤ), c ≠ 0 ∧ (∀ n, f.coeff n = c * g.coeff n) ∧
      (∀ p : ℕ, p.Prime → ∃ n, ¬ (p : ℤ) ∣ g.coeff n) := by
  set I : Ideal ℤ := Ideal.span (Set.range fun n => f.coeff n) with hI
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmem : ∀ n, f.coeff n ∈ I := fun n => Ideal.subset_span ⟨n, rfl⟩
  have hdvd : ∀ n, c ∣ f.coeff n := by
    intro n
    have := hmem n
    rw [hc, Submodule.mem_span_singleton] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by simpa [mul_comm] using ha.symm⟩
  have hc0 : c ≠ 0 := by
    intro h
    have := hmem 0
    rw [hc, h] at this
    simp [Submodule.mem_span_singleton] at this
    exact h0 this
  choose d hd using hdvd
  have hsupp : (Function.support d) ⊆ f.support := by
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [HahnSeries.mem_support]
    rw [hd n]
    exact mul_ne_zero hc0 hn
  refine ⟨c, ⟨d, f.isPWO_support.mono hsupp⟩, hc0, hd, ?_⟩
  intro p hp
  by_contra hcon
  push_neg at hcon
  have hcon' : ∀ n, (p : ℤ) ∣ d n := hcon
  have hall : ∀ n, (p : ℤ) * c ∣ f.coeff n := by
    intro n
    obtain ⟨e, he⟩ := hcon' n
    exact ⟨e, by rw [hd n, he]; ring⟩
  have hcI : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
  have : I ≤ Ideal.span {(p : ℤ) * c} := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨n, rfl⟩
    exact Ideal.mem_span_singleton.2 (hall n)
  have h2 := Ideal.mem_span_singleton.1 (this hcI)
  obtain ⟨e, he⟩ := h2
  have : (p : ℤ) * e = 1 := by
    have : c * ((p : ℤ) * e - 1) = 0 := by linear_combination he.symm
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc0
    · linarith
  have h1 : (p : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast h1)


theorem h1_normal_form (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (f : LaurentSeries ℤ)
    (hf : f ∈ zLaurentGT r) (hf0 : f ≠ 0) :
    ∃ (k : ℤ) (c : ℤ) (g : LaurentSeries ℤ), c ≠ 0 ∧ g ∈ zLaurentGT r ∧
      (∀ n : ℤ, n < 0 → g.coeff n = 0) ∧ g.coeff 0 ≠ 0 ∧
      (∀ p : ℕ, p.Prime → ∃ n, ¬ (p : ℤ) ∣ g.coeff n) ∧
      f = (HahnSeries.single k (1 : ℤ)) * (c : LaurentSeries ℤ) * g := by
  obtain ⟨s, hsr, hs⟩ := hf
  have hs0 : 0 < s := hr0.trans hsr
  set k : ℤ := f.order with hk
  set f' : LaurentSeries ℤ := HahnSeries.single (-k) (1 : ℤ) * f with hf'
  have hcoef : ∀ n, f'.coeff n = f.coeff (n + k) := by
    intro n
    have := HahnSeries.coeff_single_mul_add (r := (1 : ℤ)) (x := f) (a := n + k) (b := -k)
    rw [show n + k + -k = n by ring] at this
    simpa [hf'] using this
  have hf'dec : DecaysAt s f' := h1_decays_shift hs0 k hs
  have h00 : f'.coeff 0 ≠ 0 := by
    rw [hcoef, zero_add]; exact fun h => hf0 (HahnSeries.coeff_order_eq_zero.1 h)
  obtain ⟨c, g, hc0, hcg, hprime⟩ := h1_content f' h00
  have hgneg : ∀ n : ℤ, n < 0 → g.coeff n = 0 := by
    intro n hn
    have h1 : f'.coeff n = 0 := by
      rw [hcoef]; exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)
    rw [hcg n] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h; apply h00; rw [hcg 0, h, mul_zero]
  have hgdec : DecaysAt s g := by
    unfold DecaysAt at *
    refine squeeze_zero (fun n => mul_nonneg (abs_nonneg _) (zpow_nonneg hs0.le _)) (fun n => ?_) hf'dec
    refine mul_le_mul_of_nonneg_right ?_ (zpow_nonneg hs0.le _)
    have h1 : (f'.coeff n : ℝ) = (c : ℝ) * (g.coeff n : ℝ) := by exact_mod_cast hcg n
    rw [h1, abs_mul]
    have : (1 : ℝ) ≤ |(c : ℝ)| := by
      have : (1 : ℤ) ≤ |c| := Int.one_le_abs hc0
      exact_mod_cast this
    nlinarith [abs_nonneg ((g.coeff n : ℤ) : ℝ)]
  refine ⟨k, c, g, hc0, ⟨s, hsr, hgdec⟩, hgneg, hg0, hprime, ?_⟩
  have hfg : f' = (c : LaurentSeries ℤ) * g := by
    ext n
    have : ((c : LaurentSeries ℤ) * g).coeff n = c * g.coeff n := by
      rw [show (c : LaurentSeries ℤ) = HahnSeries.C c by simp, HahnSeries.C_mul_eq_smul,
        HahnSeries.coeff_smul]
      rfl
    rw [this, hcg n]
  have hff : f = HahnSeries.single k (1 : ℤ) * f' := by
    rw [hf', ← mul_assoc, HahnSeries.single_mul_single]
    simp
  rw [hff, hfg, mul_assoc]


/-- evalC as a sum over ℕ for a series with no negative terms. -/
theorem h2_evalC_nat (g : LaurentSeries ℤ) (hneg : ∀ n : ℤ, n < 0 → g.coeff n = 0) (y : ℂ) :
    evalC y g = ∑' n : ℕ, ((g.coeff (n : ℤ) : ℤ) : ℂ) * y ^ n := by
  unfold evalC
  rw [← Function.Injective.tsum_eq (f := fun n : ℤ => ((g.coeff n : ℤ) : ℂ) * y ^ n)
    Nat.cast_injective]
  · simp only [zpow_natCast]
  · intro n hn
    by_contra hn'
    have : n < 0 := by
      by_contra h
      apply hn'
      exact ⟨n.toNat, by simp; omega⟩
    apply hn
    simp [hneg n this]

theorem h2_arch_finite (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (g : LaurentSeries ℤ)
    (hg : g ∈ zLaurentGT r) (hneg : ∀ n : ℤ, n < 0 → g.coeff n = 0) (hg0 : g.coeff 0 ≠ 0) :
    {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ ≤ r ∧ evalC y g = 0}.Finite := by
  obtain ⟨s, hsr, hs⟩ := hg
  have hs0 : 0 < s := hr0.trans hsr
  set s' : ℝ := (r + s) / 2 with hs'
  have hrs' : r < s' := by rw [hs']; linarith
  have hs's : s' < s := by rw [hs']; linarith
  have hs'0 : 0 < s' := hr0.trans hrs'
  -- bound
  have hnat : Tendsto (fun n : ℕ => |((g.coeff (n : ℤ) : ℤ) : ℝ)| * s ^ (n : ℤ)) atTop (𝓝 0) :=
    hs.comp tendsto_natCast_atTop_atTop
  obtain ⟨C, hC⟩ := hnat.bddAbove_range
  have hC' : ∀ n : ℕ, |((g.coeff (n : ℤ) : ℤ) : ℝ)| * s ^ n ≤ C := fun n => by
    simpa using hC ⟨n, rfl⟩
  set q : ℝ := s' / s with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hs0]; exact hs's
  have hsum : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left C
  set F : ℕ → ℂ → ℂ := fun n z => ((g.coeff (n : ℤ) : ℤ) : ℂ) * z ^ n with hF
  have hdiff : DifferentiableOn ℂ (fun z => ∑' n : ℕ, F n z) (Metric.ball 0 s') := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun n => ?_) Metric.isOpen_ball
      (fun n z hz => ?_)
    · exact (differentiable_const _ |>.mul (differentiable_pow n)).differentiableOn
    · have hz' : ‖z‖ ≤ s' := by
        have := mem_ball_zero_iff.1 hz; exact this.le
      simp only [hF, norm_mul, norm_pow, Complex.norm_intCast]
      have h1 : ‖z‖ ^ n ≤ s' ^ n := pow_le_pow_left₀ (norm_nonneg _) hz' n
      have h2 : |((g.coeff (n : ℤ) : ℤ) : ℝ)| * s' ^ n ≤ C * q ^ n := by
        have : s' ^ n = s ^ n * q ^ n := by
          rw [← mul_pow, hq]; congr 1; field_simp
        rw [this, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hC' n) (pow_nonneg hq0 n)
      calc _ ≤ |((g.coeff (n : ℤ) : ℤ) : ℝ)| * s' ^ n :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ _ := h2
  have hana : AnalyticOnNhd ℂ (fun z => ∑' n : ℕ, F n z) (Metric.ball 0 s') :=
    hdiff.analyticOnNhd Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℂ) s') :=
    (convex_ball (0 : ℂ) s').isPreconnected
  have hF0 : (∑' n : ℕ, F n 0) = (g.coeff 0 : ℂ) := by
    rw [tsum_eq_single 0]
    · simp [hF]
    · intro n hn; simp [hF, zero_pow hn]
  have hcase := hana.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) s' := Metric.mem_ball_self hs'0
  rcases hcase with h | h
  · exfalso
    have := h hmem0
    simp only [Pi.zero_apply] at this
    rw [hF0] at this
    exact hg0 (by exact_mod_cast this)
  · have hKU : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) s' :=
      Metric.closedBall_subset_ball hrs'
    have hK : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
    have hmono := Filter.codiscreteWithin_mono hKU
    have hcod : {z : ℂ | (∑' n : ℕ, F n z) ≠ 0} ∈ Filter.codiscreteWithin (Metric.closedBall (0 : ℂ) r) :=
      hmono h
    have hfin := hK.finite_sdiff_of_mem_codiscreteWithin hcod
    refine hfin.subset ?_
    rintro y ⟨hy0, hyr, hy⟩
    refine ⟨mem_closedBall_zero_iff.2 hyr, ?_⟩
    simp only [Set.mem_ofPred_eq, not_not]
    rw [h2_evalC_nat g hneg y] at hy
    exact hy

end AnalyticGeometry

/-! ## Part 5 (session 3): constant-term ideal route.
For a nonzero prime `P`, the constant terms of power series in `P` form an ideal `dℤ` of `ℤ`;
an element `h ∈ P` with `h(0) = d` and no archimedean zero (after stripping the archimedean
generators, `g5_strip`) generates `P` (`g5_div`: formal division with integral quotient, the
quotient converging past `r` because `h` has no zero on the closed disc). -/

namespace AnalyticGeometry

/-- an element of `ℤ((T))_{>r}` as an element of the subring `R`. -/
def g5R (r : ℝ) (R : Subring (LaurentSeries ℤ)) (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r)
    (f : LaurentSeries ℤ) (hf : f ∈ zLaurentGT r) : R :=
  ⟨f, by rw [← SetLike.mem_coe, hR]; exact hf⟩

theorem g5_ev_ps (z : ℂ) (G : PowerSeries ℤ) :
    evalC z (G : LaurentSeries ℤ) = ∑' k : ℕ, ((PowerSeries.coeff k G : ℤ) : ℂ) * z ^ k := by
  rw [h2_evalC_nat (G : LaurentSeries ℤ) (fun n hn => by
    rw [PowerSeries.coeff_coe, if_pos hn]) z]
  simp only [LaurentSeries.coeff_coe_powerSeries]

theorem g5_ev_zero (G : PowerSeries ℤ) :
    evalC 0 (G : LaurentSeries ℤ) = ((PowerSeries.constantCoeff G : ℤ) : ℂ) := by
  rw [g5_ev_ps, tsum_eq_single 0]
  · simp
  · intro n hn; simp [zero_pow hn]

theorem g5_ext (r : ℝ) (f g : LaurentSeries ℤ) (hf : f ∈ zLaurentGT r) (hg : g ∈ zLaurentGT r) :
    ∃ t > r, f ∈ zLaurentGT t ∧ g ∈ zLaurentGT t := by
  obtain ⟨s1, hs1, hd1⟩ := hf
  obtain ⟨s2, hs2, hd2⟩ := hg
  have hm := lt_min hs1 hs2
  have hm1 := min_le_left s1 s2
  have hm2 := min_le_right s1 s2
  refine ⟨(r + min s1 s2) / 2, by linarith, ⟨s1, by linarith, hd1⟩, ⟨s2, by linarith, hd2⟩⟩

theorem g5_bound (r : ℝ) (G : PowerSeries ℤ) (hG : (G : LaurentSeries ℤ) ∈ zLaurentGT r) :
    ∃ t > r, ∃ C, ∀ k, ‖((PowerSeries.coeff k G : ℤ) : ℂ)‖ * t ^ k ≤ C := by
  obtain ⟨s, hsr, hs⟩ := hG
  have hs' : Tendsto (fun n : ℤ => |(((G : LaurentSeries ℤ).coeff n : ℤ) : ℝ)| * s ^ n)
      atTop (𝓝 0) := hs
  have h1 := hs'.comp tendsto_natCast_atTop_atTop
  obtain ⟨B, hB⟩ := h1.bddAbove_range
  refine ⟨s, hsr, B, fun k => ?_⟩
  have := hB ⟨k, rfl⟩
  simp only [Function.comp_apply, LaurentSeries.coeff_coe_powerSeries, zpow_natCast] at this
  rw [Complex.norm_intCast]
  exact this

theorem g5_ana (t : ℝ) (ht : 0 < t) (G : PowerSeries ℤ)
    (hG : (G : LaurentSeries ℤ) ∈ zLaurentGT t) :
    AnalyticOnNhd ℂ (fun z => evalC z (G : LaurentSeries ℤ)) (Metric.ball 0 t) := by
  obtain ⟨s, hst, hs⟩ := hG
  have hs0 : 0 < s := ht.trans hst
  have hs' : Tendsto (fun n : ℤ => |(((G : LaurentSeries ℤ).coeff n : ℤ) : ℝ)| * s ^ n)
      atTop (𝓝 0) := hs
  obtain ⟨C, hC⟩ := (hs'.comp tendsto_natCast_atTop_atTop).bddAbove_range
  have hC' : ∀ n : ℕ, |((PowerSeries.coeff n G : ℤ) : ℝ)| * s ^ n ≤ C := fun n => by
    have := hC ⟨n, rfl⟩
    simpa only [Function.comp_apply, LaurentSeries.coeff_coe_powerSeries, zpow_natCast]
      using this
  set q : ℝ := t / s with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hs0]; exact hst
  have hsum : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left C
  have hfun : (fun z => evalC z (G : LaurentSeries ℤ)) =
      (fun z => ∑' n : ℕ, ((PowerSeries.coeff n G : ℤ) : ℂ) * z ^ n) :=
    funext (fun z => g5_ev_ps z G)
  rw [hfun]
  have hdiff : DifferentiableOn ℂ (fun z => ∑' n : ℕ, ((PowerSeries.coeff n G : ℤ) : ℂ) * z ^ n)
      (Metric.ball 0 t) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun n => ?_) Metric.isOpen_ball
      (fun n z hz => ?_)
    · exact (differentiable_const _ |>.mul (differentiable_pow n)).differentiableOn
    · have hz' : ‖z‖ ≤ t := (mem_ball_zero_iff.1 hz).le
      rw [norm_mul, norm_pow, Complex.norm_intCast]
      have h1 : ‖z‖ ^ n ≤ t ^ n := pow_le_pow_left₀ (norm_nonneg _) hz' n
      have h2 : |((PowerSeries.coeff n G : ℤ) : ℝ)| * t ^ n ≤ C * q ^ n := by
        have : t ^ n = s ^ n * q ^ n := by
          rw [← mul_pow, hq]; congr 1; field_simp
        rw [this, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hC' n) (pow_nonneg hq0 n)
      calc _ ≤ |((PowerSeries.coeff n G : ℤ) : ℝ)| * t ^ n :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ _ := h2
  exact hdiff.analyticOnNhd Metric.isOpen_ball

theorem g5_ord_fin (r : ℝ) (hr0 : 0 < r) (G : PowerSeries ℤ)
    (hG : (G : LaurentSeries ℤ) ∈ zLaurentGT r)
    (hG0 : PowerSeries.constantCoeff G ≠ 0) (y : ℂ) (hy : ‖y‖ ≤ r) :
    AnalyticAt ℂ (fun z => evalC z (G : LaurentSeries ℤ)) y ∧
      analyticOrderAt (fun z => evalC z (G : LaurentSeries ℤ)) y ≠ ⊤ := by
  obtain ⟨t, htr, hGt, -⟩ := g5_ext r _ _ hG hG
  have ht0 : 0 < t := hr0.trans htr
  have hA := g5_ana t ht0 G hGt
  have hyB : y ∈ Metric.ball (0 : ℂ) t := mem_ball_zero_iff.2 (lt_of_le_of_lt hy htr)
  refine ⟨hA y hyB, fun htop => ?_⟩
  have hev := analyticOrderAt_eq_top.1 htop
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) t).isPreconnected hyB hev
  have h0 := hEq (Metric.mem_ball_self ht0)
  simp only [Pi.zero_apply] at h0
  rw [g5_ev_zero] at h0
  exact hG0 (by exact_mod_cast h0)

theorem g5_mul_near (r : ℝ) (hr0 : 0 < r) (F H : PowerSeries ℤ)
    (hF : (F : LaurentSeries ℤ) ∈ zLaurentGT r) (hH : (H : LaurentSeries ℤ) ∈ zLaurentGT r)
    (y : ℂ) (hy0 : y ≠ 0) (hy : ‖y‖ ≤ r) :
    (fun z => evalC z ((F * H : PowerSeries ℤ) : LaurentSeries ℤ)) =ᶠ[𝓝 y]
      (fun z => evalC z (F : LaurentSeries ℤ)) * (fun z => evalC z (H : LaurentSeries ℤ)) := by
  obtain ⟨t, htr, hFt, hHt⟩ := g5_ext r _ _ hF hH
  have ht0 : 0 < t := hr0.trans htr
  have h2 : ∀ᶠ z in 𝓝 y, ‖z‖ < t :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (lt_of_le_of_lt hy htr)
  filter_upwards [eventually_ne_nhds hy0, h2] with z hz0 hzt
  simp only [Pi.mul_apply, PowerSeries.coe_mul]
  exact h4_evalC_mul t ht0 z hz0 hzt.le _ _ hFt hHt

/-- **Archimedean stripping** (strong induction on the total order of the zeros in `S`). -/
theorem g5_strip (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (R : Subring (LaurentSeries ℤ))
    (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r) (P : Ideal R) (hP : P.IsPrime)
    (d : ℤ) (hd : d ≠ 0) (S : Finset ℂ) (hS : ∀ y ∈ S, y ≠ 0 ∧ ‖y‖ ≤ r) :
    ∀ n : ℕ, ∀ g : PowerSeries ℤ, ∀ hg : (g : LaurentSeries ℤ) ∈ zLaurentGT r,
      PowerSeries.constantCoeff g = d → g5R r R hR _ hg ∈ P →
      (∀ y : ℂ, 0 < ‖y‖ → ‖y‖ ≤ r → evalC y (g : LaurentSeries ℤ) = 0 → y ∈ S) →
      ∑ y ∈ S, (analyticOrderAt (fun z => evalC z (g : LaurentSeries ℤ)) y).toNat = n →
      P.IsPrincipal ∨ ∃ g' : PowerSeries ℤ, ∃ hg' : (g' : LaurentSeries ℤ) ∈ zLaurentGT r,
        PowerSeries.constantCoeff g' = d ∧
        (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r → evalC z (g' : LaurentSeries ℤ) ≠ 0) ∧
        g5R r R hR _ hg' ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hg hg0 hgP hgS hsum
  by_cases hfree : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r → evalC z (g : LaurentSeries ℤ) ≠ 0
  · exact Or.inr ⟨g, hg, hg0, hfree, hgP⟩
  push_neg at hfree
  obtain ⟨y, hy0, hyr, hgy⟩ := hfree
  have hy0' : y ≠ 0 := norm_pos_iff.1 hy0
  obtain ⟨F, hF0, hFb, hFz, hFdiv, hmax⟩ := h4_arch r hr0 hr1 R hR y hy0' hyr
  have hFm : (F : LaurentSeries ℤ) ∈ zLaurentGT r := h3_mem_of_bound r hr0 F hFb
  obtain ⟨h1', hh1', hgeq⟩ := (hFdiv _ hg).1 hgy
  set H : PowerSeries ℤ := PowerSeries.invOfUnit F 1 * g with hHdef
  have hFinv : F * PowerSeries.invOfUnit F 1 = 1 :=
    PowerSeries.mul_invOfUnit F 1 (by simp [hF0])
  have hFH : F * H = g := by rw [hHdef, ← mul_assoc, hFinv, one_mul]
  have hFne : (F : LaurentSeries ℤ) ≠ 0 := by
    intro h
    have := LaurentSeries.coeff_coe_powerSeries F 0
    rw [h] at this
    simp [hF0] at this
  have hHeq : (H : LaurentSeries ℤ) = h1' := by
    apply mul_left_cancel₀ hFne
    rw [← PowerSeries.coe_mul, hFH, hgeq]
  have hHm : (H : LaurentSeries ℤ) ∈ zLaurentGT r := hHeq ▸ hh1'
  have hprod : g5R r R hR _ hg = g5R r R hR _ hFm * g5R r R hR _ hHm := by
    apply Subtype.ext
    simp only [g5R, MulMemClass.coe_mul]
    rw [← PowerSeries.coe_mul, hFH]
  rw [hprod] at hgP
  rcases hP.mem_or_mem hgP with hFP | hHP
  · left
    have hker_le : RingHom.ker (h4_ev r hr0 R hR y hy0' hyr) ≤
        Ideal.span {g5R r R hR _ hFm} := by
      intro a ha
      rw [RingHom.mem_ker] at ha
      have ha' : evalC y (a : LaurentSeries ℤ) = 0 := ha
      have hamem : (a : LaurentSeries ℤ) ∈ zLaurentGT r := by rw [← hR]; exact a.2
      obtain ⟨b, hb, hab⟩ := (hFdiv _ hamem).1 ha'
      refine Ideal.mem_span_singleton'.2 ⟨g5R r R hR _ hb, ?_⟩
      apply Subtype.ext
      simp only [g5R, MulMemClass.coe_mul]
      rw [hab, mul_comm]
    have hspan_le : Ideal.span {g5R r R hR _ hFm} ≤ P :=
      (Ideal.span_singleton_le_iff_mem P).2 hFP
    have hPeq : RingHom.ker (h4_ev r hr0 R hR y hy0' hyr) = P :=
      hmax.eq_of_le hP.ne_top (hker_le.trans hspan_le)
    refine ⟨⟨g5R r R hR _ hFm, le_antisymm ?_ hspan_le⟩⟩
    rw [← hPeq]
    exact hker_le
  · have hH0 : PowerSeries.constantCoeff H = d := by
      rw [hHdef, map_mul, PowerSeries.constantCoeff_invOfUnit, hg0]
      simp
    have hevmul : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r → evalC z (g : LaurentSeries ℤ) =
        evalC z (F : LaurentSeries ℤ) * evalC z (H : LaurentSeries ℤ) := by
      intro z hz hzr
      rw [← hFH, PowerSeries.coe_mul]
      exact h4_evalC_mul r hr0 z (norm_pos_iff.1 hz) hzr _ _ hFm hHm
    have hHS : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r → evalC z (H : LaurentSeries ℤ) = 0 → z ∈ S := by
      intro z hz hzr hHz
      exact hgS z hz hzr (by rw [hevmul z hz hzr, hHz, mul_zero])
    have hFc : PowerSeries.constantCoeff F ≠ 0 := by rw [hF0]; exact one_ne_zero
    have hHc : PowerSeries.constantCoeff H ≠ 0 := by rw [hH0]; exact hd
    have hord : ∀ x ∈ S, analyticOrderAt (fun z => evalC z (g : LaurentSeries ℤ)) x =
        analyticOrderAt (fun z => evalC z (F : LaurentSeries ℤ)) x +
          analyticOrderAt (fun z => evalC z (H : LaurentSeries ℤ)) x := by
      intro x hx
      obtain ⟨hx0, hxr⟩ := hS x hx
      have hFa := g5_ord_fin r hr0 F hFm hFc x hxr
      have hHa := g5_ord_fin r hr0 H hHm hHc x hxr
      rw [← analyticOrderAt_mul hFa.1 hHa.1]
      apply analyticOrderAt_congr
      have := g5_mul_near r hr0 F H hFm hHm x hx0 hxr
      rw [hFH] at this
      exact this
    have hyS := hgS y hy0 hyr hgy
    have hlt : ∑ x ∈ S, (analyticOrderAt (fun z => evalC z (H : LaurentSeries ℤ)) x).toNat <
        ∑ x ∈ S, (analyticOrderAt (fun z => evalC z (g : LaurentSeries ℤ)) x).toNat := by
      apply Finset.sum_lt_sum
      · intro x hx
        rw [hord x hx]
        obtain ⟨hx0, hxr⟩ := hS x hx
        have hFf := (g5_ord_fin r hr0 F hFm hFc x hxr).2
        have hHf := (g5_ord_fin r hr0 H hHm hHc x hxr).2
        rw [ENat.toNat_add hFf hHf]
        omega
      · refine ⟨y, hyS, ?_⟩
        rw [hord y hyS]
        have hFa := g5_ord_fin r hr0 F hFm hFc y hyr
        have hHf := (g5_ord_fin r hr0 H hHm hHc y hyr).2
        have hFy : evalC y (F : LaurentSeries ℤ) = 0 := by
          rw [g5_ev_ps]; exact (hFz y hyr).2 (Or.inl rfl)
        have hF1 : analyticOrderAt (fun z => evalC z (F : LaurentSeries ℤ)) y ≠ 0 :=
          analyticOrderAt_ne_zero.2 ⟨hFa.1, hFy⟩
        rw [ENat.toNat_add hFa.2 hHf]
        have : (analyticOrderAt (fun z => evalC z (F : LaurentSeries ℤ)) y).toNat ≠ 0 := by
          intro h0
          rcases ENat.toNat_eq_zero.1 h0 with h | h
          · exact hF1 h
          · exact hFa.2 h
        omega
    exact ih _ (lt_of_lt_of_eq hlt hsum) H hHm hH0 hHP hHS rfl

/-- **Division** by a zero-free generator of the constant-term ideal. -/
theorem g5_div (r : ℝ) (hr0 : 0 < r) (R : Subring (LaurentSeries ℤ))
    (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r) (P : Ideal R) (d : ℤ) (hd : d ≠ 0)
    (hI : ∀ f : PowerSeries ℤ, ∀ hf : (f : LaurentSeries ℤ) ∈ zLaurentGT r,
      g5R r R hR _ hf ∈ P → d ∣ PowerSeries.constantCoeff f)
    (h : PowerSeries ℤ) (hh : (h : LaurentSeries ℤ) ∈ zLaurentGT r)
    (hh0 : PowerSeries.constantCoeff h = d) (hhP : g5R r R hR _ hh ∈ P)
    (hfree : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r → evalC z (h : LaurentSeries ℤ) ≠ 0)
    (f : PowerSeries ℤ) (hf : (f : LaurentSeries ℤ) ∈ zLaurentGT r)
    (hfP : g5R r R hR _ hf ∈ P) :
    ∃ q : PowerSeries ℤ, (q : LaurentSeries ℤ) ∈ zLaurentGT r ∧ f = h * q := by
  set φ : ℤ →+* ℂ := Int.castRingHom ℂ with hφ
  obtain ⟨th, hth, Ch, hCh⟩ := g5_bound r h hh
  obtain ⟨tf, htf, Cf, hCf⟩ := g5_bound r f hf
  have hz : ∀ z : ℂ, ‖z‖ ≤ r → ∑' k, ((PowerSeries.coeff k h : ℤ) : ℂ) * z ^ k ≠ 0 := by
    intro z hzr
    rw [← g5_ev_ps]
    by_cases hz0 : z = 0
    · rw [hz0, g5_ev_zero, hh0]; exact_mod_cast hd
    · exact hfree z (norm_pos_iff.2 hz0) hzr
  obtain ⟨v, hv, tv, htv, Cv, hCv⟩ :=
    h3_inv_bound r hr0 (fun k => ((PowerSeries.coeff k h : ℤ) : ℂ)) th Ch hth hCh hz
  set t := min tf tv with ht
  have htr : r < t := lt_min htf htv
  have hfb : ∀ k, ‖((PowerSeries.coeff k f : ℤ) : ℂ)‖ * t ^ k ≤ Cf :=
    h3_bound_mono (fun k => ((PowerSeries.coeff k f : ℤ) : ℂ)) tf t Cf (by linarith)
      (min_le_left _ _) hCf
  have hvb : ∀ k, ‖v k‖ * t ^ k ≤ Cv :=
    h3_bound_mono v tv t Cv (by linarith) (min_le_right _ _) hCv
  obtain ⟨E, hE⟩ := h3_mul_bound (fun k => ((PowerSeries.coeff k f : ℤ) : ℂ)) v t ((r + t) / 2)
    Cf Cv (by linarith) (by linarith) hfb hvb
  set qC := PowerSeries.mk (fun k => ((PowerSeries.coeff k f : ℤ) : ℂ)) * PowerSeries.mk v
    with hqC
  have hE0 : 0 ≤ E := le_trans (by positivity) (hE 0)
  have hmkh : PowerSeries.mk (fun k => ((PowerSeries.coeff k h : ℤ) : ℂ)) =
      PowerSeries.map φ h := by
    ext k; simp [hφ, PowerSeries.coeff_map]
  have hmkf : PowerSeries.mk (fun k => ((PowerSeries.coeff k f : ℤ) : ℂ)) =
      PowerSeries.map φ f := by
    ext k; simp [hφ, PowerSeries.coeff_map]
  have hhq : PowerSeries.map φ h * qC = PowerSeries.map φ f := by
    rw [hqC, ← hmkh, ← hmkf, mul_left_comm, hv, mul_one]
  have h1m : (1 : LaurentSeries ℤ) ∈ zLaurentGT r := by rw [← hR]; exact R.one_mem
  set qz : ℕ → ℤ := fun k => round ((PowerSeries.coeff k qC).re) with hqz
  have hint : ∀ n, ((qz n : ℤ) : ℂ) = PowerSeries.coeff n qC := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    set Q : PowerSeries ℤ := PowerSeries.mk (fun i => if i < n then qz i else 0) with hQ
    have hQm : (Q : LaurentSeries ℤ) ∈ zLaurentGT r := by
      apply h3_mem_of_bound r hr0 Q
      refine ⟨(r + t) / 2, by linarith, E, fun k => ?_⟩
      rw [hQ, PowerSeries.coeff_mk]
      split_ifs with hk
      · rw [ih k hk]; exact hE k
      · simp only [Int.cast_zero, norm_zero, zero_mul]; exact hE0
    set s : PowerSeries ℤ := f - h * Q with hs
    have hsC : PowerSeries.map φ s = PowerSeries.map φ h * (qC - PowerSeries.map φ Q) := by
      rw [hs, map_sub, map_mul, mul_sub, hhq]
    have hqQ : ∀ m < n, PowerSeries.coeff m (qC - PowerSeries.map φ Q) = 0 := by
      intro m hm
      rw [map_sub, PowerSeries.coeff_map, hQ, PowerSeries.coeff_mk, if_pos hm, ← ih m hm]
      simp [hφ]
    obtain ⟨w, hw⟩ : PowerSeries.X ^ n ∣ qC - PowerSeries.map φ Q :=
      PowerSeries.X_pow_dvd_iff.2 hqQ
    have hcs : ∀ m, ((PowerSeries.coeff m s : ℤ) : ℂ) = PowerSeries.coeff m (PowerSeries.map φ s) := by
      intro m; rw [PowerSeries.coeff_map]; simp [hφ]
    have hsdvd : PowerSeries.X ^ n ∣ s := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      apply Int.cast_injective (α := ℂ)
      rw [hcs, hsC, hw, mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
      simp
    obtain ⟨s', hs'⟩ := hsdvd
    set x : R := g5R r R hR _ hf - g5R r R hR _ hh * g5R r R hR _ hQm with hx
    have hxs : (x : LaurentSeries ℤ) = (s : LaurentSeries ℤ) := by
      simp only [hx, hs, g5R, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, PowerSeries.coe_sub,
        PowerSeries.coe_mul]
    have hxP : x ∈ P := P.sub_mem hfP (P.mul_mem_right _ hhP)
    have hsm : (s : LaurentSeries ℤ) ∈ zLaurentGT r := by
      rw [← hxs, ← hR]; exact x.2
    have hs'L : (s' : LaurentSeries ℤ) =
        HahnSeries.single (-(n : ℤ)) (1 : ℤ) * (s : LaurentSeries ℤ) := by
      rw [hs', PowerSeries.coe_mul, ← mul_assoc]
      have : ((PowerSeries.X ^ n : PowerSeries ℤ) : LaurentSeries ℤ) =
          HahnSeries.single (n : ℤ) (1 : ℤ) := HahnSeries.ofPowerSeries_X_pow n
      rw [this, HahnSeries.single_mul_single, neg_add_cancel, mul_one]
      simp
    have hs'm : (s' : LaurentSeries ℤ) ∈ zLaurentGT r := by
      obtain ⟨σ, hσ, hσd⟩ := hsm
      exact ⟨σ, hσ, hs'L ▸ h1_decays_shift (hr0.trans hσ) (n : ℤ) hσd⟩
    have hum : HahnSeries.single (-(n : ℤ)) (1 : ℤ) ∈ zLaurentGT r := by
      obtain ⟨σ, hσ, hσd⟩ := h1m
      have := h1_decays_shift (hr0.trans hσ) (n : ℤ) hσd
      rw [mul_one] at this
      exact ⟨σ, hσ, this⟩
    have hs'P : g5R r R hR _ hs'm ∈ P := by
      have : g5R r R hR _ hs'm = g5R r R hR _ hum * x := by
        apply Subtype.ext
        simp only [g5R, MulMemClass.coe_mul]
        rw [hxs, hs'L]
      rw [this]; exact P.mul_mem_left _ hxP
    obtain ⟨k, hk⟩ := hI s' hs'm hs'P
    have hw0 : PowerSeries.constantCoeff w = PowerSeries.coeff n qC := by
      have := congrArg (PowerSeries.coeff n) hw
      rw [PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, PowerSeries.coeff_map, hQ,
        PowerSeries.coeff_mk, if_neg (lt_irrefl n)] at this
      rw [← this]; simp
    have hcn : ((PowerSeries.constantCoeff s' : ℤ) : ℂ) = (d : ℂ) * PowerSeries.coeff n qC := by
      have e1 : ((PowerSeries.constantCoeff s' : ℤ) : ℂ) =
          PowerSeries.coeff n (PowerSeries.map φ s) := by
        rw [← hcs, hs', PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [e1, hsC, hw, mul_left_comm, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hw0]
      congr 1
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hh0]
      simp [hφ]
    have hqn : PowerSeries.coeff n qC = (k : ℂ) := by
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
      apply mul_left_cancel₀ hd'
      rw [← hcn, hk]; push_cast; ring
    show ((round ((PowerSeries.coeff n qC).re) : ℤ) : ℂ) = _
    rw [hqn]
    simp
  refine ⟨PowerSeries.mk qz, ?_, ?_⟩
  · apply h3_mem_of_bound r hr0
    refine ⟨(r + t) / 2, by linarith, E, fun k => ?_⟩
    rw [PowerSeries.coeff_mk, hint k]
    exact hE k
  · have hmap : PowerSeries.map φ (PowerSeries.mk qz) = qC := by
      ext k; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, ← hint k]; simp [hφ]
    apply PowerSeries.map_injective φ Int.cast_injective
    rw [map_mul, hmap, hhq]

/-- normal form with an explicit power series. -/
theorem g5_nf (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (x : LaurentSeries ℤ)
    (hx : x ∈ zLaurentGT r) (hx0 : x ≠ 0) :
    ∃ k : ℤ, ∃ G : PowerSeries ℤ, (G : LaurentSeries ℤ) ∈ zLaurentGT r ∧
      PowerSeries.constantCoeff G ≠ 0 ∧
      x = HahnSeries.single k (1 : ℤ) * (G : LaurentSeries ℤ) := by
  obtain ⟨k, c, g, hc, hg, hneg, hg0, -, hxe⟩ := h1_normal_form r hr0 hr1 x hx hx0
  set G : PowerSeries ℤ := PowerSeries.mk (fun n => c * g.coeff (n : ℤ)) with hG
  have hcg : ∀ n : ℤ, ((c : LaurentSeries ℤ) * g).coeff n = c * g.coeff n := by
    intro n
    have : (c : LaurentSeries ℤ) = HahnSeries.C c := by simp
    rw [this, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  have hGL : (G : LaurentSeries ℤ) = (c : LaurentSeries ℤ) * g := by
    ext n
    rw [PowerSeries.coeff_coe, hcg]
    split_ifs with hn
    · rw [hneg n hn, mul_zero]
    · rw [hG, PowerSeries.coeff_mk, Int.natAbs_of_nonneg (by omega)]
  have hxG : x = HahnSeries.single k (1 : ℤ) * (G : LaurentSeries ℤ) := by
    rw [hGL, hxe, mul_assoc]
  refine ⟨k, G, ?_, ?_, hxG⟩
  · have hGx : (G : LaurentSeries ℤ) = HahnSeries.single (-k) (1 : ℤ) * x := by
      rw [hxG, ← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one]
      simp
    obtain ⟨σ, hσ, hσd⟩ := hx
    exact ⟨σ, hσ, hGx ▸ h1_decays_shift (hr0.trans hσ) k hσd⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, PowerSeries.coeff_mk]
    exact mul_ne_zero hc (by simpa using hg0)

theorem g5_main (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (R : Subring (LaurentSeries ℤ)) (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r) :
    IsPrincipalIdealRing R := by
  have toRm : ∀ f : LaurentSeries ℤ, f ∈ zLaurentGT r → f ∈ R := fun f hf => by
    rw [← SetLike.mem_coe, hR]; exact hf
  have fromR : ∀ f : LaurentSeries ℤ, f ∈ R → f ∈ zLaurentGT r := fun f hf => by
    rw [← hR]; exact hf
  have h1m : (1 : LaurentSeries ℤ) ∈ zLaurentGT r := fromR _ R.one_mem
  have hsing : ∀ k : ℤ, HahnSeries.single k (1 : ℤ) ∈ zLaurentGT r := by
    intro k
    obtain ⟨σ, hσ, hσd⟩ := h1m
    have := h1_decays_shift (hr0.trans hσ) (-k) hσd
    rw [mul_one, neg_neg] at this
    exact ⟨σ, hσ, this⟩
  apply IsPrincipalIdealRing.of_prime_ne_bot
  intro P hP hPb
  -- every nonzero element of `P` is `T^k` times a power series in `P` with nonzero constant term
  have hPx : ∀ x ∈ P, x ≠ 0 → ∃ k : ℤ, ∃ G : PowerSeries ℤ,
      ∃ hG : (G : LaurentSeries ℤ) ∈ zLaurentGT r, PowerSeries.constantCoeff G ≠ 0 ∧
        g5R r R hR _ hG ∈ P ∧ (x : LaurentSeries ℤ) = HahnSeries.single k (1 : ℤ) * G := by
    intro x hxP hx0
    have hxL : (x : LaurentSeries ℤ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨k, G, hGm, hG0, hxe⟩ := g5_nf r hr0 hr1 _ (fromR _ x.2) hxL
    refine ⟨k, G, hGm, hG0, ?_, hxe⟩
    have : g5R r R hR _ hGm = g5R r R hR _ (hsing (-k)) * x := by
      apply Subtype.ext
      simp only [g5R, MulMemClass.coe_mul]
      rw [hxe, ← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one]
      simp
    rw [this]; exact P.mul_mem_left _ hxP
  -- the ideal of constant terms
  let I : Ideal ℤ :=
    { carrier := {a | ∃ f : PowerSeries ℤ, ∃ hf : (f : LaurentSeries ℤ) ∈ zLaurentGT r,
        g5R r R hR _ hf ∈ P ∧ PowerSeries.constantCoeff f = a}
      add_mem' := by
        rintro a b ⟨f, hf, hfP, rfl⟩ ⟨g, hg, hgP, rfl⟩
        have hfg : ((f + g : PowerSeries ℤ) : LaurentSeries ℤ) ∈ zLaurentGT r := by
          rw [PowerSeries.coe_add]; exact fromR _ (R.add_mem (toRm _ hf) (toRm _ hg))
        refine ⟨f + g, hfg, ?_, map_add _ _ _⟩
        have : g5R r R hR _ hfg = g5R r R hR _ hf + g5R r R hR _ hg := by
          apply Subtype.ext; simp only [g5R, AddMemClass.coe_add, PowerSeries.coe_add]
        rw [this]; exact P.add_mem hfP hgP
      zero_mem' := by
        have h0 : ((0 : PowerSeries ℤ) : LaurentSeries ℤ) ∈ zLaurentGT r := by
          rw [PowerSeries.coe_zero]; exact fromR _ R.zero_mem
        refine ⟨0, h0, ?_, map_zero _⟩
        have : g5R r R hR _ h0 = 0 := by
          apply Subtype.ext; simp only [g5R, PowerSeries.coe_zero, ZeroMemClass.coe_zero]
        rw [this]; exact P.zero_mem
      smul_mem' := by
        rintro c a ⟨f, hf, hfP, rfl⟩
        have hcf : ((PowerSeries.C c * f : PowerSeries ℤ) : LaurentSeries ℤ) =
            (c : LaurentSeries ℤ) * (f : LaurentSeries ℤ) := by
          rw [PowerSeries.coe_mul, PowerSeries.coe_C, eq_intCast]
        have hcm : ((PowerSeries.C c * f : PowerSeries ℤ) : LaurentSeries ℤ) ∈ zLaurentGT r := by
          rw [hcf]; exact fromR _ (R.mul_mem (intCast_mem R c) (toRm _ hf))
        refine ⟨PowerSeries.C c * f, hcm, ?_, ?_⟩
        · have : g5R r R hR _ hcm = (c : R) * g5R r R hR _ hf := by
            apply Subtype.ext
            simp only [g5R, MulMemClass.coe_mul, SubringClass.coe_intCast]
            exact hcf
          rw [this]; exact P.mul_mem_left _ hfP
        · rw [map_mul, PowerSeries.constantCoeff_C, smul_eq_mul] }
  obtain ⟨d, hdI⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ a : ℤ, a ∈ I ↔ d ∣ a := by
    intro a
    rw [hdI]
    exact Ideal.mem_span_singleton
  have hdvd : ∀ f : PowerSeries ℤ, ∀ hf : (f : LaurentSeries ℤ) ∈ zLaurentGT r,
      g5R r R hR _ hf ∈ P → d ∣ PowerSeries.constantCoeff f :=
    fun f hf hfP => (hmemI _).1 ⟨f, hf, hfP, rfl⟩
  have hd0 : d ≠ 0 := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPb
    obtain ⟨k, G, hGm, hG0, hGP, -⟩ := hPx x hxP hx0
    intro hd
    have := hdvd G hGm hGP
    rw [hd, zero_dvd_iff] at this
    exact hG0 this
  obtain ⟨h0, hh0m, hh0P, hh0c⟩ : d ∈ I := (hmemI d).2 dvd_rfl
  have hneg : ∀ n : ℤ, n < 0 → (h0 : LaurentSeries ℤ).coeff n = 0 := by
    intro n hn; rw [PowerSeries.coeff_coe, if_pos hn]
  have hc0 : (h0 : LaurentSeries ℤ).coeff 0 ≠ 0 := by
    have := LaurentSeries.coeff_coe_powerSeries h0 0
    simp only [Nat.cast_zero] at this
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, hh0c]
    exact hd0
  have hfin := h2_arch_finite r hr0 hr1 _ hh0m hneg hc0
  rcases g5_strip r hr0 hr1 R hR P hP d hd0 hfin.toFinset
      (fun y hy => by
        rw [Set.Finite.mem_toFinset] at hy
        exact ⟨norm_pos_iff.1 hy.1, hy.2.1⟩) _ h0 hh0m hh0c hh0P
      (fun y hy hyr hy0 => by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hy, hyr, hy0⟩) rfl with hprin | ⟨h, hhm, hhc, hfree, hhP⟩
  · exact hprin
  refine ⟨⟨g5R r R hR _ hhm, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem P).2 hhP)⟩⟩
  intro x hxP
  by_cases hx0 : x = 0
  · rw [hx0]; exact Submodule.zero_mem _
  obtain ⟨k, G, hGm, -, hGP, hxe⟩ := hPx x hxP hx0
  obtain ⟨q, hqm, hGq⟩ := g5_div r hr0 R hR P d hd0 hdvd h hhm hhc hhP hfree G hGm hGP
  have hqk : HahnSeries.single k (1 : ℤ) * (q : LaurentSeries ℤ) ∈ zLaurentGT r :=
    fromR _ (R.mul_mem (toRm _ (hsing k)) (toRm _ hqm))
  refine Ideal.mem_span_singleton'.2 ⟨⟨_, toRm _ hqk⟩, Subtype.ext ?_⟩
  simp only [MulMemClass.coe_mul, g5R]
  rw [hxe, hGq, PowerSeries.coe_mul]
  ring

end AnalyticGeometry

open AnalyticGeometry in
theorem solution (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (R : Subring (LaurentSeries ℤ)) (hR : (R : Set (LaurentSeries ℤ)) = zLaurentGT r) :
    IsPrincipalIdealRing R := by
  exact AnalyticGeometry.g5_main r hr0 hr1 R hR
