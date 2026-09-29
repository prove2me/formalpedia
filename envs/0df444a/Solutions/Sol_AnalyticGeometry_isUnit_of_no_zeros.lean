-- Prove2me | solution 1 for AnalyticGeometry.isUnit_of_no_zeros
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:24:48.506306+00:00
-- url     : https://prove2.me/submissions/316c42f9-bc7d-4489-973e-155b2714c004

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

set_option autoImplicit false

open Filter Topology Metric

lemma AGiu_decays_of_nat {s : ℝ} (g : LaurentSeries ℤ)
    (h : Tendsto (fun n : ℕ => |(g.coeff (n : ℤ) : ℝ)| * s ^ n) atTop (𝓝 0)) :
    AnalyticGeometry.DecaysAt s g := by
  unfold AnalyticGeometry.DecaysAt
  have ht : Tendsto (fun n : ℤ => n.toNat) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun n hn => by omega⟩)
  refine (h.comp ht).congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℤ)] with n hn
  simp only [Function.comp_apply]
  rw [← zpow_natCast, Int.toNat_of_nonneg hn]

open AnalyticGeometry in
theorem solution (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (f : LaurentSeries ℤ)
    (hf : f ∈ zLaurentGT r) (hf0 : f.coeff 0 = 1) (hfneg : ∀ n : ℤ, n < 0 → f.coeff n = 0)
    (hzero : ∀ y : ℂ, 0 < ‖y‖ → ‖y‖ ≤ r → evalC y f ≠ 0) :
    ∃ g ∈ zLaurentGT r, f * g = 1 := by
  obtain ⟨s, hsr, hs⟩ := hf
  have hs0 : 0 < s := by linarith
  -- the formal inverse in `ℤ⟦X⟧`
  set P : PowerSeries ℤ := PowerSeries.mk (fun n : ℕ => f.coeff (n : ℤ)) with hP
  have hPf : (P : LaurentSeries ℤ) = f := by
    ext n
    rw [PowerSeries.coeff_coe]
    split_ifs with hn
    · exact (hfneg n hn).symm
    · rw [hP, PowerSeries.coeff_mk]
      congr 1
      omega
  have hPc : PowerSeries.constantCoeff P = ((1 : ℤˣ) : ℤ) := by
    rw [hP, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simpa using hf0
  set G : PowerSeries ℤ := PowerSeries.invOfUnit P 1 with hG
  have hPG : P * G = 1 := PowerSeries.mul_invOfUnit P 1 hPc
  refine ⟨(G : LaurentSeries ℤ), ?_, ?_⟩
  swap
  · rw [← hPf, ← PowerSeries.coe_mul, hPG, PowerSeries.coe_one]
  -- the holomorphic function `F` defined by `f` on the disc of radius `s`
  set c : ℕ → ℂ := fun n => (f.coeff (n : ℤ) : ℂ) with hc
  set pF : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hpF
  set sN : NNReal := ⟨s, hs0.le⟩ with hsN
  have hsN0 : (0 : ENNReal) < (sN : ENNReal) :=
    ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hs0)
  have hsnat : Tendsto (fun n : ℕ => |(f.coeff (n : ℤ) : ℝ)| * s ^ n) atTop (𝓝 0) := by
    have := hs.comp tendsto_natCast_atTop_atTop
    refine this.congr (fun n => ?_)
    simp [Function.comp_apply, zpow_natCast]
  have hradF : (sN : ENNReal) ≤ pF.radius := by
    refine pF.le_radius_of_tendsto (l := 0) ?_
    refine hsnat.congr (fun n => ?_)
    rw [hpF, FormalMultilinearSeries.ofScalars_norm, hc]
    simp only [Complex.norm_intCast]
    rfl
  set F : ℂ → ℂ := pF.sum with hFdef
  have hF : HasFPowerSeriesOnBall F pF 0 sN :=
    (pF.hasFPowerSeriesOnBall (lt_of_lt_of_le hsN0 hradF)).mono hsN0 hradF
  have hFeval : ∀ z : ℂ, evalC z f = F z := by
    intro z
    have hsupp : Function.support (fun n : ℤ => (f.coeff n : ℂ) * z ^ n) ⊆
        Set.range (Nat.cast : ℕ → ℤ) := by
      intro n hn
      by_cases h0 : 0 ≤ n
      · exact ⟨n.toNat, Int.toNat_of_nonneg h0⟩
      · exfalso
        apply hn
        simp [hfneg n (by omega)]
    rw [evalC]
    refine ((Nat.cast_injective (R := ℤ)).tsum_eq hsupp).symm.trans ?_
    show ∑' k : ℕ, (f.coeff (k : ℤ) : ℂ) * z ^ (k : ℤ) = ∑' k : ℕ, pF k (fun _ => z)
    congr 1
    funext k
    rw [hpF, FormalMultilinearSeries.ofScalars_apply_eq, hc, smul_eq_mul, zpow_natCast]
  have hF0 : F 0 = 1 := by
    show FormalMultilinearSeries.ofScalarsSum (E := ℂ) c 0 = 1
    rw [FormalMultilinearSeries.ofScalarsSum_zero]
    simp [hc, hf0]
  have hFne : ∀ z : ℂ, ‖z‖ ≤ r → F z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, hF0]; exact one_ne_zero
    · rw [← hFeval]; exact hzero z (norm_pos_iff.2 hz0) hz
  have hdiffF : DifferentiableOn ℂ F (ball (0:ℂ) s) := by
    have := hF.differentiableOn
    rw [Metric.eball_coe] at this
    exact this
  -- `F` has no zero on a slightly larger closed disc
  have hU : IsOpen (ball (0:ℂ) s ∩ F ⁻¹' {0}ᶜ) :=
    hdiffF.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hKU : closedBall (0:ℂ) r ⊆ ball (0:ℂ) s ∩ F ⁻¹' {0}ᶜ := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    refine ⟨?_, hFne z hz⟩
    rw [mem_ball, dist_zero_right]; linarith
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0:ℂ) r).exists_cthickening_subset_open hU hKU
  rw [cthickening_closedBall hδ.le hr0.le] at hδU
  set R' := δ + r with hR'
  have hR'0 : 0 < R' := by linarith
  have hR's : R' < s := by
    have hmem : ((R' : ℝ) : ℂ) ∈ closedBall (0:ℂ) R' := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR'0]
    have := (hδU hmem).1
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR'0] at this
    exact this
  -- `1 / F` is holomorphic on the closed disc of radius `R'`
  set H : ℂ → ℂ := fun z => (F z)⁻¹ with hHdef
  have hdiffH : DifferentiableOn ℂ H (closedBall (0:ℂ) R') := by
    have h1 : DifferentiableOn ℂ F (closedBall (0:ℂ) R') :=
      hdiffF.mono (fun z hz => (hδU hz).1)
    exact h1.inv (fun z hz => (hδU hz).2)
  set RN : NNReal := ⟨R', hR'0.le⟩ with hRN
  have hRN0 : (0 : NNReal) < RN := by rw [← NNReal.coe_pos]; exact hR'0
  have hH : HasFPowerSeriesOnBall H (cauchyPowerSeries H 0 RN) 0 RN :=
    hdiffH.hasFPowerSeriesOnBall hRN0
  set pH := cauchyPowerSeries H 0 RN with hpH
  set q : ℕ → ℂ := fun n => pH.coeff n with hq
  set e : ℕ → ℂ := fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, c kl.1 * q kl.2 with he
  -- Cauchy product: `∑ e_n y^n = F y * H y = 1`
  have hprod : ∀ y : ℂ, ‖y‖ < R' →
      Summable (fun n => ‖e n * y ^ n‖) ∧ HasSum (fun n => e n * y ^ n) 1 := by
    intro y hy
    have hyRN : y ∈ eball (0:ℂ) (RN : ENNReal) := by
      rw [Metric.eball_coe, mem_ball, dist_zero_right]; exact hy
    have hysN : y ∈ eball (0:ℂ) (sN : ENNReal) := by
      rw [Metric.eball_coe, mem_ball, dist_zero_right]; show ‖y‖ < s; linarith
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
  -- uniqueness of power series: `e = (1, 0, 0, ...)`
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
  -- hence the Taylor coefficients of `1 / F` are those of the formal inverse `G`
  set Q : PowerSeries ℂ := PowerSeries.mk q with hQ
  set Cc : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) P with hCc
  set Gc : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) G with hGc
  have hCQ : Cc * Q = 1 := by
    ext n
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, ← he_val n]
    simp only [he]
    refine Finset.sum_congr rfl (fun kl _ => ?_)
    simp [hCc, hQ, hP, hc]
  have hCG : Cc * Gc = 1 := by
    rw [hCc, hGc, ← map_mul, hPG, map_one]
  have hQG : Q = Gc := by
    calc Q = Q * (Cc * Gc) := by rw [hCG, mul_one]
      _ = (Cc * Q) * Gc := by ring
      _ = Gc := by rw [hCQ, one_mul]
  have hqG : ∀ n, pH.coeff n = ((PowerSeries.coeff n G : ℤ) : ℂ) := by
    intro n
    have := congrArg (PowerSeries.coeff n) hQG
    rw [hQ, PowerSeries.coeff_mk, hGc, PowerSeries.coeff_map] at this
    simpa [hq] using this
  -- Cauchy estimates give decay of `G` at radius `t ∈ (r, R')`
  set t : ℝ := (r + R') / 2 with ht
  have htr : r < t := by linarith
  have htR : t < R' := by linarith
  set tN : NNReal := ⟨t, by linarith⟩ with htN
  have htrad : (tN : ENNReal) < pH.radius := by
    refine lt_of_lt_of_le ?_ hH.r_le
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe]; exact htR)
  have hsumH := pH.summable_norm_mul_pow htrad
  refine ⟨t, htr, AGiu_decays_of_nat _ ?_⟩
  refine hsumH.tendsto_atTop_zero.congr (fun n => ?_)
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hqG n,
    LaurentSeries.coeff_coe_powerSeries, Complex.norm_intCast]
  rfl
