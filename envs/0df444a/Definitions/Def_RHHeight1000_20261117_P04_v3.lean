-- Prove2me | Definitions.Def_RHHeight1000_20261117_P04_v3
-- name    : RHHeight1000_20261117_P04_v3
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T12:16:53.551203+00:00
-- url     : https://prove2.me/theorems/24bde58a-9aad-4400-a4d0-697ba973d5c6
-- title:
--   Zeta analytic counting dependencies 04 (ordinary proofs)
-- statement:
--   Complete analytic proof dependencies for zeta counting, without custom metaprogramming declarations. No numeric zero-certification assumptions. Source attribution and Apache-2.0 headers retained.
-- source:
--   smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe; reduced height and Lean 4.33.1 packaging by Desenvolvimento RH. AXLE full source d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Definitions.Def_RHHeight1000_20261117_P03_v3
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort72
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology MeasureTheory Set
theorem Real.sum_range_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by
  have h1mσ : 0 < 1 - σ := by linarith
  have hcmp := (Real.antitoneOn_rpow_neg_Icc (a := 1) (b := 1 + (↑(N - 1) : ℝ)) hσ0.le
    one_pos).sum_le_integral
  have hcast : (1 : ℝ) + (↑(N - 1) : ℝ) = (N : ℝ) := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [hcast] at hcmp
  have hint : ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ) = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -σ)), Real.one_rpow,
      show -σ + 1 = 1 - σ by ring]
  rw [hint] at hcmp
  rw [Finset.sum_range_succ', Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0.ne'), add_zero]
  have inner : ∑ i ∈ Finset.range N, ((↑(i + 1) : ℝ)) ^ (-σ)
      = (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1 := by
    conv_lhs => rw [show N = (N - 1) + 1 by lia]
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      congr 1; push_cast; ring
    · norm_num
  rw [inner]
  calc (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1
      ≤ ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) + 1 := by linarith [hcmp]
    _ ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by gcongr; linarith
private theorem add_mul_I_ne_one {σ t : ℝ} (ht : t ≠ 0) : (σ : ℂ) + (t : ℂ) * I ≠ 1 :=
  fun h ↦ ht (by simpa using congrArg Complex.im h)
private theorem abs_floor_bundle {t : ℝ} (ht : 3 < |t|) :
    0 < |t| ∧ 0 < ⌊|t|⌋₊ ∧ (⌊|t|⌋₊ : ℝ) ≤ |t| :=
  have htpos : (0 : ℝ) < |t| := by linarith
  ⟨htpos, Nat.floor_pos.mpr (by linarith), Nat.floor_le htpos.le⟩
private theorem norm_sum_one_div_cpow_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hs_ne : (σ : ℂ) + (t : ℂ) * I ≠ 0 := fun h ↦ by rw [h] at hre; simp at hre
  have hsum_norm : ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), (n : ℝ) ^ (-σ) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hs_ne, div_zero, norm_zero, Real.zero_rpow (neg_ne_zero.mpr σpos.ne')]
    · rw [norm_div, norm_one, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  refine hsum_norm.trans ((Real.sum_range_rpow_neg_le σpos hσ.2 Npos).trans ?_)
  have hdiv : (⌊|t|⌋₊ : ℝ) ^ (1 - σ) / (1 - σ) ≤ |t| ^ (1 - σ) / (1 - σ) := by gcongr
  have h1L : (1 : ℝ) ≤ |t| ^ (1 - σ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ |t|) h1mσ.le
  linarith
private theorem norm_neg_cpow_one_sub_div_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (1 - ((σ : ℂ) + (t : ℂ) * I)) / (1 - ((σ : ℂ) + (t : ℂ) * I))‖
      ≤ |t| ^ (1 - σ) * 2 := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos,
    show ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).1
private theorem norm_neg_cpow_neg_div_two_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) / 2‖ ≤ |t| ^ (1 - σ) := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos, RCLike.norm_ofNat,
    show (-((σ : ℂ) + (t : ℂ) * I)).re = -σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).2.1
private theorem norm_riemannZeta0_tail_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖((σ : ℂ) + (t : ℂ) * I) * ∫ x in Ioi (⌊|t|⌋₊ : ℝ),
        (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) + 1)‖ ≤ 16 * |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have hσ2 : σ ≤ 2 := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hpow : |t| * |t| ^ (-σ) = |t| ^ (1 - σ) := by
    rw [show (1 - σ : ℝ) = 1 + (-σ) by ring, Real.rpow_add htpos, Real.rpow_one]
  refine (ZetaBnd_aux1 ⌊|t|⌋₊ Npos ⟨σpos, hσ2⟩ (by linarith : (2 : ℝ) ≤ |t|)).trans ?_
  rw [mul_div_assoc]
  refine (mul_le_mul_of_nonneg_left
    (UpperBnd_aux6 ht ⟨hσ.1, hσ2⟩ (add_mul_I_ne_one (abs_pos.mp htpos)) Npos N_le_t).2.2
    (by positivity)).trans (le_of_eq ?_)
  rw [show |t| ^ (1 - σ) = |t| * |t| ^ (-σ) from hpow.symm]; ring
theorem norm_riemannZeta_le_of_mem_strip {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := by
  rw [mul_comm Complex.I (t : ℂ)]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  have σpos : 0 < σ := by linarith [hσ.1]
  obtain ⟨htpos, Npos, -⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hL : (0 : ℝ) < |t| ^ (1 - σ) := Real.rpow_pos_of_pos htpos _
  rw [← Zeta0EqZeta Npos hre (add_mul_I_ne_one (abs_pos.mp htpos))]
  refine le_trans (norm_add₄_le ..) ?_
  refine le_trans (add_le_add (add_le_add (add_le_add (norm_sum_one_div_cpow_le hσ ht)
    (norm_neg_cpow_one_sub_div_le hσ ht)) (norm_neg_cpow_neg_div_two_le hσ ht))
    (norm_riemannZeta0_tail_le hσ ht)) ?_
  have hscalar : 1 / (1 - σ) + 20 ≤ 11 / (1 - σ) := by
    rw [← sub_nonneg, show 11 / (1 - σ) - (1 / (1 - σ) + 20) = (20 * σ - 10) / (1 - σ) by
      field_simp; ring]
    exact div_nonneg (by linarith [hσ.1]) h1mσ.le
  calc |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) + |t| ^ (1 - σ) * 2 + |t| ^ (1 - σ)
        + 16 * |t| ^ (1 - σ)
      = (1 / (1 - σ) + 20) * |t| ^ (1 - σ) := by ring
    _ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := mul_le_mul_of_nonneg_right hscalar hL.le
private theorem intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (1 - σ)) volume (1 / 2) 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (1 / 2 : ℝ)) (b := 0)).comp_sub_left 1
  norm_num at h; exact h
private theorem intervalIntegrable_log_sub_one :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (σ - 1)) volume 1 2 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).comp_sub_right 1
  norm_num at h; exact h
private theorem integral_strip_majorant (L : ℝ) :
    ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * L - Real.log (1 - σ))
      = 1 / 2 * Real.log 11 + L / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have ii_const : IntervalIntegrable (fun _ : ℝ ↦ Real.log 11) volume (1 / 2) 1 :=
    intervalIntegrable_const
  have ii_lin : IntervalIntegrable (fun σ : ℝ ↦ (1 - σ) * L) volume (1 / 2) 1 :=
    Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1
  have ii_log := intervalIntegrable_log_one_sub
  have hlin : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) * L = L / 8 := by
    rw [intervalIntegral.integral_mul_const]
    have hone : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) = 1 / 8 := by
      rw [intervalIntegral.integral_comp_sub_left (fun x ↦ x) 1, integral_id]
      norm_num
    rw [hone]; ring
  have hlog : ∫ σ in (1 / 2 : ℝ)..1, Real.log (1 - σ) = -(1 / 2 * Real.log 2) - 1 / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x ↦ Real.log x) 1, integral_log]
    rw [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      Real.log_div one_ne_zero two_ne_zero, Real.log_one]
    simp
  rw [intervalIntegral.integral_sub (ii_const.add ii_lin) ii_log,
    intervalIntegral.integral_add ii_const ii_lin, intervalIntegral.integral_const, hlin, hlog]
  simp only [smul_eq_mul]
  ring
theorem norm_riemannZeta_le_div_sub_one {σ t : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ σ / (σ - 1) := by
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs
  have hsre : s.re = σ := by simp [hs]
  have htail : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have h := norm_riemannZeta_sub_one_le (s := s) (by rw [hsre]; exact hσ)
    rwa [hsre] at h
  have hsum := Real.tsum_one_div_nat_add_two_rpow_le_inv_sub_one hσ
  have hnorm := norm_le_insert (1 : ℂ) (riemannZeta s)
  rw [norm_one, norm_sub_rev] at hnorm
  refine (by linarith [htail, hsum] : ‖riemannZeta s‖ ≤ 1 + 1 / (σ - 1)).trans (le_of_eq ?_)
  rw [eq_div_iff hσ1.ne']; field_simp; ring
private theorem integral_log_sub_log_sub_one :
    ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) = 2 * Real.log 2 := by
  have iiA : IntervalIntegrable (fun σ : ℝ ↦ Real.log σ) volume 1 2 :=
    intervalIntegral.intervalIntegrable_log'
  rw [intervalIntegral.integral_sub iiA intervalIntegrable_log_sub_one]
  have hA : ∫ σ in (1 : ℝ)..2, Real.log σ = 2 * Real.log 2 - 1 := by
    rw [integral_log, Real.log_one]; ring
  have hB : ∫ σ in (1 : ℝ)..2, Real.log (σ - 1) = -1 := by
    rw [intervalIntegral.integral_comp_sub_right (fun x ↦ Real.log x) 1]
    norm_num [integral_log, Real.log_one]
  rw [hA, hB]; ring
private theorem integrableOn_log_norm_riemannZeta_subset {t : ℝ} {S : Set ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hS : S ⊆ Ioi (1 / 2 : ℝ)) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
  (integrableOn_log_norm_riemannZeta_Ioi ht hzero).mono_set hS
private theorem logNormZetaIntegral_eq_add {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t
      = (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + ∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  have ig : ∀ {S : Set ℝ}, S ⊆ Ioi (1 / 2 : ℝ) →
      IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
    fun hS ↦ integrableOn_log_norm_riemannZeta_subset ht hzero hS
  have ig_a := ig (S := Ioc (1 / 2 : ℝ) 1) Ioc_subset_Ioi_self
  have ig_Ioi1 := ig (S := Ioi (1 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_Ioi2 := ig (S := Ioi (2 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_b := ig (S := Ioc (1 : ℝ) 2) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_c := ig (S := Ioc (2 : ℝ) 4) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_d := ig (S := Ioi (4 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  rw [logNormZetaIntegral, ← Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_a ig_Ioi1,
    ← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ 2 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_b ig_Ioi2,
    ← Ioc_union_Ioi_eq_Ioi (show (2 : ℝ) ≤ 4 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_c ig_d]
  ring
private theorem integral_log_norm_riemannZeta_Ioc_half_one_le {t : ℝ} (ht : 3 < t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have htpos : 0 < t := by linarith
  have ht3 : 3 < |t| := by rwa [abs_of_pos htpos]
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_a := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 / 2 : ℝ) 1) htpos.ne' hzero
    Ioc_subset_Ioi_self
  have hmaj : IntegrableOn
      (fun σ : ℝ ↦ Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ))
      (Ioc (1 / 2 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_const).add
      (Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1)).sub intervalIntegrable_log_one_sub
  calc (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (1 / 2 : ℝ) 1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) := by
        refine setIntegral_mono_on_ae ig_a hmaj measurableSet_Ioc ?_
        have hne1 : ∀ᵐ σ : ℝ, σ ≠ 1 := by rw [ae_iff]; simp
        filter_upwards [hne1] with σ hσ1 hσmem
        have hσIoo : σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hσmem.1, lt_of_le_of_ne hσmem.2 hσ1⟩
        have h1mσ : 0 < 1 - σ := by linarith [hσIoo.2]
        have hstrip := norm_riemannZeta_le_of_mem_strip hσIoo ht3
        rw [abs_of_pos htpos] at hstrip
        have hzpos := hpos σ (le_of_lt hσmem.1)
        have hlogexp : Real.log (11 / (1 - σ) * t ^ (1 - σ))
            = Real.log 11 - Real.log (1 - σ) + (1 - σ) * Real.log t := by
          rw [Real.log_mul (ne_of_gt (div_pos (by norm_num) h1mσ))
              (ne_of_gt (Real.rpow_pos_of_pos htpos _)),
            Real.log_div (by norm_num) (ne_of_gt h1mσ), Real.log_rpow htpos]
        calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
            ≤ Real.log (11 / (1 - σ) * t ^ (1 - σ)) := Real.log_le_log hzpos hstrip
          _ = Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ) := by rw [hlogexp]; ring
    _ = ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) :=
        (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) :=
        integral_strip_majorant _
private theorem integral_log_norm_riemannZeta_Ioc_two_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log (Real.pi ^ 2 / 6) := by
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_c := integrableOn_log_norm_riemannZeta_subset (S := Ioc (2 : ℝ) 4) ht hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_m3 : IntegrableOn (fun _ : ℝ ↦ Real.log (Real.pi ^ 2 / 6)) (Ioc (2 : ℝ) 4) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    exact intervalIntegrable_const
  calc (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (2 : ℝ) 4, Real.log (Real.pi ^ 2 / 6) := by
        refine setIntegral_mono_on ig_c ig_m3 measurableSet_Ioc ?_
        intro σ hσmem
        have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
        have hb := norm_riemannZeta_sub_one_le_of_two_le_re
          (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; linarith [hσmem.1])
        have hzle : ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ Real.pi ^ 2 / 6 := by
          have h := norm_sub_norm_le (riemannZeta ((σ : ℂ) + Complex.I * t)) 1
          rw [norm_one] at h
          linarith
        have hzpos := hpos σ (by linarith [hσmem.1])
        exact Real.log_le_log hzpos hzle
    _ = 2 * Real.log (Real.pi ^ 2 / 6) := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4),
          intervalIntegral.integral_const]; norm_num
private theorem integral_log_norm_riemannZeta_Ioi_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ig_d := integrableOn_log_norm_riemannZeta_subset (S := Ioi (4 : ℝ)) ht hzero
    (Ioi_subset_Ioi (by norm_num))
  have ig_maj : IntegrableOn
      (fun σ : ℝ ↦ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))) (Ioi (4 : ℝ)) :=
    (Real.integrableOn_exp_neg_mul_Ioi hl2 4).const_mul _
  refine setIntegral_mono_on ig_d ig_maj measurableSet_Ioi ?_
  intro σ hσmem
  calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
      ≤ |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖| := le_abs_self _
    _ ≤ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) :=
        abs_log_norm_riemannZeta_le_exp (le_of_lt hσmem)
theorem logNormZetaIntegral_le_of_middle {M₂ β₂ : ℝ} {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ M₂ + β₂ * Real.log t) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + M₂
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + (1 / 8 + β₂) * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ht3 : 3 < t := by nlinarith [Real.pi_gt_three]
  rw [logNormZetaIntegral_eq_add htpos.ne' hzero]
  linarith [integral_log_norm_riemannZeta_Ioc_half_one_le ht3 hzero, hmid,
    integral_log_norm_riemannZeta_Ioc_two_four_le htpos.ne' hzero,
    integral_log_norm_riemannZeta_Ioi_four_le htpos.ne' hzero]
theorem logNormZetaIntegral_le_elem {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + 2 * Real.log 2
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + 1 / 8 * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ig_b := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 : ℝ) 2) htpos.ne' hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log 2 + 0 * Real.log t := by
    have hmaj : IntegrableOn (fun σ : ℝ ↦ Real.log σ - Real.log (σ - 1)) (Ioc (1 : ℝ) 2) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_log_sub_one
    calc (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ ∫ σ in Ioc (1 : ℝ) 2, (Real.log σ - Real.log (σ - 1)) := by
          refine setIntegral_mono_on ig_b hmaj measurableSet_Ioc (fun σ hσmem ↦ ?_)
          have hσ1 : 1 < σ := hσmem.1
          have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
          have hzpos : 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
            norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact hσ1.le))
          have hζle := norm_riemannZeta_le_div_sub_one (t := t) hσ1
          calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
              ≤ Real.log (σ / (σ - 1)) := Real.log_le_log hzpos hζle
            _ = Real.log σ - Real.log (σ - 1) := Real.log_div (by linarith) (by linarith)
      _ = ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) :=
          (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = 2 * Real.log 2 := integral_log_sub_log_sub_one
      _ = 2 * Real.log 2 + 0 * Real.log t := by ring
  linarith [logNormZetaIntegral_le_of_middle ht hzero hmid]
private theorem integral_exp_tail_eq :
    (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have key : (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = 8 * (Real.pi ^ 2 / 6 - 1) * ∫ σ in Ioi (4 : ℝ), Real.exp ((-Real.log 2) * σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun σ _ ↦ ?_)
    simp only [neg_mul]
  rw [key, integral_exp_mul_Ioi (by linarith : -Real.log 2 < 0) 4]
  have hexp : Real.exp ((-Real.log 2) * 4) = 1 / 16 := by
    rw [show (-Real.log 2) * 4 = -(4 * Real.log 2) by ring, Real.exp_neg,
      show (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    norm_num
  rw [hexp]; field_simp; ring
private theorem pi_sq_lt_d4 : Real.pi ^ 2 < 9.8697 := by
  nlinarith [Real.pi_lt_d6, Real.pi_pos]
private theorem log_eleven_le : Real.log 11 ≤ 3 * Real.log 2 + 3 / 8 := by
  have he : Real.log 11 = Real.log (2 ^ 3) + Real.log (11 / 8) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; norm_num
  rw [he, Real.log_pow]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 8 by norm_num)
  push_cast; linarith
private theorem log_pi_sq_div_six_lt : Real.log (Real.pi ^ 2 / 6) < 1 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hsq : (Real.pi ^ 2 / 6) ^ 2 < Real.exp (1 / 2) ^ 2 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [pow_two, ← Real.exp_add]; norm_num
    rw [h1]; nlinarith [pi_sq_lt_d4, Real.exp_one_gt_d9]
  exact lt_of_pow_lt_pow_left₀ 2 (Real.exp_pos _).le hsq
private theorem exp_tail_lt_half : (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) < 1 / 2 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_sq_lt_d4, Real.log_two_gt_d9]
theorem logNormZetaIntegral_le_five {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤ 5 + 1 / 8 * Real.log t := by
  refine (logNormZetaIntegral_le_elem ht hzero).trans ?_
  rw [integral_exp_tail_eq]
  linarith [log_eleven_le, log_pi_sq_div_six_lt, exp_tail_lt_half, Real.log_two_lt_d9]
end
end CertificatePort72
section CertificatePort73
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Set MeasureTheory
open scoped Real
noncomputable def logNormGammaArchimedean (t σ : ℝ) : ℝ :=
  Real.log ‖(1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) * (((σ : ℂ) + Complex.I * t) - 1)) *
    Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖
private lemma norm_ofReal_add_I_mul (a t : ℝ) :
    ‖(a : ℂ) + Complex.I * t‖ = Real.sqrt (a ^ 2 + t ^ 2) := by
  rw [mul_comm, Complex.norm_add_mul_I]
lemma archLine_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    (σ : ℂ) + Complex.I * t ≠ 0 := by
  intro h
  exact ht (by simpa using congrArg Complex.im h)
lemma archLine_sub_one_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    (σ : ℂ) + Complex.I * t - 1 ≠ 0 := by
  intro h
  exact ht (by simpa using congrArg Complex.im h)
private lemma Gammaℝ_archLine_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_im_ne_zero (by simpa using ht)
private lemma archLine_div_two (σ t : ℝ) :
    ((σ : ℂ) + Complex.I * t) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring
private lemma archLine_div_two_ne_neg_natCast {t : ℝ} (ht : t ≠ 0) (σ : ℝ) (m : ℕ) :
    ((σ : ℂ) + Complex.I * t) / 2 ≠ -m := by
  intro hm
  rw [archLine_div_two] at hm
  apply ht
  have him := congrArg Complex.im hm
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_re, Complex.neg_im, Complex.natCast_im, mul_one, mul_zero, zero_add,
    add_zero] at him
  linarith
private lemma norm_Gammaℝ_archLine (σ t : ℝ) :
    ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ =
      Real.pi ^ (-σ / 2) * ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp [neg_div]
private lemma log_norm_Gammaℝ_archLine {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ =
      -(σ / 2) * Real.log Real.pi + Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  have hpole := archLine_div_two_ne_neg_natCast ht σ
  rw [norm_Gammaℝ_archLine,
    Real.log_mul (by positivity) (norm_ne_zero_iff.2 (Complex.Gamma_ne_zero hpole)),
    Real.log_rpow Real.pi_pos]
  ring
private lemma logNormGammaArchimedean_eq {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    logNormGammaArchimedean t σ =
      Real.log (1 / 2) + Real.log ‖(σ : ℂ) + Complex.I * t‖ +
        Real.log ‖(σ : ℂ) + Complex.I * t - 1‖ +
        Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ := by
  unfold logNormGammaArchimedean
  set z : ℂ := (σ : ℂ) + Complex.I * t with hz
  have hz_ne : ‖z‖ ≠ 0 := by rw [hz]; exact norm_ne_zero_iff.2 (archLine_ne_zero ht σ)
  have hz1_ne : ‖z - 1‖ ≠ 0 := by rw [hz]; exact norm_ne_zero_iff.2 (archLine_sub_one_ne_zero ht σ)
  have hG_ne : ‖Complex.Gammaℝ z‖ ≠ 0 := by
    rw [hz]; exact norm_ne_zero_iff.2 (Gammaℝ_archLine_ne_zero ht σ)
  have e : (1 / 2 : ℂ) * (z * (z - 1)) * Complex.Gammaℝ z =
      (1 / 2 : ℂ) * z * (z - 1) * Complex.Gammaℝ z := by ring
  rw [e, norm_mul, norm_mul, norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_ofNat]
  rw [h12, Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num) hz_ne) hz1_ne) hG_ne,
    Real.log_mul (mul_ne_zero (by norm_num) hz_ne) hz1_ne,
    Real.log_mul (by norm_num) hz_ne]
private lemma continuous_archFactor {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ (1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) *
      (((σ : ℂ) + Complex.I * t) - 1)) * Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)) := by
  have hline : Continuous (fun σ : ℝ ↦ (σ : ℂ) + Complex.I * t) := by fun_prop
  have hdiv : Continuous (fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) / 2) := hline.div_const 2
  have hndiv : Continuous (fun σ : ℝ ↦ -((σ : ℂ) + Complex.I * t) / 2) := hline.neg.div_const 2
  have hG : Continuous (fun σ : ℝ ↦ Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)) := by
    rw [continuous_iff_continuousAt]
    intro σ
    have hcpow : ContinuousAt
        (fun σ : ℝ ↦ (Real.pi : ℂ) ^ (-((σ : ℂ) + Complex.I * t) / 2)) σ :=
      (continuousAt_const_cpow (by exact_mod_cast Real.pi_ne_zero)).comp hndiv.continuousAt
    have hGamma : ContinuousAt
        (fun σ : ℝ ↦ Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)) σ :=
      ContinuousAt.comp (g := Complex.Gamma)
        (f := fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) / 2)
        (Complex.differentiableAt_Gamma _ (archLine_div_two_ne_neg_natCast ht σ)).continuousAt
        hdiv.continuousAt
    simp only [Complex.Gammaℝ_def]
    exact hcpow.mul hGamma
  exact (continuous_const.mul (hline.mul (hline.sub continuous_const))).mul hG
lemma continuous_logNormGammaArchimedean {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ logNormGammaArchimedean t σ) := by
  rw [continuous_iff_continuousAt]
  intro σ
  have hne : (1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) * (((σ : ℂ) + Complex.I * t) - 1)) *
      Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
    prefactor_ne_zero_of (archLine_ne_zero ht σ)
      (sub_ne_zero.mp (archLine_sub_one_ne_zero ht σ)) (Gammaℝ_archLine_ne_zero ht σ)
  exact (Real.continuousAt_log (by simpa using hne)).comp
    ((continuous_norm.comp (continuous_archFactor ht)).continuousAt)
lemma intervalIntegrable_logNormGammaArchimedean {t : ℝ} (ht : t ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t σ) volume a b :=
  (continuous_logNormGammaArchimedean ht).intervalIntegrable a b
lemma intervalIntegral.Ioo_eq_comp_add_right (f : ℝ → ℝ) {a b s : ℝ} (hab : a ≤ b) :
    (∫ σ in Set.Ioo (a + s) (b + s), f σ) = ∫ x in a..b, f (x + s) := by
  rw [intervalIntegral.integral_comp_add_right f s,
    intervalIntegral.integral_of_le (by linarith : a + s ≤ b + s),
    integral_Ioc_eq_integral_Ioo]
private lemma hasDerivAt_log_norm_Gamma_archLine_half {t : ℝ} (_ht : t ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun u : ℝ ↦ Real.log ‖Complex.Gamma (((u : ℂ) + Complex.I * t) / 2)‖)
      (1 / 2 * (Complex.digamma (((σ : ℂ) + Complex.I * t) / 2)).re) σ := by
  have hpath : HasDerivAt (fun u : ℝ ↦ ((u : ℂ) + Complex.I * t) / 2) (1 / 2 : ℂ) σ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := σ)).add_const (Complex.I * t)).div_const 2
  have hzpos : 0 < (((σ : ℂ) + Complex.I * t) / 2).re := by
    rw [Complex.div_ofNat_re, show ((σ : ℂ) + Complex.I * t).re = σ by simp]; linarith
  simpa [Complex.mul_re] using Complex.hasDerivAt_log_norm_Gamma_comp hpath hzpos
private lemma half_re_digamma_archLine_ge {t : ℝ} (ht : 168 * Real.pi ≤ t)
    {u : ℝ} (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 9 / 2) :
    1 / 2 * Real.log (t / 2) - 1 / 10000 ≤
      1 / 2 * (Complex.digamma (((u : ℂ) + Complex.I * t) / 2)).re := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht504 : (504 : ℝ) ≤ t := by nlinarith
  have ht0 : 0 < t := by linarith
  set z : ℂ := ((u : ℂ) + Complex.I * t) / 2 with hz
  have hzre : z.re = u / 2 := by rw [hz, Complex.div_ofNat_re]; simp
  have h2z : 2 * z = (u : ℂ) + Complex.I * t := by rw [hz]; ring
  have hnorm_ge : t / 2 ≤ ‖z‖ := by
    have h : t ≤ Real.sqrt (u ^ 2 + t ^ 2) := by
      have := Real.sqrt_le_sqrt (show t ^ 2 ≤ u ^ 2 + t ^ 2 by nlinarith [sq_nonneg u])
      rwa [Real.sqrt_sq ht0.le] at this
    rw [hz, norm_div, Complex.norm_ofNat, le_div_iff₀ (by norm_num),
      mul_comm (Complex.I) (t : ℂ), Complex.norm_add_mul_I]
    linarith
  have hznpos : 0 < ‖z‖ := by linarith
  have hlogz : Real.log (t / 2) ≤ (Complex.log z).re := by
    rw [Complex.log_re]; exact Real.log_le_log (by linarith) hnorm_ge
  have hpole_le : ((2 * z)⁻¹).re ≤ u / t ^ 2 := by
    rw [h2z, show ((u : ℂ) + Complex.I * t) = ((u : ℂ) + (t : ℂ) * Complex.I) by ring,
      Complex.inv_re, Complex.normSq_add_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    gcongr
    nlinarith [sq_nonneg u]
  set E : ℂ := Complex.digamma z - Complex.log z + (2 * z)⁻¹ with hE
  have hEbound := Complex.Stirling.norm_digamma_sub_log_le' (a := 1 / 4) (by norm_num) z
    (by rw [hzre]; linarith)
  rw [← hE, show ‖z‖ ^ (-(2 : ℤ)) = (‖z‖ ^ 2)⁻¹ by rw [zpow_neg]; norm_cast] at hEbound
  have hC₀ : 3 / (2 * π ^ 2 * (1 / 4)) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hzn2_le : (‖z‖ ^ 2)⁻¹ ≤ 4 / t ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hEre : -(3 / t ^ 2) ≤ E.re := by
    have h3 : (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * (‖z‖ ^ 2)⁻¹ ≤ 3 / t ^ 2 := by
      calc (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * (‖z‖ ^ 2)⁻¹
          ≤ 3 / 4 * (4 / t ^ 2) := mul_le_mul (by linarith) hzn2_le (by positivity) (by norm_num)
        _ = 3 / t ^ 2 := by ring
    linarith [neg_abs_le E.re, Complex.abs_re_le_norm E, hEbound, h3]
  have hψre : (Complex.digamma z).re = (Complex.log z).re - ((2 * z)⁻¹).re + E.re := by
    rw [hE]; simp only [Complex.add_re, Complex.sub_re]; ring
  have htail : u / t ^ 2 + 3 / t ^ 2 ≤ 2 * (1 / 10000) := by
    rw [show u / t ^ 2 + 3 / t ^ 2 = (u + 3) / t ^ 2 by ring, div_le_iff₀ (by positivity)]
    nlinarith [ht504, hu2]
  linarith [hlogz, hpole_le, hEre, hψre, htail]
private lemma logNormGamma_half_diff_ge {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2) {t : ℝ}
    (ht : 168 * Real.pi ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    (d / 2) * Real.log (t / 2) - d / 10000 ≤
      Real.log ‖Complex.Gamma ((((σ + d : ℝ) : ℂ) + Complex.I * t) / 2)‖ -
        Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htne : t ≠ 0 := by nlinarith
  have hσd : σ ≤ σ + d := by linarith
  have hderiv : ∀ u ∈ Set.Icc σ (σ + d),
      HasDerivAt (fun v : ℝ ↦ Real.log ‖Complex.Gamma (((v : ℂ) + Complex.I * t) / 2)‖)
        (1 / 2 * (Complex.digamma (((u : ℂ) + Complex.I * t) / 2)).re) u :=
    fun u hu ↦ hasDerivAt_log_norm_Gamma_archLine_half htne (by linarith [hu.1])
  have hmvt := (convex_Icc σ (σ + d)).mul_sub_le_image_sub_of_le_deriv
    (f := fun v : ℝ ↦ Real.log ‖Complex.Gamma (((v : ℂ) + Complex.I * t) / 2)‖)
    (C := 1 / 2 * Real.log (t / 2) - 1 / 10000)
    (fun u hu ↦ (hderiv u hu).continuousAt.continuousWithinAt)
    (fun u hu ↦ (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ by
      rw [interior_Icc, Set.mem_Ioo] at hu
      rw [(hderiv u ⟨hu.1.le, hu.2.le⟩).deriv]
      exact half_re_digamma_archLine_ge ht (by linarith [hu.1]) (by linarith [hu.2]))
    σ (Set.left_mem_Icc.2 hσd) (σ + d) (Set.right_mem_Icc.2 hσd) hσd
  beta_reduce at hmvt
  push_cast at hmvt ⊢
  nlinarith [hmvt]
lemma logNormGammaArchimedean_line_log_norm_diff_ge {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2)
    {t : ℝ} (ht : 2 ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    Real.log ‖(σ : ℂ) + Complex.I * t‖ ≤ Real.log ‖((σ : ℂ) + (d : ℂ)) + Complex.I * t‖ ∧
    -(1 / 2 * Real.log 2) ≤
      Real.log ‖((σ : ℂ) + (d : ℂ)) + Complex.I * t - 1‖ -
        Real.log ‖(σ : ℂ) + Complex.I * t - 1‖ := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2pos : (0 : ℝ) < t ^ 2 := pow_pos ht0 2
  refine ⟨?_, ?_⟩
  ·
    rw [show ((σ : ℂ) + (d : ℂ)) + Complex.I * t = ((σ + d : ℝ) : ℂ) + Complex.I * t by
        push_cast; ring, norm_ofReal_add_I_mul, norm_ofReal_add_I_mul]
    apply Real.log_le_log (Real.sqrt_pos.2 (by nlinarith [sq_nonneg σ]))
    apply Real.sqrt_le_sqrt
    nlinarith
  ·
    rw [show ((σ : ℂ) + (d : ℂ)) + Complex.I * t - 1 = ((σ + d - 1 : ℝ) : ℂ) + Complex.I * t by
        push_cast; ring,
      show (σ : ℂ) + Complex.I * t - 1 = ((σ - 1 : ℝ) : ℂ) + Complex.I * t by push_cast; ring,
      norm_ofReal_add_I_mul, norm_ofReal_add_I_mul, Real.log_sqrt (by positivity),
      Real.log_sqrt (by positivity)]
    have hlow : Real.log (t ^ 2) ≤ Real.log ((σ + d - 1) ^ 2 + t ^ 2) :=
      Real.log_le_log ht2pos (by nlinarith [sq_nonneg (σ + d - 1)])
    have hhigh : Real.log ((σ - 1) ^ 2 + t ^ 2) ≤ Real.log (2 * t ^ 2) := by
      apply Real.log_le_log (by nlinarith [sq_nonneg (σ - 1)])
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - (σ - 1))
          (by linarith : (0 : ℝ) ≤ 2 + (σ - 1)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ t - 2) (by linarith : (0 : ℝ) ≤ t + 2)]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hhigh
    rw [Real.log_pow] at hlow
    push_cast at hlow hhigh
    nlinarith [hlow, hhigh]
lemma logNormGammaArchimedean_diff_ge_tight {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2)
    {t : ℝ} (ht : 168 * Real.pi ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    (d / 2) * Real.log (t / 2) - (d / 2) * Real.log Real.pi - 1 / 2 * Real.log 2 - d / 10000 ≤
      logNormGammaArchimedean t (σ + d) - logNormGammaArchimedean t σ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht2 : (2 : ℝ) ≤ t := by nlinarith
  have htne : t ≠ 0 := by nlinarith
  rw [logNormGammaArchimedean_eq htne (σ + d), logNormGammaArchimedean_eq htne σ,
    log_norm_Gammaℝ_archLine htne (σ + d), log_norm_Gammaℝ_archLine htne σ]
  push_cast
  obtain ⟨hE1, hE2⟩ := logNormGammaArchimedean_line_log_norm_diff_ge hd hd' ht2 hσ1 hσ2
  have hGamma := logNormGamma_half_diff_ge hd hd' ht hσ1 hσ2
  push_cast at hGamma
  nlinarith [hE1, hE2, hGamma]
private lemma logNormGammaArchimedean_strip_diff_ge_of_pointwise {d G : ℝ} (hd : 1 / 2 < d)
    {t : ℝ} (htne : t ≠ 0)
    (hpt : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + d →
      G ≤ logNormGammaArchimedean t (σ + d) - logNormGammaArchimedean t σ) :
    d * G ≤
      (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
        ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  have hab : (1 / 2 : ℝ) ≤ 1 / 2 + d := by linarith
  have hshift : (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), logNormGammaArchimedean t (σ + d) := by
    rw [show (1 / 2 + 2 * d : ℝ) = (1 / 2 + d) + d by ring]
    exact intervalIntegral.Ioo_eq_comp_add_right
      (fun σ ↦ logNormGammaArchimedean t σ) (a := 1 / 2) (b := 1 / 2 + d) (s := d) hab
  have h1 : (∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), logNormGammaArchimedean t σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), logNormGammaArchimedean t σ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Ioc_eq_integral_Ioo]
  rw [hshift, h1]
  have hint1 : IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t (σ + d)) volume
      (1 / 2) (1 / 2 + d) :=
    ((continuous_logNormGammaArchimedean htne).comp (by fun_prop)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t σ) volume
      (1 / 2) (1 / 2 + d) := intervalIntegrable_logNormGammaArchimedean htne _ _
  rw [← intervalIntegral.integral_sub hint1 hint2]
  have hmono : (∫ _σ in (1 / 2 : ℝ)..(1 / 2 + d), G) ≤
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), (logNormGammaArchimedean t (σ + d) -
        logNormGammaArchimedean t σ) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint1.sub hint2)
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    exact hpt σ hσ.1 hσ.2
  rwa [intervalIntegral.integral_const, smul_eq_mul,
    show (1 / 2 + d - 1 / 2 : ℝ) = d by ring] at hmono
theorem logNormGammaArchimedean_strip_diff_ge_tight {d : ℝ} (hd : 1 / 2 < d) (hd' : d ≤ 2) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t -
          ((d ^ 2 / 2) * (Real.log 2 + Real.log Real.pi) + (d / 2) * Real.log 2 + d ^ 2 / 10000) ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  intro t ht
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht504 : (504 : ℝ) ≤ t := by nlinarith
  have htne : t ≠ 0 := by linarith
  have key := logNormGammaArchimedean_strip_diff_ge_of_pointwise hd htne
    (fun σ hσ1 hσ2 ↦ logNormGammaArchimedean_diff_ge_tight (by linarith) hd' ht hσ1 hσ2)
  have hlogt : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div htne (by norm_num)]
  rw [hlogt] at key
  nlinarith [key]
end
end CertificatePort73
section CertificatePort74
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology MeasureTheory Set
open scoped Real
private lemma riemannXiZeros_im_ne_of_forall_riemannZeta_ne {t : ℝ}
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (i : RiemannXiZerosIndex) : (riemannXiZeros i).im ≠ t := by
  intro hi
  have key : ∀ ρ : ℂ, riemannXi ρ = 0 → ρ.im = t → (1 / 2 : ℝ) ≤ ρ.re → False :=
    fun ρ hξ hρ hge ↦ hzero ρ.re hge (by
      rw [show ((ρ.re : ℝ) : ℂ) + Complex.I * t = ρ from Complex.ext (by simp) (by simp [hρ])]
      exact riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)
  set ρ := riemannXiZeros i
  have hξ : riemannXi ρ = 0 := riemannXi_riemannXiZeros_eq_zero i
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hge | hlt
  · exact key ρ hξ hi hge
  ·
    refine key (1 - starRingEnd ℂ ρ) (by rw [riemannXi_one_sub, riemannXi_conj, hξ, map_zero])
      (by simp [hi]) ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
private lemma log_norm_riemannXi_eq {t σ : ℝ} (htne : t ≠ 0) (hσ : 0 < σ)
    (hζ : riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    Real.log ‖riemannXi ((σ : ℂ) + Complex.I * t)‖
      = logNormGammaArchimedean t σ + Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  have hz0 : (σ : ℂ) + Complex.I * t ≠ 0 := archLine_ne_zero htne σ
  have hz1 : (σ : ℂ) + Complex.I * t ≠ 1 := sub_ne_zero.mp (archLine_sub_one_ne_zero htne σ)
  have hΓ : Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hσ)
  rw [riemannXi_eq_prefactor_mul hz0 hz1 hΓ, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (prefactor_ne_zero_of hz0 hz1 hΓ))
      (norm_ne_zero_iff.mpr hζ)]
  rfl
private lemma continuousOn_log_norm_riemannZeta_Ici {t : ℝ} (htne : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    ContinuousOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      (Set.Ici (1 / 2)) := by
  refine continuousOn_log_norm_riemannZeta (fun σ _ h ↦ ?_) hzero
  have him : ((σ : ℂ) + Complex.I * t).im = t := by simp
  rw [h] at him; simp only [Complex.one_im] at him; exact htne him.symm
private lemma intervalIntegral_zero_shift_eq_Ioo (f : ℝ → ℝ) {s d b : ℝ} (hd : 0 ≤ d)
    (hb : s + d = b) : (∫ x in (0 : ℝ)..d, f (x + s)) = ∫ σ in Set.Ioo s b, f σ := by
  have h := intervalIntegral.Ioo_eq_comp_add_right f (a := 0) (b := d) (s := s) hd
  rw [zero_add, show d + s = b from by rw [← hb]; ring] at h
  exact h.symm
theorem le_logNormZetaIntegral_of_le {d κ Ca Cψ Ct : ℝ} (hd : 1 / 2 < d)
    (hκ : ∀ s : ℂ, (∀ i, s ≠ riemannXiZeros i) → (∀ i, s + d ≠ riemannXiZeros i) →
        ∑' i, (Real.log ‖s + ↑d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
          = Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖ - ↑d * κ)
    (hCa : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t - Ca ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ)
    (hCψ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      ∑' i, (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + Cψ)
    (hCt : ∀ t : ℝ,
      (-Ct ≤ ∫ σ in Set.Ioi (1 / 2 + d), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) ∧
      (-Ct ≤ ∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d),
              Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖))
    {c : ℝ} (hc : 2 ≤ c) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤
        (c * d ^ 2 * Cψ + d ^ 2 * κ + 2 * Ct + Ca) + (c - 1) / 2 * d ^ 2 * Real.log t := by
  intro t ht hzero
  have hd0 : (0 : ℝ) < d := by linarith
  have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) ht)
  have ht_im : ∀ i, (riemannXiZeros i).im ≠ t :=
    riemannXiZeros_im_ne_of_forall_riemannZeta_ne hzero
  have hZc := continuousOn_log_norm_riemannZeta_Ici htne hzero
  have hg := integrableOn_log_norm_riemannZeta_Ioi htne hzero
  have hCa' := hCa t ht
  have hCt1 := (hCt t).1
  have hCt2 := (hCt t).2
  set Z : ℝ → ℝ := fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ with hZdef
  set A : ℝ → ℝ := fun σ : ℝ ↦ logNormGammaArchimedean t σ with hAdef
  have hsplit : Set.EqOn (fun x ↦ ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x)
      (fun x ↦ A (x + (1 / 2 + d)) + Z (x + (1 / 2 + d)) - (A (x + 1 / 2) + Z (x + 1 / 2))
        - d * κ) (Set.uIcc 0 d) := by
    intro x hx
    rw [Set.uIcc_of_le hd0.le, Set.mem_Icc] at hx
    have hne : ∀ y : ℂ, y.im = t → ∀ i, y ≠ riemannXiZeros i := fun y hy i h ↦ ht_im i (h ▸ hy)
    have key : ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x
        = Real.log ‖riemannXi ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ))‖
          - Real.log ‖riemannXi ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I)‖ - d * κ := by
      rw [← hκ _ (hne _ (by simp)) (hne _ (by simp))]
      exact tsum_congr fun i ↦ by rw [shiftLogIntegrand]
    simp only [hZdef, hAdef]
    rw [key,
      show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)
          = (((x + (1 / 2 + d) : ℝ) : ℂ) + Complex.I * t) from by push_cast; ring,
      show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I = (((x + 1 / 2 : ℝ) : ℂ) + Complex.I * t) from by
        push_cast; ring,
      log_norm_riemannXi_eq htne (by linarith [hx.1] : (0 : ℝ) < x + (1 / 2 + d))
        (hzero _ (by linarith [hx.1])),
      log_norm_riemannXi_eq htne (by linarith [hx.1] : (0 : ℝ) < x + 1 / 2)
        (hzero _ (by linarith [hx.1]))]
  have iA : ∀ s : ℝ, IntervalIntegrable (fun x ↦ A (x + s)) volume 0 d := fun s ↦
    ((continuous_logNormGammaArchimedean htne).comp (by fun_prop)).intervalIntegrable 0 d
  have iZ : ∀ s : ℝ, 1 / 2 ≤ s → IntervalIntegrable (fun x ↦ Z (x + s)) volume 0 d := fun s hs ↦ by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hd0.le]
    exact hZc.comp (by fun_prop) fun x hx ↦ by
      simp only [Set.mem_Icc] at hx; simp only [Set.mem_Ici]; linarith [hx.1]
  have eA1 := intervalIntegral_zero_shift_eq_Ioo A (s := 1 / 2) hd0.le rfl
  have eA2 := intervalIntegral_zero_shift_eq_Ioo A (s := 1 / 2 + d) (b := 1 / 2 + 2 * d) hd0.le
    (by ring)
  have eZ1 := intervalIntegral_zero_shift_eq_Ioo Z (s := 1 / 2) hd0.le rfl
  have eZ2 := intervalIntegral_zero_shift_eq_Ioo Z (s := 1 / 2 + d) (b := 1 / 2 + 2 * d) hd0.le
    (by ring)
  have hIeq : (∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x)
      = ((∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), A σ)
            - ∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), A σ)
        + ((∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), Z σ)
            - ∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), Z σ) - d ^ 2 * κ := by
    have j1 := (iA (1 / 2)).add (iZ (1 / 2) le_rfl)
    have j2 := (iA (1 / 2 + d)).add (iZ (1 / 2 + d) (by linarith))
    rw [intervalIntegral.integral_congr hsplit,
      intervalIntegral.integral_sub (j2.sub j1) intervalIntegrable_const,
      intervalIntegral.integral_sub j2 j1,
      intervalIntegral.integral_add (iA (1 / 2 + d)) (iZ (1 / 2 + d) (by linarith)),
      intervalIntegral.integral_add (iA (1 / 2)) (iZ (1 / 2) le_rfl),
      intervalIntegral.integral_const, eA2, eZ2, eA1, eZ1]
    simp only [smul_eq_mul, sub_zero]
    ring
  have hSb : ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ c / 2 * d ^ 2 * Real.log t + c * d ^ 2 * Cψ := by
    have h := (integral_tsum_log_norm_shift_le_of hd ht_im hc).trans
      (mul_le_mul_of_nonneg_left (hCψ t ht) (mul_nonneg (by linarith : (0 : ℝ) ≤ c) (sq_nonneg d)))
    linarith [h]
  rw [tsum_shiftLogIntegral_eq_intervalIntegral_tsum hd ht_im, hIeq] at hSb
  have hIt : logNormZetaIntegral t
      = (∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), Z σ) + ∫ σ in Set.Ioi (1 / 2 + d), Z σ := by
    simp only [hZdef, logNormZetaIntegral]
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 1 / 2 + d by linarith),
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi (by linarith))),
      integral_Ioc_eq_integral_Ioo]
  rw [hIt]
  nlinarith [hSb, hCa', hCt1, hCt2]
end
end CertificatePort74
section CertificatePort75
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology MeasureTheory Set
open scoped Real
theorem norm_integral_argZeta_le_of_bounds' {a₁ a₂ b₁ b₂ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb : b₁ + b₂ ≤ 0.128 * Real.pi)
    (ha₁ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      logNormZetaIntegral t ≤ a₁ + b₁ * Real.log t)
    (ha₂ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + b₂ * Real.log t) :
    ∀ t₁ t₂ : ℝ, 168 * Real.pi < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t|
        ≤ ((a₁ + a₂) + (b₁ + b₂) * Real.log (2 * Real.pi)) / Real.pi
          + 0.128 * Real.log (t₂ / (2 * Real.pi)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  intro t₁ t₂ ht1 h12 hne1 hne2
  have ht1pos : 0 < t₁ := lt_trans (by positivity) ht1
  have ht2' : 168 * Real.pi ≤ t₂ := ht1.le.trans h12.le
  have hlogeq : Real.log t₂ = Real.log (t₂ / (2 * Real.pi)) + Real.log (2 * Real.pi) := by
    rw [Real.log_div (ht1pos.trans h12).ne' (by positivity)]; ring
  have hLpos : 0 ≤ Real.log (t₂ / (2 * Real.pi)) :=
    Real.log_nonneg <| (one_le_div (by positivity)).2 <| by nlinarith
  have hlogmono := Real.log_le_log ht1pos h12.le
  have hm₁ := mul_le_mul_of_nonneg_left hlogmono hb₁
  have hm₂ := mul_le_mul_of_nonneg_left hlogmono hb₂
  have hmul := mul_le_mul_of_nonneg_right hb hLpos
  have e1 : Real.pi * |∫ t in t₁..t₂, argZeta t|
      = |logNormZetaIntegral t₂ - logNormZetaIntegral t₁| := by
    rw [← pi_mul_integral_argZeta_eq_sub h12 ht1pos hne1 hne2, abs_mul, abs_of_pos hπ]
  refine le_of_mul_le_mul_left ?_ hπ
  rw [e1, mul_add, mul_div_cancel₀ _ hπ.ne', abs_le]
  constructor <;>
    nlinarith [ha₁ t₁ ht1.le hne1, ha₁ t₂ ht2' hne2, ha₂ t₁ ht1.le hne1, ha₂ t₂ ht2' hne2]
end
end CertificatePort75
section CertificatePort76
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Function Set
private lemma summable_and_riemannZeta_ofReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-σ)) ∧
      riemannZeta (σ : ℂ) = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  refine ⟨?_, ?_⟩
  · refine ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hneg)).congr (fun n ↦ ?_)
    rw [Nat.cast_add, Nat.cast_one]
  · rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hσ), Complex.ofReal_tsum]
    refine tsum_congr (fun n ↦ ?_)
    have hbase : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.rpow_neg hbase, Complex.ofReal_inv, Complex.ofReal_cpow hbase, one_div]
    push_cast
    ring
private lemma integral_Ioi_rpow_le_tsum_shift {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    ((k : ℝ) + 1) ^ (1 - σ) / (σ - 1) ≤ ∑' n : ℕ, (((n + k : ℕ) : ℝ) + 1) ^ (-σ) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  have hb : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  obtain ⟨hsum, -⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  set a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ (-σ) with ha
  have hintval : ∫ x in Set.Ioi ((k : ℝ) + 1), x ^ (-σ) = ((k : ℝ) + 1) ^ (1 - σ) / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt hneg hb, show (-σ + 1 : ℝ) = -(σ - 1) by ring, neg_div_neg_eq,
      show (-(σ - 1) : ℝ) = 1 - σ by ring]
  rw [← hintval]
  refine Real.integral_Ioi_le_tsum_of_window k hsum (integrableOn_Ioi_rpow_of_lt hneg hb)
    fun N ↦ (Real.antitoneOn_rpow_neg_Icc (a := (k : ℝ) + 1) (b := (k : ℝ) + 1 + (N : ℝ))
      (by linarith) hb).integral_le_sum.trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
  show ((k : ℝ) + 1 + (i : ℝ)) ^ (-σ) = a (i + k)
  simp only [ha]; congr 1; push_cast; ring
theorem one_div_sub_one_le_riemannZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  obtain ⟨-, hzeq⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  rw [hzeq, Complex.ofReal_re]
  simpa using integral_Ioi_rpow_le_tsum_shift hσ 0
theorem riemannZeta_ofReal_ge_sharp {σ : ℝ} (hσ : 1 < σ) :
    1 + 2 ^ (-σ) + 3 ^ (-σ) + 4 ^ (1 - σ) / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  obtain ⟨hsum, hzeq⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  set a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ (-σ) with ha
  rw [hzeq, Complex.ofReal_re]
  have htail : (4 : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∑' n, a (n + 3) := by
    have h := integral_Ioi_rpow_le_tsum_shift hσ 3
    rw [show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num] at h
    simpa [ha] using h
  have hfirst : (∑ i ∈ Finset.range 3, a i) = 1 + 2 ^ (-σ) + 3 ^ (-σ) := by
    simp only [ha, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Real.one_rpow]
  rw [(hsum.sum_add_tsum_nat_add 3).symm, hfirst]
  linarith [htail]
section Digamma
open Complex.Stirling MeasureTheory
open scoped Nat Real
end Digamma
open scoped LSeries.notation
open ArithmeticFunction
open scoped Real
private noncomputable def negZetaDerivAntideriv (σ x : ℝ) : ℝ :=
  -(1 / (σ - 1)) * (x ^ (1 - σ) * Real.log x) - (1 / (σ - 1) ^ 2) * x ^ (1 - σ)
private lemma hasDerivAt_negZetaDerivAntideriv {σ : ℝ} (hσ : 1 < σ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (negZetaDerivAntideriv σ) (Real.log x * x ^ (-σ)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hc : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
  have hA : HasDerivAt (fun y : ℝ ↦ y ^ (1 - σ)) ((1 - σ) * x ^ (1 - σ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have h1 : HasDerivAt (fun y : ℝ ↦ y ^ (1 - σ) * Real.log y)
      ((1 - σ) * x ^ (1 - σ - 1) * Real.log x + x ^ (1 - σ) * x⁻¹) x := hA.mul hlog
  have p1 : x ^ (1 - σ - 1) = x ^ (-σ) := by rw [show (1 - σ - 1) = -σ by ring]
  have p2 : x ^ (1 - σ) * x⁻¹ = x ^ (-σ) := by
    rw [show x⁻¹ = x ^ (-1 : ℝ) from (Real.rpow_neg_one x).symm, ← Real.rpow_add hx,
      show (1 - σ + -1 : ℝ) = -σ by ring]
  rw [show Real.log x * x ^ (-σ)
      = -(1 / (σ - 1)) * ((1 - σ) * x ^ (1 - σ - 1) * Real.log x + x ^ (1 - σ) * x⁻¹)
        - 1 / (σ - 1) ^ 2 * ((1 - σ) * x ^ (1 - σ - 1)) from by rw [p1, p2]; field_simp; ring]
  exact (h1.const_mul (-(1 / (σ - 1)))).sub (hA.const_mul (1 / (σ - 1) ^ 2))
private lemma tendsto_negZetaDerivAntideriv {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (negZetaDerivAntideriv σ) atTop (𝓝 0) := by
  have hc : (0 : ℝ) < σ - 1 := by linarith
  have h1 : Tendsto (fun x : ℝ ↦ x ^ (1 - σ)) atTop (𝓝 0) := by
    simpa [show -(σ - 1) = 1 - σ by ring] using tendsto_rpow_neg_atTop hc
  have h2 : Tendsto (fun x : ℝ ↦ x ^ (1 - σ) * Real.log x) atTop (𝓝 0) := by
    refine ((isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show (1 - σ) = -(σ - 1) by ring, Real.rpow_neg hx.le, div_eq_mul_inv, mul_comm]
  have hcomb := (h2.const_mul (-(1 / (σ - 1)))).sub (h1.const_mul (1 / (σ - 1) ^ 2))
  rw [show (fun x : ℝ ↦ -(1 / (σ - 1)) * (x ^ (1 - σ) * Real.log x)
    - 1 / (σ - 1) ^ 2 * x ^ (1 - σ)) = negZetaDerivAntideriv σ from rfl] at hcomb
  simpa using hcomb
theorem neg_deriv_riemannZeta_ofReal_le {σ : ℝ} (hσ : 1 < σ) :
    (- deriv riemannZeta (σ : ℂ)).re ≤
      Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
        + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) := by
  set f : ℝ → ℝ := fun x ↦ Real.log x * x ^ (-σ) with hf
  set b : ℕ → ℝ := fun n ↦ Real.log n * (n : ℝ) ^ (-σ) with hb
  have habs : LSeries.abscissaOfAbsConv 1 < ((σ : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_one, Complex.ofReal_re]; exact_mod_cast hσ
  have hEv : riemannZeta =ᶠ[𝓝 (σ : ℂ)] LSeries 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < ((σ : ℂ)).re by rwa [Complex.ofReal_re])] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  have h1 : HasSum b (- deriv riemannZeta (σ : ℂ)).re := by
    have h0 : HasSum (LSeries.term (LSeries.logMul 1) (σ : ℂ)) (- deriv riemannZeta (σ : ℂ)) := by
      rw [hEv.deriv_eq, LSeries_deriv habs, neg_neg]
      exact (LSeriesSummable_logMul_of_lt_re habs).hasSum
    refine (Complex.hasSum_re h0).congr_fun fun n ↦ Eq.symm ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hb, LSeries.term]
    · have hnpos : 0 < (n : ℝ) := by positivity
      rw [LSeries.term_of_ne_zero hn]
      simp only [hb, LSeries.logMul, Pi.one_apply, mul_one]
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
          ← Complex.ofReal_log hnpos.le, ← Complex.ofReal_cpow hnpos.le,
          ← Complex.ofReal_div, Complex.ofReal_re, Real.rpow_neg hnpos.le, div_eq_mul_inv]
  have hbsum : Summable b := h1.summable
  rw [← h1.tsum_eq]
  have hlog3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hderivf : ∀ {x : ℝ}, 0 < x →
      HasDerivAt f (x⁻¹ * x ^ (-σ) + Real.log x * (-σ * x ^ (-σ - 1))) x := fun hx ↦
    (Real.hasDerivAt_log hx.ne').mul (Real.hasDerivAt_rpow_const (Or.inl hx.ne'))
  have hdf : ∀ x ∈ Set.Ici (3 : ℝ), DifferentiableAt ℝ f x := fun x hx ↦
    (hderivf (by simp only [Set.mem_Ici] at hx; linarith)).differentiableAt
  have hderiv_np : ∀ x ∈ Set.Ioi (3 : ℝ), deriv f x ≤ 0 := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogx : (1 : ℝ) < Real.log x := hlog3.trans_le (Real.log_le_log (by norm_num) hx.le)
    rw [(hderivf hxpos).deriv, show x⁻¹ * x ^ (-σ) = x ^ (-σ - 1) by
      rw [show x⁻¹ = x ^ (-1 : ℝ) from (Real.rpow_neg_one x).symm, ← Real.rpow_add hxpos,
        show (-1 + -σ : ℝ) = -σ - 1 by ring]]
    nlinarith [Real.rpow_pos_of_pos hxpos (-σ - 1), hlogx, hσ,
      mul_nonneg (by linarith : (0 : ℝ) ≤ σ - 1) (by linarith : (0 : ℝ) ≤ Real.log x - 1)]
  have hanti : AntitoneOn f (Set.Ici (3 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 3)
      (fun x hx ↦ (hdf x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hdf x (interior_subset hx)).differentiableWithinAt) ?_
    rw [interior_Ici]; exact hderiv_np
  have hcont : ContinuousWithinAt (negZetaDerivAntideriv σ) (Set.Ici 3) 3 :=
    (hasDerivAt_negZetaDerivAntideriv hσ (by norm_num)).continuousAt.continuousWithinAt
  have hderivF : ∀ x ∈ Set.Ioi (3 : ℝ), HasDerivAt (negZetaDerivAntideriv σ) (f x) x :=
    fun x hx ↦ hasDerivAt_negZetaDerivAntideriv hσ (by simp only [Set.mem_Ioi] at hx; linarith)
  have hfpos : ∀ x ∈ Set.Ioi (3 : ℝ), 0 ≤ f x := fun x hx ↦
    mul_nonneg (Real.log_nonneg (by simp only [Set.mem_Ioi] at hx; linarith))
      (Real.rpow_nonneg (by simp only [Set.mem_Ioi] at hx; linarith) _)
  have hlim := tendsto_negZetaDerivAntideriv hσ
  have htail : ∑' k, b (k + 4) ≤ (0 : ℝ) - negZetaDerivAntideriv σ 3 := by
    refine (Real.tsum_le_integral_Ioi_of_window 4 hbsum
        (MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderivF hfpos hlim)
        (fun N ↦ le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
          (hanti.mono Set.Icc_subset_Ici_self).sum_le_integral)).trans_eq
      (MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderivF hfpos hlim)
    simp only [hb, hf]
    rw [show ((i + 4 : ℕ) : ℝ) = 3 + ((i + 1 : ℕ) : ℝ) by push_cast; ring]
  have hfirst : (∑ i ∈ Finset.range 4, b i) = Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ) := by
    simp only [hb, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Real.log_zero]
  have hFval : (0 : ℝ) - negZetaDerivAntideriv σ 3
      = 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) := by
    simp only [negZetaDerivAntideriv]; ring
  rw [(hbsum.sum_add_tsum_nat_add 4).symm, hfirst]
  linarith [hFval ▸ htail]
private lemma log_three_le : Real.log 3 ≤ 1099 / 1000 := by
  linarith [Real.log_three_lt_d9]
private lemma tsum_norm_term_vonMangoldt_eq_and_pos {σ : ℝ} (hσ : 1 < σ) :
    ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖
        = (- deriv riemannZeta (σ : ℂ)).re * ((riemannZeta (σ : ℂ)).re)⁻¹ ∧
      0 < (riemannZeta (σ : ℂ)).re ∧ 0 ≤ (- deriv riemannZeta (σ : ℂ)).re := by
  set s : ℂ := (σ : ℂ) with hsdef
  have hs : 1 < s.re := by rw [hsdef, Complex.ofReal_re]; exact hσ
  have hnorm_re : ∀ n : ℕ, (LSeries.term ↗Λ s n).re = ‖LSeries.term ↗Λ s n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hnpos : 0 < (n : ℝ) := by positivity
      rw [show LSeries.term ↗Λ s n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) from by
            rw [LSeries.term_of_ne_zero hn, hsdef,
              show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
              ← Complex.ofReal_cpow hnpos.le, ← Complex.ofReal_div],
          Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hnpos.le σ))]
  have hD : ∑' n, ‖LSeries.term ↗Λ s n‖ = (LSeries ↗Λ s).re :=
    ((Complex.hasSum_re (LSeriesSummable_vonMangoldt hs).hasSum).congr_fun
      (fun n ↦ (hnorm_re n).symm)).tsum_eq
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s = (((1 / ((n : ℝ) + 1) ^ σ : ℝ)) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, hsdef, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have hζim : (riemannZeta s).im = 0 := by
    rw [hsdef, zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.ofReal_re]; exact hσ),
        tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_im]
  have hσ1pos : (0 : ℝ) < σ - 1 := by linarith
  have hζpos : 0 < (riemannZeta s).re :=
    lt_of_lt_of_le (by positivity) (one_div_sub_one_le_riemannZeta_ofReal hσ)
  set r : ℝ := (riemannZeta s).re with hrdef
  have hζeq : riemannZeta s = (r : ℂ) :=
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im, hζim])
  have hDeq : ∑' n, ‖LSeries.term ↗Λ s n‖ = (- deriv riemannZeta s).re * r⁻¹ := by
    rw [hD, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hζeq, div_eq_mul_inv,
      ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  refine ⟨hDeq, hζpos, ?_⟩
  nlinarith [hDeq ▸ tsum_nonneg (fun n ↦ norm_nonneg (LSeries.term ↗Λ s n)), inv_pos.mpr hζpos]
private lemma rpow_pow_25 {x e : ℝ} (hx : 0 ≤ x) {k : ℕ} (he : e * (25 : ℕ) = -(k : ℕ)) :
    (x ^ e) ^ (25 : ℕ) = (x ^ k)⁻¹ := by
  rw [← Real.rpow_natCast (x ^ e) 25, ← Real.rpow_mul hx, he, Real.rpow_neg hx, Real.rpow_natCast]
private lemma inner_pole_bound_124 :
    Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2 ≤ 439 / 20 := by
  rw [show Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2
    = Real.log 3 * (25 / 6) + 625 / 36 by ring]
  linarith [log_three_le]
private lemma rpow_two_neg_124_ge : (42 / 100 : ℝ) ≤ (2 : ℝ) ^ (-(124 / 100) : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_three_neg_124_ge : (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (-(124 / 100) : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_four_one_sub_124_ge : (71 / 100 : ℝ) ≤ (4 : ℝ) ^ (1 - 124 / 100 : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (1 - 124 / 100 : ℝ) * (25 : ℕ) = -(6 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_two_neg_124_le : (2 : ℝ) ^ (-(124 / 100) : ℝ) ≤ 43 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_three_neg_124_le : (3 : ℝ) ^ (-(124 / 100) : ℝ) ≤ 27 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_three_one_sub_124_le : (3 : ℝ) ^ (1 - 124 / 100 : ℝ) ≤ 77 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (1 - 124 / 100 : ℝ) * (25 : ℕ) = -(6 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma riemannZeta_ofReal_124_ge :
    (462 / 100 : ℝ) ≤ (riemannZeta ((124 / 100 : ℝ) : ℂ)).re := by
  have h4div : (1775 / 600 : ℝ) ≤ (4 : ℝ) ^ (1 - 124 / 100 : ℝ) / ((124 / 100 : ℝ) - 1) := by
    rw [show ((124 / 100 : ℝ) - 1) = 6 / 25 by norm_num,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 6 / 25)]
    linarith [rpow_four_one_sub_124_ge]
  linarith [riemannZeta_ofReal_ge_sharp (σ := (124 / 100 : ℝ)) (by norm_num),
    rpow_two_neg_124_ge, rpow_three_neg_124_ge, h4div]
private lemma neg_deriv_riemannZeta_124_le :
    (- deriv riemannZeta ((124 / 100 : ℝ) : ℂ)).re ≤ 35 / 2 := by
  refine (neg_deriv_riemannZeta_ofReal_le (by norm_num : (1 : ℝ) < 124 / 100)).trans ?_
  have ht1 : Real.log 2 * 2 ^ (-(124 / 100) : ℝ) ≤ (6932 / 10000) * (43 / 100) :=
    mul_le_mul (by linarith [Real.log_two_lt_d9]) rpow_two_neg_124_le
      (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have ht2 : Real.log 3 * 3 ^ (-(124 / 100) : ℝ) ≤ (1099 / 1000) * (27 / 100) :=
    mul_le_mul log_three_le rpow_three_neg_124_le (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have ht3 : 3 ^ (1 - 124 / 100 : ℝ)
      * (Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2)
      ≤ (77 / 100) * (439 / 20) :=
    mul_le_mul rpow_three_one_sub_124_le inner_pole_bound_124 (by positivity) (by norm_num)
  linarith [ht1, ht2, ht3]
theorem tsum_vonMangoldt_norm_le_124_sharp :
    ∑' n, ‖LSeries.term ↗Λ ((124 / 100 : ℝ) : ℂ) n‖ ≤ 379 / 100 := by
  obtain ⟨hDeq, hζpos, -⟩ :=
    tsum_norm_term_vonMangoldt_eq_and_pos (show (1 : ℝ) < 124 / 100 by norm_num)
  set A : ℝ := (- deriv riemannZeta ((124 / 100 : ℝ) : ℂ)).re with hAdef
  set r : ℝ := (riemannZeta ((124 / 100 : ℝ) : ℂ)).re with hrdef
  have hinvle : r⁻¹ ≤ 100 / 462 := by
    rw [show (100 / 462 : ℝ) = (462 / 100)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) riemannZeta_ofReal_124_ge
  rw [hDeq]
  calc A * r⁻¹ ≤ (35 / 2) * (100 / 462) :=
        mul_le_mul neg_deriv_riemannZeta_124_le hinvle (inv_pos.mpr hζpos).le (by norm_num)
    _ ≤ 379 / 100 := by norm_num
private lemma le_norm_of_im_eq {z : ℂ} {t : ℝ} (ht : 0 < t) (h : z.im = t) : t ≤ ‖z‖ := by
  simpa [h, abs_of_pos ht] using Complex.abs_im_le_norm z
private lemma re_digamma_shiftedLine_le {d t : ℝ} (hdlt : 1 / 2 < d) (hd1 : d ≤ 1)
    (ht : 168 * π ≤ t) :
    (Complex.digamma (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I) / 2)).re
      ≤ Real.log t - Real.log 2 + 2 / 100 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  obtain ⟨hsre, hsim, -, -, -, -, -, hsnorm_pos, hsnorm_ub⟩ := shiftedLine_setup hdlt ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  have hs_ge_t : t ≤ ‖s‖ := le_norm_of_im_eq ht0 hsim
  have hz : 0 < (s / 2).re := by rw [Complex.div_ofNat_re, hsre]; linarith
  have hnorm_half : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  have hdig := re_digamma_le (C := 1) hz
    (by simpa using Complex.Stirling.norm_digammaRemainderIoi_le' (s / 2) hz 1 le_rfl)
  rw [show (1 / 2 + (1 : ℝ)) = 3 / 2 by norm_num] at hdig
  have hlog_half : Real.log ‖s / 2‖ ≤ Real.log t + (1 / 2 + d) / (168 * π) - Real.log 2 := by
    rw [hnorm_half, Real.log_div hsnorm_pos.ne' (by norm_num)]
    have h3 := Real.log_add_le (u := 1 / 2 + d) (t := t) (by linarith) ht0
    have h4 : (1 / 2 + d) / t ≤ (1 / 2 + d) / (168 * π) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) ht
    linarith [Real.log_le_log hsnorm_pos hsnorm_ub]
  have hfrac : (3 / 2 : ℝ) / ‖s / 2‖ ≤ 3 / (168 * π) := by
    rw [hnorm_half]
    calc (3 / 2 : ℝ) / (‖s‖ / 2) ≤ (3 / 2 : ℝ) / (t / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      _ = 3 / t := by ring
      _ ≤ 3 / (168 * π) := div_le_div_of_nonneg_left (by norm_num) (by positivity) ht
  have htiny : (1 / 2 + d) / (168 * π) + 3 / (168 * π) ≤ 2 / 100 := by
    rw [← add_div, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  linarith
private lemma re_logDeriv_riemannZeta_le_of_re {s : ℂ} {σ D : ℝ} (hσ : 1 < s.re) (hsre : s.re = σ)
    (hVM : ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖ ≤ D) : (logDeriv riemannZeta s).re ≤ D := by
  refine (re_logDeriv_riemannZeta_le hσ).trans ?_
  rw [show (∑' n, ‖LSeries.term ↗Λ s n‖) = ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖ from
    tsum_congr fun n ↦ by rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre, Complex.ofReal_re]]
  exact hVM
theorem tsum_re_inv_riemannXiZeros_sub_le_tight_of {t D : ℝ} (ht : 168 * π ≤ t)
    (hVM : ∑' n, ‖LSeries.term ↗Λ ((124 / 100 : ℝ) : ℂ) n‖ ≤ D) :
    ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + (D - 3 / 5) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have ht500 : (500 : ℝ) ≤ t := le_trans (by nlinarith [Real.pi_gt_three]) ht
  set d : ℝ := 74 / 100 with hd
  have hdlt : (1 / 2 : ℝ) < d := by rw [hd]; norm_num
  have hPair := summable_pairDensity (d := d) (t := t) hdlt
  obtain ⟨hsre, hsim, hre, hreσ, hs1, hsne, -, -, -⟩ := shiftedLine_setup hdlt ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  have hDir : (logDeriv riemannZeta s).re ≤ D :=
    re_logDeriv_riemannZeta_le_of_re hreσ (by rw [hsre, hd]; norm_num) hVM
  have hinv500 : t⁻¹ ≤ 1 / 500 := by rw [one_div]; exact inv_anti₀ (by norm_num) ht500
  have b2 : (1 / s).re ≤ 1 / 500 := (Complex.re_one_div_le_norm_inv s).trans
    ((inv_anti₀ ht0 (le_norm_of_im_eq ht0 hsim)).trans hinv500)
  have hs1im : (s - 1).im = t := by rw [Complex.sub_im, Complex.one_im, hsim]; ring
  have b3 : (1 / (s - 1)).re ≤ 1 / 500 := (Complex.re_one_div_le_norm_inv _).trans
    ((inv_anti₀ ht0 (le_norm_of_im_eq ht0 hs1im)).trans hinv500)
  have hpsi_bound : 1 / 2 * (Complex.digamma (s / 2)).re
      ≤ 1 / 2 * Real.log t + 1 / 100 - 1 / 2 * Real.log 2 := by
    have hcore := re_digamma_shiftedLine_le hdlt (by rw [hd]; norm_num) ht
    rw [← hsdef] at hcore
    linarith
  have hlogπ_ge : (1 : ℝ) ≤ Real.log π := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1)
      (le_of_lt (lt_trans (lt_trans Real.exp_one_lt_d9 (by norm_num)) Real.pi_gt_three))
  have hlog2_ge := Real.log_two_gt_d9
  rw [tsum_re_inv_riemannXiZeros_sub_eq hre hs1 hsne hPair]
  linarith [b2, b3, hpsi_bound, hDir, hlogπ_ge, hlog2_ge]
theorem tsum_re_inv_riemannXiZeros_sub_le_tight_sharp (t : ℝ) (ht : 168 * π ≤ t) :
    ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + 319 / 100 := by
  linarith [tsum_re_inv_riemannXiZeros_sub_le_tight_of ht tsum_vonMangoldt_norm_le_124_sharp]
end
end CertificatePort76
section CertificatePort77
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Function Set
open scoped Real
section Tail
open MeasureTheory
theorem tsum_one_div_nat_add_two_rpow_le_majorant {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ 2 ^ (-σ) + 2 ^ (1 - σ) / (σ - 1) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ σ) :=
    Real.summable_one_div_nat_add_two_rpow hσ
  rw [hsum.tsum_eq_zero_add]
  have h0 : 1 / (((0 : ℕ) : ℝ) + 2) ^ σ = (2 : ℝ) ^ (-σ) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div]
    norm_num
  have htail : ∑' n : ℕ, 1 / (((n : ℕ) + 1 : ℝ) + 2) ^ σ ≤ 2 ^ (1 - σ) / (σ - 1) := by
    have h := Real.tsum_one_div_nat_add_rpow_le 2 (by norm_num) hσ
    norm_num at h
    refine le_trans (le_of_eq (tsum_congr fun n ↦ ?_)) h
    rw [show ((n : ℕ) + 1 : ℝ) + 2 = (n : ℝ) + 3 by ring, one_div]
  refine add_le_add (le_of_eq ?_) (le_trans (le_of_eq (tsum_congr fun n ↦ ?_)) htail)
  · exact h0
  · push_cast; ring_nf
theorem Real.rpow_two_neg_le_one_sub_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (2 : ℝ) ^ (-u) ≤ 1 - u / 2 := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-Real.log 2))
    (by linarith : (0 : ℝ) ≤ 1 - u) hu0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show Real.log 2 * -u = u * -Real.log 2 by ring]
  linarith [h]
private lemma two_rpow_one_sub (σ : ℝ) : (2 : ℝ) ^ (1 - σ) = 2 * 2 ^ (-σ) := by
  rw [show (1 - σ : ℝ) = 1 + -σ by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one]
private lemma integrableOn_two_rpow_neg_Ioi (c : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (-σ)) (Set.Ioi c) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : IntegrableOn (fun σ : ℝ ↦ Real.exp (-(Real.log 2 * σ))) (Set.Ioi c) :=
    Real.integrableOn_exp_neg_mul_Ioi hl2 c
  refine hexp.congr_fun (fun σ _ ↦ ?_) measurableSet_Ioi
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf
private lemma integral_two_rpow_neg_Ioi (c : ℝ) :
    ∫ σ in Set.Ioi c, (2 : ℝ) ^ (-σ) = 2 ^ (-c) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcong : ∫ σ in Set.Ioi c, (2 : ℝ) ^ (-σ)
      = ∫ σ in Set.Ioi c, Real.exp (-Real.log 2 * σ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun σ _ ↦ ?_
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [hcong, integral_exp_mul_Ioi (by linarith) c,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [div_eq_div_iff (ne_of_lt (by linarith : -Real.log 2 < 0)) (ne_of_gt hl2)]
  rw [show -Real.log 2 * c = Real.log 2 * -c by ring]
  ring
private lemma integrableOn_tail_majorant_snd {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) (Set.Ioi c) := by
  have hcont : ContinuousOn (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) (Set.Ioi c) := by
    have h2 : Continuous fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) :=
      (Real.continuous_const_rpow (by norm_num)).comp (continuous_const.sub continuous_id)
    exact h2.continuousOn.div ((continuous_id.sub continuous_const).continuousOn)
      (fun σ hσ ↦ ne_of_gt (by simp only [Set.mem_Ioi] at hσ; linarith))
  refine Integrable.mono' ((integrableOn_two_rpow_neg_Ioi c).const_mul (2 / (c - 1)))
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  simp only [Set.mem_Ioi] at hσ
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.rpow_nonneg (by norm_num) _) hσ1.le), two_rpow_one_sub,
    show 2 / (c - 1) * (2 : ℝ) ^ (-σ) = 2 * (2 : ℝ) ^ (-σ) / (c - 1) by ring]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
private lemma integrableOn_tail_majorant {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) (Set.Ioi c) :=
  (integrableOn_two_rpow_neg_Ioi _).add (integrableOn_tail_majorant_snd hc)
private lemma integral_tail_majorant_le_core {a : ℝ} (ha : 1 < a) (ha2 : a ≤ 2) :
    ∫ σ in Set.Ioi a, ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1))
      ≤ 0.7214 + (Real.log (a - 1)⁻¹ + a / 2 - 1) + 0.7214 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [integral_add (integrableOn_two_rpow_neg_Ioi _) (integrableOn_tail_majorant_snd ha)]
  have hp1 : ∫ σ in Set.Ioi a, (2 : ℝ) ^ (-σ) ≤ 0.7214 := by
    rw [integral_two_rpow_neg_Ioi, div_le_iff₀ hl2]
    have h2c : (2 : ℝ) ^ (-a) ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : (-a : ℝ) ≤ -1)
      rwa [Real.rpow_neg_one, ← one_div] at h
    linarith [Real.log_two_gt_d9]
  have hsplit : ∫ σ in Set.Ioi a, (2 : ℝ) ^ (1 - σ) / (σ - 1)
      = (∫ σ in Set.Ioc a 2, (2 : ℝ) ^ (1 - σ) / (σ - 1))
        + ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1) := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_tail_majorant_snd ha).mono_set Set.Ioc_subset_Ioi_self)
      (integrableOn_tail_majorant_snd (by norm_num : (1 : ℝ) < 2)),
      Set.Ioc_union_Ioi_eq_Ioi ha2]
  have hmid : ∫ σ in Set.Ioc a 2, (2 : ℝ) ^ (1 - σ) / (σ - 1)
      ≤ Real.log (a - 1)⁻¹ + a / 2 - 1 := by
    rw [← intervalIntegral.integral_of_le ha2]
    have hII : IntervalIntegrable (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) volume a 2 := by
      apply ContinuousOn.intervalIntegrable
      have h2 : Continuous fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) :=
        (Real.continuous_const_rpow (by norm_num)).comp (continuous_const.sub continuous_id)
      refine h2.continuousOn.div ((continuous_id.sub continuous_const).continuousOn)
        fun σ hσ ↦ ne_of_gt ?_
      rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
      linarith [hσ.1]
    have hII' : IntervalIntegrable (fun σ : ℝ ↦ 1 / (σ - 1) - 1 / 2) volume a 2 := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.sub (ContinuousOn.div continuousOn_const
        ((continuous_id.sub continuous_const).continuousOn) fun σ hσ ↦ ne_of_gt ?_)
        continuousOn_const
      rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
      linarith [hσ.1]
    have hle : ∫ σ in a..2, (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∫ σ in a..2, (1 / (σ - 1) - 1 / 2) := by
      refine intervalIntegral.integral_mono_on ha2 hII hII' fun σ hσ ↦ ?_
      rw [Set.mem_Icc] at hσ
      have hσ1 : (0 : ℝ) < σ - 1 := by linarith [hσ.1]
      have hchord : (2 : ℝ) ^ (1 - σ) ≤ 1 - (σ - 1) / 2 := by
        have h := Real.rpow_two_neg_le_one_sub_half (u := σ - 1) (by linarith [hσ.1])
          (by linarith [hσ.2])
        rwa [show (-(σ - 1) : ℝ) = 1 - σ by ring] at h
      calc (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ (1 - (σ - 1) / 2) / (σ - 1) := by gcongr
        _ = 1 / (σ - 1) - 1 / 2 := by field_simp
    have hFTC : ∫ σ in a..2, (1 / (σ - 1) - 1 / 2) = Real.log (a - 1)⁻¹ + a / 2 - 1 := by
      have hderiv : ∀ σ ∈ Set.uIcc a 2,
          HasDerivAt (fun x : ℝ ↦ Real.log (x - 1) - x / 2) (1 / (σ - 1) - 1 / 2) σ := by
        intro σ hσ
        rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
        have hne : σ - 1 ≠ 0 := ne_of_gt (by linarith [hσ.1])
        have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x - 1)) (1 / (σ - 1)) σ := by
          simpa using ((hasDerivAt_id σ).sub_const 1).log hne
        exact h1.sub ((hasDerivAt_id σ).div_const 2)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII',
        show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, Real.log_inv]
      ring
    exact hle.trans_eq hFTC
  have hp3 : ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ 0.7214 := by
    have hmono : ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1)
        ≤ ∫ σ in Set.Ioi (2 : ℝ), 2 * (2 : ℝ) ^ (-σ) := by
      refine setIntegral_mono_on (integrableOn_tail_majorant_snd (by norm_num : (1 : ℝ) < 2))
        ((integrableOn_two_rpow_neg_Ioi 2).const_mul 2)
        measurableSet_Ioi fun σ hσ ↦ ?_
      simp only [Set.mem_Ioi] at hσ
      rw [two_rpow_one_sub]
      exact div_le_self (by positivity) (by linarith)
    rw [integral_const_mul, integral_two_rpow_neg_Ioi] at hmono
    have h22 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
      rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [h22] at hmono
    refine hmono.trans ?_
    rw [show (2 : ℝ) * (1 / 4 / Real.log 2) = 1 / 2 / Real.log 2 by ring, div_le_iff₀ hl2]
    linarith [Real.log_two_gt_d9]
  rw [hsplit]
  linarith [hp1, hmid, hp3]
private lemma log_25_24_mul_two_pow_le (k : ℕ) :
    Real.log (25 / 24 * 2 ^ k) ≤ 1 / 24 + k * Real.log 2 := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 25 / 24 by norm_num)]
private lemma neg_le_logNormZetaIntegral_of_integral_majorant_le {a B : ℝ} (ha1 : 1 < a)
    (hIN : ∫ σ in Set.Ioi a, ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) ≤ B) (b t : ℝ) :
    (-B ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-B ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_tsum_le ha1 (integrableOn_tail_majorant ha1)
    (fun _ hσ ↦ tsum_one_div_nat_add_two_rpow_le_majorant (lt_trans ha1 hσ)) hIN
theorem integral_tail_majorant_le_124 :
    ∫ σ in Set.Ioi (124 / 100 : ℝ), ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) ≤ 5 / 2 := by
  have h := integral_tail_majorant_le_core (a := 124 / 100) (by norm_num) (by norm_num)
  rw [show ((124 / 100 : ℝ) - 1)⁻¹ = 25 / 6 by norm_num] at h
  have hlog : Real.log (25 / 6) ≤ 1 / 24 + 2 * Real.log 2 := by
    have h2 := log_25_24_mul_two_pow_le 2
    rw [show (25 / 24 * 2 ^ (2 : ℕ) : ℝ) = 25 / 6 by norm_num] at h2
    push_cast at h2; linarith
  linarith [h, hlog, Real.log_two_lt_d9]
theorem logNormZetaIntegral_tail_ge_tight (t : ℝ) :
    (-(5 / 2) ≤ ∫ σ in Set.Ioi (124 / 100 : ℝ),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-(5 / 2) ≤ ∫ σ in Set.Ioo (124 / 100 : ℝ) (198 / 100),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_integral_majorant_le (a := 124 / 100) (by norm_num)
    integral_tail_majorant_le_124 (198 / 100) t
end Tail
end
end CertificatePort77
section CertificatePort78
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Function Set
open scoped Real
private lemma log_pi_le_two_log_two : Real.log π ≤ 2 * Real.log 2 := by
  rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
  exact Real.log_le_log Real.pi_pos Real.pi_lt_four.le
private lemma log_two_pi_le_three_log_two : Real.log (2 * π) ≤ 3 * Real.log 2 := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']; linarith [log_pi_le_two_log_two]
private lemma logDeriv_riemannXi_zero_eq {B : ℝ}
    (hB : ∀ s, riemannXi s =
      1 / 2 * Complex.exp (B * s) * riemannXiCanonicalProduct riemannXiZeros s) :
    logDeriv riemannXi 0 = (B : ℂ) := by
  have hrep : ∀ s, riemannXi s = Complex.exp (Complex.log (1 / 2) + B * s) *
      riemannXiCanonicalProduct riemannXiZeros s := fun s ↦ by
    rw [hB s, Complex.exp_add, Complex.exp_log (by norm_num)]
  have hde : HasDerivAt (fun s : ℂ ↦ Complex.log (1 / 2) + (B : ℂ) * s) (B : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (B : ℂ)).const_add (Complex.log (1 / 2))
  rw [logDeriv_riemannXi_zero_eq_deriv (by fun_prop) hrep, hde.deriv]
theorem tsum_log_norm_riemannXiZeros_shift_eq {s : ℂ} {d : ℝ}
    (hs : ∀ i, s ≠ riemannXiZeros i) (hsd : ∀ i, s + d ≠ riemannXiZeros i) :
    ∑' i, (Real.log ‖s + ↑d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
      = Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖ := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  have hsum : Summable fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2 := summable_inv_norm_sq_riemannXiZeros
  have hresum : Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := summable_re_inv_riemannXiZeros
  have hκ0 : B + ∑' i, ((riemannXiZeros i)⁻¹).re = 0 := by
    have hBre : (logDeriv riemannXi 0).re = B := by
      rw [logDeriv_riemannXi_zero_eq hB, Complex.ofReal_re]
    have h := hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero
    rwa [hBre] at h
  set ρ := riemannXiZeros
  have hzne : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) → ∀ i, z / ρ i ≠ 1 := fun {z} hz i h ↦
    hz i ((div_eq_one_iff_eq (riemannXiZeros_ne_zero i)).mp h)
  have hsummSplit : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Summable (fun i ↦ Real.log ‖1 - z / ρ i‖ + (z / ρ i).re) := fun {z} hz ↦
    (summable_log_norm_weierstrassE1 ρ hsum z).congr
      (fun i ↦ log_norm_weierstrassE1 (hzne hz i))
  have hlogXi : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Real.log ‖riemannXi z‖
        = Real.log (1 / 2) + B * z.re + Real.log ‖riemannXiCanonicalProduct ρ z‖ := by
    intro z hz
    have hPne : riemannXiCanonicalProduct ρ z ≠ 0 :=
      riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ hsum hz
    have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_ofNat]
    rw [hB z, norm_mul, norm_mul, Complex.norm_exp, h12,
      show ((B : ℂ) * z).re = B * z.re from by rw [Complex.re_ofReal_mul],
      Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hPne),
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hdiffXi : Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖
      = B * d + (Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖) := by
    rw [hlogXi hsd, hlogXi hs, Complex.add_re, Complex.ofReal_re]; ring
  have hterm : ∀ i,
      (Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re)
        = (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) + d * ((ρ i)⁻¹).re := by
    intro i
    have hρ0 := riemannXiZeros_ne_zero i
    have elog : ∀ {w : ℂ}, w ≠ ρ i →
        Real.log ‖1 - w / ρ i‖ = Real.log ‖w - ρ i‖ - Real.log ‖ρ i‖ := by
      intro w hw
      have h1 : (1 : ℂ) - w / ρ i = (ρ i - w) / ρ i := by rw [sub_div, div_self hρ0]
      rw [h1, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hw h.symm))
        (norm_ne_zero_iff.mpr hρ0), norm_sub_rev]
    have hsubdiv : (s + ↑d) / ρ i - s / ρ i = (↑d : ℂ) * (ρ i)⁻¹ := by
      rw [div_sub_div_same, add_sub_cancel_left, div_eq_mul_inv]
    have ere : ((s + ↑d) / ρ i).re - (s / ρ i).re = d * ((ρ i)⁻¹).re := by
      rw [← Complex.sub_re, hsubdiv, Complex.re_ofReal_mul]
    rw [elog (hsd i), elog (hs i)]
    linear_combination ere
  have hD : Summable (fun i ↦ Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) := by
    refine ((hsummSplit hsd).sub (hsummSplit hs)).sub (hresum.mul_left d) |>.congr fun i ↦ ?_
    rw [hterm i]; ring
  have hsplit : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = ∑' i, (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖)
          + d * ∑' i, ((ρ i)⁻¹).re := by
    rw [funext (fun i ↦ hterm i), hD.tsum_add (hresum.mul_left d), tsum_mul_left]
  have hPsub : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖ := by
    rw [(hsummSplit hsd).tsum_sub (hsummSplit hs),
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hsd,
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hs]
  rw [hPsub] at hsplit
  have hfinal : ∑' i, (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖)
      = (Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖) - d * ∑' i, ((ρ i)⁻¹).re := by
    linear_combination -hsplit
  rw [hfinal, hdiffXi]
  linear_combination (-(d : ℝ)) * hκ0
section Assembly
open Complex.Stirling MeasureTheory
private lemma le_logNormZetaIntegral_p1_of {Cψ a₂ : ℝ}
    (hCψ : ∀ t : ℝ, 168 * π ≤ t →
      ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + Cψ)
    (ha₂ : (2 : ℝ) * (74 / 100) ^ 2 * Cψ + 2 * (5 / 2)
        + ((74 / 100) ^ 2 / 2 * (3 * Real.log 2) + (74 / 100) / 2 * Real.log 2
          + (74 / 100) ^ 2 / 10000) ≤ a₂) :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + (74 / 100) ^ 2 / 2 * Real.log t := by
  intro t ht hzero
  have hlt := le_logNormZetaIntegral_of_le (d := 74 / 100) (κ := 0)
    (Ca := (74 / 100) ^ 2 / 2 * (Real.log 2 + Real.log π) + (74 / 100) / 2 * Real.log 2
      + (74 / 100) ^ 2 / 10000)
    (Cψ := Cψ) (Ct := 5 / 2) (by norm_num)
    (fun s hs hsd ↦ by rw [tsum_log_norm_riemannXiZeros_shift_eq hs hsd]; ring)
    (logNormGammaArchimedean_strip_diff_ge_tight (by norm_num) (by norm_num))
    hCψ
    (fun t ↦ by
      rw [show (1 / 2 + 74 / 100 : ℝ) = 124 / 100 by norm_num,
        show (1 / 2 + 2 * (74 / 100) : ℝ) = 198 / 100 by norm_num]
      exact logNormZetaIntegral_tail_ge_tight t)
    (c := 2) (by norm_num) t ht hzero
  have h1 : (74 / 100 : ℝ) ^ 2 / 2 * (Real.log 2 + Real.log π)
      ≤ (74 / 100) ^ 2 / 2 * (3 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith [log_pi_le_two_log_two]) (by positivity)
  nlinarith [hlt, ha₂, h1]
theorem le_logNormZetaIntegral_five :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 933 / 100 + (74 / 100) ^ 2 / 2 * Real.log t :=
  le_logNormZetaIntegral_p1_of tsum_re_inv_riemannXiZeros_sub_le_tight_sharp
    (by nlinarith [Real.log_two_lt_d9, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
theorem norm_integral_argZeta_le_five :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 5 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds' (b₁ := 1 / 8) (b₂ := (74 / 100) ^ 2 / 2)
    (by norm_num) (by positivity) (by nlinarith [Real.pi_gt_d2])
    (fun t ht hzero ↦ logNormZetaIntegral_le_five ht hzero)
    (fun t ht hzero ↦ le_logNormZetaIntegral_five t ht hzero)
      t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  have hconst :
      (5 + 933 / 100 + (1 / 8 + (74 / 100) ^ 2 / 2) * Real.log (2 * π)) / π ≤ 5 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]
end Assembly
section Unconditional
open MeasureTheory
private lemma exists_zeroFree_Ioo {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ t : ℝ, t ∈ Set.Ioo c (c + ε) ∧
      ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0 := by
  have hcε : c < c + ε := by linarith
  have hfin := finite_setOf_riemannZeta_zero_ray_Icc hc hcε.le
  obtain ⟨t, htd⟩ := ((Set.Ioo_infinite hcε).sdiff hfin).nonempty
  rw [Set.mem_sdiff] at htd
  exact ⟨t, htd.1, fun σ hσ hz ↦ htd.2 ⟨⟨σ, hσ, hz⟩, Set.Ioo_subset_Icc_self htd.1⟩⟩
private lemma norm_integral_argZeta_le_unconditional_of {A : ℝ}
    (hbnd : ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ A + 0.128 * Real.log (t₂ / (2 * π)))
    {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁) (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ A + 0.128 * Real.log (t₂ / (2 * π)) := by
  have hπ : 0 < π := Real.pi_pos
  have ht1pos : 0 < t₁ := lt_trans (by positivity) ht1
  have ht2pos : 0 < t₂ := lt_trans ht1pos h12
  have ht1gt1 : (1 : ℝ) < t₁ := by nlinarith [Real.pi_gt_three]
  set m : ℝ := min 1 (t₂ - t₁) with hm
  have hm0 : 0 < m := lt_min one_pos (by linarith)
  have hmlt : m ≤ t₂ - t₁ := min_le_right _ _
  set d : ℕ → ℝ := fun n ↦ min (1 / ((n : ℝ) + 1)) m with hd
  have hd0 : ∀ n, 0 < d n := fun n ↦ lt_min (by positivity) hm0
  have hdm : ∀ n, d n ≤ m := fun n ↦ min_le_right _ _
  have hdinv : ∀ n, d n ≤ 1 / ((n : ℝ) + 1) := fun n ↦ min_le_left _ _
  have hdtend : Tendsto d atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hd0 n).le) hdinv tendsto_one_div_add_atTop_nhds_zero_nat
  choose a hamem hafree using fun n ↦ exists_zeroFree_Ioo ht1pos (hd0 n)
  choose b hbmem hbfree using fun n ↦ exists_zeroFree_Ioo ht2pos (hd0 n)
  have halt : ∀ n, t₁ < a n := fun n ↦ (hamem n).1
  have hault : ∀ n, a n < t₁ + d n := fun n ↦ (hamem n).2
  have hblt : ∀ n, t₂ < b n := fun n ↦ (hbmem n).1
  have hbult : ∀ n, b n < t₂ + d n := fun n ↦ (hbmem n).2
  have hab : ∀ n, a n < b n := fun n ↦ by
    have := hault n; have := hdm n; have := hblt n; linarith
  have hII : IntervalIntegrable argZeta volume (t₁ - 1) (t₂ + 1) :=
    intervalIntegrable_argZeta (by linarith) (by linarith)
  have hle : t₁ - 1 ≤ t₂ + 1 := by linarith
  have hcontOn : ContinuousOn (fun x ↦ ∫ s in t₁..x, argZeta s) (Set.Icc (t₁ - 1) (t₂ + 1)) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := t₁) hII
      (by rw [Set.uIcc_of_le hle]; exact ⟨by linarith, by linarith⟩)
    rwa [Set.uIcc_of_le hle] at this
  have hcatT1 : ContinuousAt (fun x ↦ ∫ s in t₁..x, argZeta s) t₁ :=
    hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcatT2 : ContinuousAt (fun x ↦ ∫ s in t₁..x, argZeta s) t₂ :=
    hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have haup : Tendsto (fun n ↦ t₁ + d n) atTop (𝓝 t₁) := by
    simpa using tendsto_const_nhds.add hdtend
  have hbup : Tendsto (fun n ↦ t₂ + d n) atTop (𝓝 t₂) := by
    simpa using tendsto_const_nhds.add hdtend
  have hatend : Tendsto a atTop (𝓝 t₁) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds haup
      (fun n ↦ (halt n).le) (fun n ↦ (hault n).le)
  have hbtend : Tendsto b atTop (𝓝 t₂) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbup
      (fun n ↦ (hblt n).le) (fun n ↦ (hbult n).le)
  have hsplit : ∀ n, ∫ s in (a n)..(b n), argZeta s
      = (∫ s in t₁..(b n), argZeta s) - ∫ s in t₁..(a n), argZeta s := fun n ↦ by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_argZeta ht1pos (halt n).le)
      (intervalIntegrable_argZeta (lt_trans ht1pos (halt n)) (hab n).le)]
    ring
  have hIb : Tendsto (fun n ↦ ∫ s in t₁..(b n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₂, argZeta s)) := hcatT2.tendsto.comp hbtend
  have hIa : Tendsto (fun n ↦ ∫ s in t₁..(a n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₁, argZeta s)) := hcatT1.tendsto.comp hatend
  rw [intervalIntegral.integral_same] at hIa
  have hlhs : Tendsto (fun n ↦ ∫ s in (a n)..(b n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₂, argZeta s)) := by
    have hd := hIb.sub hIa
    rw [sub_zero] at hd
    exact hd.congr (fun n ↦ (hsplit n).symm)
  have hrhs : Tendsto (fun n ↦ A + 0.128 * Real.log (b n / (2 * π))) atTop
      (𝓝 (A + 0.128 * Real.log (t₂ / (2 * π)))) := by
    have hlog : Tendsto (fun n ↦ Real.log (b n / (2 * π))) atTop
        (𝓝 (Real.log (t₂ / (2 * π)))) :=
      (Real.continuousAt_log (by positivity)).tendsto.comp (hbtend.div_const (2 * π))
    exact tendsto_const_nhds.add (hlog.const_mul 0.128)
  have hbound : ∀ n, |∫ s in (a n)..(b n), argZeta s| ≤ A + 0.128 * Real.log (b n / (2 * π)) :=
    fun n ↦ hbnd (a n) (b n)
      (by have := halt n; linarith) (hab n) (hafree n) (hbfree n)
  exact le_of_tendsto_of_tendsto' hlhs.abs hrhs hbound
theorem norm_integral_argZeta_le_five_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 5 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_five ht1 h12
end Unconditional
end
end CertificatePort78
section CertificatePort79
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open scoped Real
namespace Complex
noncomputable def chi (s : ℂ) : ℂ :=
  Gammaℝ (1 - s) / Gammaℝ s
theorem chi_eq_cpow_mul_Gamma_div_Gamma (s : ℂ) :
    chi s = (π : ℂ) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) / Gamma (s / 2) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [chi, Gammaℝ_def, Gammaℝ_def, ← div_mul_div_comm, ← cpow_sub _ _ hπ,
    show -(1 - s) / 2 - -s / 2 = s - 1 / 2 by ring, mul_div_assoc]
theorem inv_Gammaℂ (s : ℂ) : (Gammaℂ s)⁻¹ = (2 * π) ^ s / (2 * Gamma s) := by
  rw [Gammaℂ_def, cpow_neg, mul_inv, mul_inv, inv_inv, div_eq_mul_inv, mul_inv]
  ring
theorem chi_mul_cos {s : ℂ} (hs : ∀ n : ℕ, s ≠ 2 * n + 1) :
    chi s * cos ((π : ℂ) * s / 2) = (2 * π) ^ s / (2 * Gamma s) := by
  rw [chi, ← inv_Gammaℂ]
  by_cases hcos : cos ((π : ℂ) * s / 2) = 0
  ·
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hsk : s = 2 * (k : ℂ) + 1 :=
      mul_left_cancel₀ hπ (by linear_combination 2 * hk : (π : ℂ) * s = (π : ℂ) * (2 * k + 1))
    rcases le_or_gt 0 k with hk0 | hk0
    · lift k to ℕ using hk0 with n
      exact absurd hsk (hs n)
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m + 1) := ⟨(-k - 1).toNat, by omega⟩
      have hGamma : Gamma s = 0 := by
        refine (Gamma_eq_zero_iff s).2 ⟨2 * m + 1, ?_⟩
        rw [hsk]
        push_cast
        ring
      rw [hcos, mul_zero, Gammaℂ_def, hGamma, mul_zero, inv_zero]
  ·
    have hodd : ∀ n : ℕ, s ≠ -(2 * n + 1) := by
      intro n hsn
      refine hcos ?_
      rw [cos_eq_zero_iff]
      exact ⟨-(n + 1), by rw [hsn]; push_cast; ring⟩
    have hinv : Gammaℝ (1 - s) / Gammaℝ s = (Gammaℂ s * cos ((π : ℂ) * s / 2))⁻¹ := by
      rw [← Gammaℝ_div_Gammaℝ_one_sub hodd, inv_div]
    rw [hinv, mul_inv, inv_mul_cancel_right₀ hcos]
theorem differentiableAt_chi {s : ℂ} (hs : ∀ n : ℕ, s ≠ 2 * n + 1) : DifferentiableAt ℂ chi s := by
  have hfun : chi = fun z : ℂ ↦ (π : ℂ) ^ (z - 1 / 2) * Gamma ((1 - z) / 2) * (Gamma (z / 2))⁻¹ :=
    funext fun z ↦ by rw [chi_eq_cpow_mul_Gamma_div_Gamma, div_eq_mul_inv]
  have h1 : DifferentiableAt ℂ (fun z : ℂ ↦ (π : ℂ) ^ (z - 1 / 2)) s :=
    (differentiableAt_id.sub_const _).const_cpow (Or.inl (ofReal_ne_zero.2 Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun z : ℂ ↦ Gamma ((1 - z) / 2)) s :=
    (differentiableAt_Gamma _ fun m hm ↦ hs m (by linear_combination -2 * hm)).comp s
      (((differentiableAt_const 1).sub differentiableAt_id).div_const 2)
  have h3 : DifferentiableAt ℂ (fun z : ℂ ↦ (Gamma (z / 2))⁻¹) s :=
    (differentiable_one_div_Gamma _).comp s (differentiableAt_id.div_const 2)
  rw [hfun]
  exact (h1.mul h2).mul h3
end Complex
end
end CertificatePort79
section CertificatePort80
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Filter Topology Set
open scoped ComplexConjugate Real Nat
namespace Complex
noncomputable def logGammaAux : ℂ → ℂ :=
  Classical.choose (Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_re_gt 0)
    differentiableOn_digamma_re_pos)
private lemma logGammaAux_hasDerivWithinAt {w : ℂ} (hw : 0 < w.re) :
    HasDerivWithinAt logGammaAux (Complex.digamma w) {z : ℂ | 0 < z.re} w :=
  Classical.choose_spec (Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_re_gt 0)
    differentiableOn_digamma_re_pos) w hw
noncomputable def logGamma (w : ℂ) : ℂ := logGammaAux w - logGammaAux 1
@[simp]
theorem logGamma_one : logGamma 1 = 0 := sub_self _
theorem hasDerivAt_logGamma {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt logGamma (Complex.digamma w) w :=
  ((logGammaAux_hasDerivWithinAt hw).hasDerivAt ((isOpen_re_gt 0).mem_nhds hw)).sub_const
    (logGammaAux 1)
theorem cexp_logGamma {w : ℂ} (hw : 0 < w.re) :
    Complex.exp (logGamma w) = Complex.Gamma w := by
  have hf : DifferentiableOn ℂ (fun z ↦ Complex.exp (logGamma z)) {z : ℂ | 0 < z.re} :=
    fun z hz ↦ ((hasDerivAt_logGamma hz).cexp).differentiableAt.differentiableWithinAt
  have hfn : ∀ z ∈ {z : ℂ | 0 < z.re}, Complex.exp (logGamma z) ≠ 0 :=
    fun z _ ↦ Complex.exp_ne_zero _
  have hlog : EqOn (logDeriv (fun z ↦ Complex.exp (logGamma z)))
      (logDeriv Complex.Gamma) {z : ℂ | 0 < z.re} := by
    intro z hz
    have hd : deriv (fun z ↦ Complex.exp (logGamma z)) z
        = Complex.exp (logGamma z) * Complex.digamma z :=
      ((hasDerivAt_logGamma hz).cexp).deriv
    rw [logDeriv_apply, logDeriv_apply, hd, mul_comm, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one, Complex.digamma_def, logDeriv_apply]
  obtain ⟨c, -, hce⟩ := (logDeriv_eqOn_iff hf differentiableOn_Gamma_re_pos (isOpen_re_gt 0)
    isPreconnected_re_pos (fun _ hz ↦ Complex.Gamma_ne_zero_of_re_pos hz) hfn).mp hlog
  have hc1 : c = 1 := by
    simpa [logGamma_one, Complex.Gamma_one, Pi.smul_apply, smul_eq_mul]
      using (hce (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})).symm
  simpa [Pi.smul_apply, smul_eq_mul, hc1] using hce (show w ∈ {z : ℂ | 0 < z.re} from hw)
theorem digamma_conj (s : ℂ) :
    Complex.digamma (conj s) = conj (Complex.digamma s) := by
  have hΓeq : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
    funext z; simp [Function.comp, Complex.Gamma_conj]
  have hderiv : deriv Complex.Gamma (conj s) = conj (deriv Complex.Gamma s) := by
    simpa using congrArg conj (congrFun (by rw [← deriv_conj_conj, hΓeq] :
      conj ∘ deriv Complex.Gamma ∘ conj = deriv Complex.Gamma) s)
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, hderiv, Complex.Gamma_conj, map_div₀]
theorem logGamma_im_ofReal {x : ℝ} (hx : 0 < x) :
    (logGamma (x : ℂ)).im = 0 := by
  have hψderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (logGamma (u : ℂ)).im) 0 t := by
    intro t ht
    have htre : 0 < ((t : ℂ)).re := by simpa using ht
    have hc : HasDerivAt (fun u : ℝ ↦ logGamma (u : ℂ)) (Complex.digamma (t : ℂ)) t :=
      (hasDerivAt_logGamma htre).comp_ofReal
    have him : HasDerivAt (fun u : ℝ ↦ Complex.imCLM (logGamma (u : ℂ)))
        (Complex.imCLM (Complex.digamma (t : ℂ))) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hc
    have hreal : (Complex.digamma (t : ℂ)).im = 0 :=
      Complex.conj_eq_iff_im.mp <| by
        simpa [Complex.conj_ofReal] using (digamma_conj (t : ℂ)).symm
    simpa only [Complex.imCLM_apply, hreal] using him
  simpa [Complex.ofReal_one] using isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun u hu ↦ (hψderiv u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hψderiv u hu).deriv) hx (mem_Ioi.mpr one_pos)
theorem logGamma_ofReal {x : ℝ} (hx : 0 < x) :
    logGamma (x : ℂ) = (Real.log (Real.Gamma x) : ℂ) := by
  have hre : Complex.exp (logGamma (x : ℂ)) = (Real.Gamma x : ℂ) := by
    rw [cexp_logGamma (by simpa using hx), Complex.Gamma_ofReal]
  have hreal : logGamma (x : ℂ) = ((logGamma (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [logGamma_im_ofReal hx]
  rw [hreal, ← Complex.ofReal_exp] at hre
  have hlog : (logGamma (x : ℂ)).re = Real.log (Real.Gamma x) := by
    rw [← Complex.ofReal_injective hre, Real.log_exp]
  rw [hreal, hlog]
theorem logGamma_add_one {z : ℂ} (hz : 0 < z.re) :
    logGamma (z + 1) = Complex.log z + logGamma z := by
  set S : Set ℂ := {w : ℂ | 0 < w.re} with hS
  set k : ℂ → ℂ := fun v ↦ logGamma (v + 1) - Complex.log v - logGamma v with hk
  have hopen : IsOpen S := isOpen_re_gt 0
  have hpre : IsPreconnected S := isPreconnected_re_pos
  have hderiv : ∀ w ∈ S, HasDerivAt k 0 w := by
    intro w hw
    have hw' : (0 : ℝ) < w.re := hw
    have hw1 : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
    have hslit : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hw')
    have hd1 : HasDerivAt (fun v : ℂ ↦ logGamma (v + 1)) (Complex.digamma (w + 1)) w := by
      have := (hasDerivAt_logGamma hw1).comp w ((hasDerivAt_id w).add_const 1)
      simpa [Function.comp_def] using this
    have hd2 : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hslit
    have hd3 : HasDerivAt logGamma (Complex.digamma w) w := hasDerivAt_logGamma hw'
    have hval : Complex.digamma (w + 1) - w⁻¹ - Complex.digamma w = 0 := by
      rw [Complex.digamma_apply_add_one w (ne_neg_natCast_of_re_pos hw')]; ring
    have hkd := (hd1.sub hd2).sub hd3
    rwa [hval] at hkd
  have hfderiv : S.EqOn (fderiv ℂ k) 0 :=
    fun w hw ↦ by simpa using (hderiv w hw).hasFDerivAt.fderiv
  have hdiff : DifferentiableOn ℂ k S :=
    fun w hw ↦ (hderiv w hw).differentiableAt.differentiableWithinAt
  have h1mem : (1 : ℂ) ∈ S := by rw [hS]; simp
  have hzmem : z ∈ S := hz
  have hconst := hopen.is_const_of_fderiv_eq_zero hpre hdiff hfderiv hzmem h1mem
  have hk1 : k 1 = 0 := by
    simp only [hk, Complex.log_one, logGamma_one, sub_zero]
    rw [show (1 : ℂ) + 1 = ((2 : ℝ) : ℂ) by norm_num, logGamma_ofReal (by norm_num),
      Real.Gamma_two, Real.log_one, Complex.ofReal_zero]
  rw [hk1] at hconst
  simp only [hk] at hconst
  linear_combination hconst
theorem logGamma_eq_sub_sum_log_add {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    logGamma w
      = logGamma (w + N) - ∑ j ∈ Finset.range N, Complex.log (w + j) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hwn : 0 < (w + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hstep : logGamma (w + ((n + 1 : ℕ) : ℂ))
        = Complex.log (w + n) + logGamma (w + n) := by
      rw [show w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 by push_cast; ring,
        logGamma_add_one hwn]
    rw [Finset.sum_range_succ, hstep, ih]
    ring
end Complex
end
end CertificatePort80
section CertificatePort81
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open MeasureTheory Filter
open scoped Topology Nat Real
namespace Complex.Stirling
noncomputable def logGammaStirling (M : ℕ) (w : ℂ) : ℂ :=
  (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ)
    + ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ))
theorem hasDerivAt_logGammaStirling {M : ℕ} {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (logGammaStirling M)
      (Complex.log w - (2 * w)⁻¹
        - ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * w ^ (-(2 * k : ℤ))) w := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hwslit : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hw)
  have hlog : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hwslit
  have hid : HasDerivAt (fun z : ℂ ↦ z - 1 / 2) 1 w := (hasDerivAt_id w).sub_const _
  have hT1 : HasDerivAt (fun z : ℂ ↦ (z - 1 / 2) * Complex.log z)
      (1 * Complex.log w + (w - 1 / 2) * w⁻¹) w := hid.mul hlog
  have hsum : HasDerivAt
      (fun z : ℂ ↦ ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * z ^ (1 - 2 * (k : ℤ)))
      (∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1))
          * ((1 - 2 * (k : ℤ) : ℤ) * w ^ ((1 - 2 * (k : ℤ)) - 1))) w := by
    apply HasDerivAt.fun_sum
    intro k _
    exact (hasDerivAt_zpow (1 - 2 * (k : ℤ)) w (Or.inl hw0)).const_mul
      ((bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)))
  have hderiv := ((hT1.sub (hasDerivAt_id w)).add_const
      ((1 / 2 : ℂ) * (Real.log (2 * π) : ℂ))).add hsum
  refine hderiv.congr_deriv ?_
  have hscal : 1 * Complex.log w + (w - 1 / 2) * w⁻¹ - 1 = Complex.log w - (2 * w)⁻¹ := by
    field_simp
    ring
  have hsumeq : (∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1))
          * ((1 - 2 * (k : ℤ) : ℤ) * w ^ ((1 - 2 * (k : ℤ)) - 1)))
      = -∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * w ^ (-(2 * k : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hk2 : 2 * (k : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show 2 * k ≠ 1 by lia))
    rw [show (1 - 2 * (k : ℤ)) - 1 = -(2 * k : ℤ) by ring]
    push_cast
    field_simp
    ring
  rw [hscal, hsumeq]
  ring
noncomputable def logGammaRemainderIoi (M : ℕ) (w : ℂ) : ℂ :=
  ∫ τ in Set.Ioi (0 : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1)
private theorem rpow_neg_natCast_eq_zpow (x : ℝ) (n : ℕ) :
    x ^ (-(n : ℝ)) = x ^ (-(n : ℤ)) := by
  rw [show (-(n : ℝ)) = ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
private theorem integral_Ioi_add_rpow_of_lt {a σ : ℝ} (ha : a < -1) (hσ : 0 < σ) :
    ∫ τ in Set.Ioi (0 : ℝ), (τ + σ) ^ a = -σ ^ (a + 1) / (a + 1) := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ ↦ (t + σ) ^ (a + 1) / (a + 1)) ((x + σ) ^ a) x := by
    intro x hx
    have hxσ : (0 : ℝ) < x + σ := by linarith [Set.mem_Ici.mp hx]
    have ha1 : a + 1 ≠ 0 := by linarith
    have h := (((hasDerivAt_id x).add_const σ).rpow_const (p := a + 1)
      (Or.inl hxσ.ne')).div_const (a + 1)
    have hval : (1 : ℝ) * (a + 1) * (id x + σ) ^ (a + 1 - 1) / (a + 1) = (x + σ) ^ a := by
      rw [id_eq, show a + 1 - 1 = a by ring]
      field_simp
    rwa [hval] at h
  have hint : IntegrableOn (fun τ : ℝ ↦ (τ + σ) ^ a) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt ha (by linarith)
  have ht : Tendsto (fun t : ℝ ↦ (t + σ) ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ σ tendsto_id) |>.div_const _
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht using 1
  simp [neg_div]
noncomputable abbrev logGammaRemainderBound (M : ℕ) (w : ℂ) : ℝ :=
  ((2 * M + 1)! : ℝ) / (2 * M * (2 * π) ^ (2 * M)) * w.re ^ (-(2 * M : ℤ))
noncomputable abbrev logGammaRemainderNormBound (M : ℕ) (w : ℂ) : ℝ :=
  ((2 * M + 1)! : ℝ) * 2 ^ (2 * M + 1) / (2 * M * (2 * π) ^ (2 * M)) * ‖w‖ ^ (-(2 * M : ℤ))
private theorem norm_logGammaRemainderIoi_le_of_div_le {M : ℕ} (hM : 1 ≤ M) {w : ℂ}
    (hw : 0 < w.re) {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hle : ∀ τ ∈ Set.Ioi (0 : ℝ), (τ + σ) / κ ≤ ‖w + (τ : ℂ)‖) :
    ‖logGammaRemainderIoi M w‖
      ≤ ((2 * M + 1)! : ℝ) * κ ^ (2 * M + 1) / (2 * M * (2 * π) ^ (2 * M))
          * σ ^ (-(2 * M : ℤ)) := by
  set p : ℕ := 2 * M + 1 with hp
  have hp2 : 2 ≤ p := by lia
  have hp1 : p - 1 = 2 * M := by lia
  set C : ℝ := (p ! : ℝ) / (2 * π) ^ (p - 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hpR : (-(p : ℝ)) < -1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  set g : ℝ → ℝ := fun τ ↦ C * κ ^ p * (τ + σ) ^ (-(p : ℝ)) with hgdef
  have hgint : IntegrableOn g (Set.Ioi 0) :=
    (integrableOn_add_rpow_Ioi_of_lt hpR (by linarith)).const_mul (C * κ ^ p)
  have hbound : ∀ τ ∈ Set.Ioi (0 : ℝ),
      ‖digammaRemainderIoi (w + (τ : ℂ)) p‖ ≤ g τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have hre : 0 < (w + (τ : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
    have hnpos : 0 < (τ + σ) / κ := by positivity
    have h1 := norm_digammaRemainderIoi_le' (w + (τ : ℂ)) hre p (by lia)
    rw [← hCdef] at h1
    have hmono : ‖w + (τ : ℂ)‖ ^ (-(p : ℝ)) ≤ ((τ + σ) / κ) ^ (-(p : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hnpos (hle τ hτ) (neg_nonpos.mpr (by positivity))
    have hdiv : ((τ + σ) / κ) ^ (-(p : ℝ)) = κ ^ p * (τ + σ) ^ (-(p : ℝ)) := by
      rw [Real.div_rpow (by positivity) hκ.le, Real.rpow_neg hκ.le, Real.rpow_natCast,
        div_eq_mul_inv, inv_inv, mul_comm]
    calc ‖digammaRemainderIoi (w + (τ : ℂ)) p‖
        ≤ C * ‖w + (τ : ℂ)‖ ^ (-(p : ℤ)) := h1
      _ = C * ‖w + (τ : ℂ)‖ ^ (-(p : ℝ)) := by rw [← rpow_neg_natCast_eq_zpow]
      _ ≤ C * (κ ^ p * (τ + σ) ^ (-(p : ℝ))) :=
          mul_le_mul_of_nonneg_left (hdiv ▸ hmono) hC0
      _ = g τ := by simp only [hgdef]; ring
  calc ‖logGammaRemainderIoi M w‖
      ≤ ∫ τ in Set.Ioi (0 : ℝ), g τ := by
        rw [logGammaRemainderIoi, ← hp]
        refine norm_integral_le_of_norm_le hgint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ using hbound τ hτ
    _ = C * κ ^ p * (σ ^ (-(2 * M : ℤ)) / (2 * (M : ℝ))) := by
        rw [hgdef, integral_const_mul, integral_Ioi_add_rpow_of_lt hpR hσ,
          show (-(p : ℝ)) + 1 = -(2 * (M : ℝ)) by rw [hp]; push_cast; ring,
          show σ ^ (-(2 * (M : ℝ))) = σ ^ (-(2 * M : ℤ)) by
            rw [show (-(2 * (M : ℝ))) = ((-(2 * M : ℤ) : ℤ) : ℝ) by push_cast; ring,
              Real.rpow_intCast],
          neg_div_neg_eq]
    _ = _ := by rw [hCdef, hp1, hp]; ring
theorem norm_logGammaRemainderIoi_le {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    ‖logGammaRemainderIoi M w‖ ≤ logGammaRemainderBound M w := by
  refine (norm_logGammaRemainderIoi_le_of_div_le hM hw hw zero_lt_one fun τ hτ ↦ ?_).trans_eq ?_
  · rw [div_one]
    have hτ0 : (0 : ℝ) < τ := hτ
    have := Complex.re_le_norm (w + (τ : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  · simp [logGammaRemainderBound]
theorem norm_logGammaRemainderIoi_le' {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    ‖logGammaRemainderIoi M w‖ ≤ logGammaRemainderNormBound M w := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hw)
  refine norm_logGammaRemainderIoi_le_of_div_le hM hw hw0 two_pos fun τ hτ ↦ ?_
  have hτ0 : (0 : ℝ) < τ := hτ
  have h1 : ‖w‖ ≤ ‖w + (τ : ℂ)‖ := by
    have hsq : ‖w‖ ^ 2 ≤ ‖w + (τ : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
      nlinarith
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
  have h2 : τ ≤ ‖w + (τ : ℂ)‖ := by
    have := Complex.re_le_norm (w + (τ : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  linarith
theorem logGammaStirling_two (w : ℂ) :
    logGammaStirling 2 w
      = (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ)
        + 1 / 12 * w⁻¹ - 1 / 360 * (w ^ 3)⁻¹ := by
  have hb2 : ((bernoulli 2 : ℚ) : ℂ) = 1 / 6 := by rw [bernoulli_two]; norm_num
  have hb4 : ((bernoulli 4 : ℚ) : ℂ) = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]; norm_num
  rw [logGammaStirling, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  rw [show ((1 : ℤ) - 2 * ((1 : ℕ) : ℤ)) = -1 by norm_num,
    show ((1 : ℤ) - 2 * ((2 : ℕ) : ℤ)) = -(3 : ℕ) by norm_num,
    zpow_neg_one, zpow_neg, zpow_natCast, hb2, hb4]
  push_cast
  ring
end Complex.Stirling
namespace Real.Stirling
noncomputable def stirlingRef (x : ℝ) : ℝ :=
  (x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)
private theorem hasDerivAt_stirlingRef {x : ℝ} (hx : 0 < x) :
    HasDerivAt stirlingRef (Real.log x - 1 / (2 * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ (y - 1 / 2) * Real.log y)
      (1 * Real.log x + (x - 1 / 2) * x⁻¹) x :=
    ((hasDerivAt_id' (x := x)).sub_const (1 / 2)).mul (Real.hasDerivAt_log hx.ne')
  have h2 : HasDerivAt stirlingRef ((1 * Real.log x + (x - 1 / 2) * x⁻¹) - 1) x :=
    (h1.sub (hasDerivAt_id' (x := x))).add_const (1 / 2 * Real.log (2 * π))
  rwa [show (1 * Real.log x + (x - 1 / 2) * x⁻¹) - 1 = Real.log x - 1 / (2 * x) by
    field_simp; ring] at h2
private noncomputable def stirlingAnchorBound (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) - 1) + 1 / (2 * (n : ℝ))
private theorem tendsto_stirlingAnchorBound :
    Tendsto (fun n : ℕ ↦ stirlingAnchorBound n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) - 1))
      atTop (𝓝 0) := by
    have hratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ ↦ 2 / ((n : ℝ) - 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right atTop (-1) tendsto_natCast_atTop_atTop)
      have h3 : Tendsto (fun n : ℕ ↦ 1 + 2 / ((n : ℝ) - 1)) atTop (𝓝 1) := by
        simpa using h2.const_add 1
      refine h3.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hle : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn1 : ((n : ℝ) - 1) ≠ 0 := by
        intro h; rw [sub_eq_zero] at h; linarith
      field_simp
      ring
    have hc := (Real.continuousAt_log (one_ne_zero)).tendsto.comp hratio
    rw [Real.log_one] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hle : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) - 1) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
    rw [Function.comp_apply, Real.log_div h1 h2]
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (2 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop' (by norm_num) tendsto_natCast_atTop_atTop)
  simpa [stirlingAnchorBound] using hlog.add hinv
private theorem tendsto_log_Gamma_sub_stirlingRef_nat :
    Tendsto (fun n : ℕ ↦ Real.log (Real.Gamma (n : ℝ)) - stirlingRef (n : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n) - Real.log π / 2)
      atTop (𝓝 0) := by
    have hcont : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n))
        atTop (𝓝 (Real.log π / 2)) := by
      have h := (Real.continuousAt_log (x := √π) (by positivity)).tendsto.comp
        Stirling.tendsto_stirlingSeq_sqrt_pi
      rwa [Function.comp_def, Real.log_sqrt Real.pi_pos.le] at h
    simpa using hcont.sub_const (Real.log π / 2)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
  have hΓpos : 0 < Real.Gamma (n : ℝ) :=
    Real.Gamma_pos_of_pos (by exact_mod_cast (show 0 < n by lia))
  have hfact : (n : ℝ) * Real.Gamma (n : ℝ) = (n ! : ℝ) := by
    rw [← Real.Gamma_add_one hn0]; exact_mod_cast Real.Gamma_nat_eq_factorial n
  have e1 : Real.log (Real.Gamma (n : ℝ)) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
    have h := congrArg Real.log hfact
    rw [Real.log_mul hn0 hΓpos.ne'] at h
    linarith
  rw [Stirling.log_stirlingSeq_formula, e1, stirlingRef,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
    Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring
private theorem abs_log_Gamma_sub_stirlingRef_le {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (Real.Gamma x) - stirlingRef x|
      ≤ |Real.log (Real.Gamma (⌊x⌋₊ : ℝ)) - stirlingRef (⌊x⌋₊ : ℝ)| + stirlingAnchorBound ⌊x⌋₊ := by
  set n := ⌊x⌋₊
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_floor (by exact_mod_cast hx : ((2 : ℕ) : ℝ) ≤ x)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hax : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxa1 : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlogmono : Real.log ((n : ℝ) - 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hnm1pos (by linarith)
  have hbnd_nonneg : 0 ≤ stirlingAnchorBound n := by
    have : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := by positivity
    simp only [stirlingAnchorBound]; linarith
  have hf1 : Real.log (Real.Gamma ((n : ℝ) + 1))
      = Real.log (n : ℝ) + Real.log (Real.Gamma (n : ℝ)) := by
    rw [Real.Gamma_add_one hnpos.ne', Real.log_mul hnpos.ne' (Real.Gamma_pos_of_pos hnpos).ne']
  have hnum : Real.log (Real.Gamma (n : ℝ)) - Real.log (Real.Gamma ((n : ℝ) - 1))
      = Real.log ((n : ℝ) - 1) := by
    have h := Real.Gamma_add_one (s := (n : ℝ) - 1) hnm1pos.ne'
    rw [show (n : ℝ) - 1 + 1 = (n : ℝ) by ring] at h
    rw [h, Real.log_mul hnm1pos.ne' (Real.Gamma_pos_of_pos hnm1pos).ne']; ring
  rw [← sub_le_iff_le_add']
  refine (abs_sub_abs_le_abs_sub _ _).trans ?_
  rcases hax.lt_or_eq with hlt | heq
  ·
    have hd0 : (0 : ℝ) < x - (n : ℝ) := by linarith
    have hup := Real.convexOn_log_Gamma.secant_mono_aux2 hnpos
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < (n : ℝ) + 1)) hlt hxa1
    simp only [Function.comp_apply] at hup
    rw [hf1, show (n : ℝ) + 1 - (n : ℝ) = 1 by ring, div_one, add_sub_cancel_right] at hup
    have hup' := (div_le_iff₀ hd0).mp hup
    have hlo := Real.convexOn_log_Gamma.slope_mono_adjacent hnm1pos
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < x)) (by linarith) hlt
    simp only [Function.comp_apply] at hlo
    rw [show (n : ℝ) - ((n : ℝ) - 1) = 1 by ring, div_one, hnum] at hlo
    have hlo' := (le_div_iff₀ hd0).mp hlo
    have hcont : ContinuousOn stirlingRef (Set.Icc (n : ℝ) x) := fun t ht ↦
      (hasDerivAt_stirlingRef (by have := ht.1; linarith)).continuousAt.continuousWithinAt
    obtain ⟨ξ, ⟨hξlo, hξhi⟩, hξeq⟩ := exists_hasDerivAt_eq_slope stirlingRef
      (fun t ↦ Real.log t - 1 / (2 * t)) hlt hcont
      (fun t ht ↦ hasDerivAt_stirlingRef (by have := ht.1; linarith))
    have hξpos : 0 < ξ := by linarith
    have hQ : stirlingRef x - stirlingRef (n : ℝ)
        = (Real.log ξ - 1 / (2 * ξ)) * (x - (n : ℝ)) := by
      rw [hξeq, div_mul_cancel₀ _ hd0.ne']
    have hlogξlo : Real.log (n : ℝ) ≤ Real.log ξ := Real.log_le_log hnpos hξlo.le
    have hlogξhi : Real.log ξ ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hξpos (by linarith)
    have hinvξ : 1 / (2 * ξ) ≤ 1 / (2 * (n : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hinvξ0 : (0 : ℝ) ≤ 1 / (2 * ξ) := by positivity
    have hQlo : (Real.log (n : ℝ) - 1 / (2 * (n : ℝ))) * (x - (n : ℝ))
        ≤ stirlingRef x - stirlingRef (n : ℝ) := by
      rw [hQ]; exact mul_le_mul_of_nonneg_right (by linarith) hd0.le
    have hQhi : stirlingRef x - stirlingRef (n : ℝ)
        ≤ Real.log ((n : ℝ) + 1) * (x - (n : ℝ)) := by
      rw [hQ]; exact mul_le_mul_of_nonneg_right (by linarith) hd0.le
    rw [abs_le, stirlingAnchorBound]
    refine ⟨?_, ?_⟩
    · nlinarith [hlo', hQhi, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (x - (n : ℝ)))
        (by linarith : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) - 1))]
    · nlinarith [hup', hQlo, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (x - (n : ℝ)))
        (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)))]
  · rw [heq]; simpa using hbnd_nonneg
theorem tendsto_log_Gamma_sub_stirlingRef_atTop :
    Tendsto (fun x : ℝ ↦ Real.log (Real.Gamma x) - stirlingRef x) atTop (𝓝 0) := by
  set M : ℕ → ℝ := fun n ↦
    |Real.log (Real.Gamma (n : ℝ)) - stirlingRef (n : ℝ)| + stirlingAnchorBound n with hM
  have hMlim : Tendsto M atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ |Real.log (Real.Gamma (n : ℝ)) - stirlingRef (n : ℝ)|)
        atTop (𝓝 0) := by
      simpa [Real.norm_eq_abs] using tendsto_log_Gamma_sub_stirlingRef_nat.norm
    simpa [hM] using h1.add tendsto_stirlingAnchorBound
  have hbnd : ∀ᶠ x : ℝ in atTop,
      ‖Real.log (Real.Gamma x) - stirlingRef x‖ ≤ M ⌊x⌋₊ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [Real.norm_eq_abs, hM]
    exact abs_log_Gamma_sub_stirlingRef_le hx
  exact squeeze_zero_norm' hbnd (hMlim.comp tendsto_nat_floor_atTop)
end Real.Stirling
end
end CertificatePort81
section CertificatePort82
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open MeasureTheory Filter
open scoped Topology Nat Real
namespace Complex.Stirling
private theorem digammaRemainderIoi_eq {M : ℕ} {z : ℂ} (hz : 0 < z.re) :
    digammaRemainderIoi z (2 * M + 1)
      = (Complex.log z - (2 * z)⁻¹
          - ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * z ^ (-(2 * k : ℤ)))
        - Complex.digamma z := by
  rw [digamma_eq_log_sub z hz M]; ring
private theorem hasDerivAt_logGamma_sub_logGammaStirling {M : ℕ} {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun s ↦ logGamma s - logGammaStirling M s)
      (-(digammaRemainderIoi z (2 * M + 1))) z := by
  have h := (hasDerivAt_logGamma hz).sub (hasDerivAt_logGammaStirling (M := M) hz)
  rwa [show -(digammaRemainderIoi z (2 * M + 1))
      = Complex.digamma z - (Complex.log z - (2 * z)⁻¹
        - ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * z ^ (-(2 * k : ℤ)))
      by rw [digamma_eq_log_sub z hz M]; ring]
private theorem hasDerivAt_logGamma_sub_logGammaStirling_comp {M : ℕ} {ψ : ℂ → ℂ}
    {c : ℂ} {t : ℝ} (hψ : HasDerivAt ψ c (t : ℂ)) (ht : 0 < (ψ (t : ℂ)).re) :
    HasDerivAt (fun s : ℝ ↦ logGamma (ψ (s : ℂ)) - logGammaStirling M (ψ (s : ℂ)))
      (-(digammaRemainderIoi (ψ (t : ℂ)) (2 * M + 1)) * c) t := by
  simpa [Function.comp_def] using
    ((hasDerivAt_logGamma_sub_logGammaStirling (M := M) ht).comp (t : ℂ) hψ).comp_ofReal
private theorem continuousAt_digammaRemainderIoi_comp {M : ℕ} {f : ℝ → ℂ} {t : ℝ}
    (hf : ContinuousAt f t) (ht : 0 < (f t).re) :
    ContinuousAt (fun s : ℝ ↦ digammaRemainderIoi (f s) (2 * M + 1)) t := by
  have hmem : {s : ℝ | 0 < (f s).re} ∈ nhds t :=
    hf.preimage_mem_nhds ((isOpen_re_gt 0).mem_nhds ht)
  have hslit : f t ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl ht)
  have hne : f t ≠ 0 := Complex.ne_zero_of_re_pos ht
  have c1 : ContinuousAt (fun s ↦ Complex.log (f s)) t := (continuousAt_clog hslit).comp hf
  have c2 : ContinuousAt (fun s ↦ (2 * f s)⁻¹) t :=
    (continuousAt_const.mul hf).inv₀ (by simp [hne])
  have c3 : ContinuousAt
      (fun s ↦ ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * (f s) ^ (-(2 * k : ℤ)))
      t :=
    tendsto_finsetSum _ fun k _ ↦ (hf.zpow₀ (-(2 * (k : ℤ))) (Or.inl hne)).const_mul _
  have c4 : ContinuousAt (fun s ↦ Complex.digamma (f s)) t := (continuousAt_digamma ht).comp hf
  refine (((c1.sub c2).sub c3).sub c4).congr ?_
  filter_upwards [hmem] with s hs using (digammaRemainderIoi_eq hs).symm
private theorem norm_digammaRemainderIoi_le_re {M : ℕ} (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖digammaRemainderIoi s (2 * M + 1)‖
      ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) * s.re ^ (-(2 * M + 1 : ℝ)) := by
  have h1 := norm_digammaRemainderIoi_le' s hs (2 * M + 1) (by lia)
  have hge : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hzr : ‖s‖ ^ (-(2 * M + 1 : ℤ)) = ‖s‖ ^ (-(2 * M + 1 : ℝ)) := by
    rw [show (-(2 * M + 1 : ℝ)) = ((-(2 * M + 1 : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]
  have hmono : ‖s‖ ^ (-(2 * M + 1 : ℝ)) ≤ s.re ^ (-(2 * M + 1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs hge (neg_nonpos.mpr (by positivity))
  have hCpos : (0 : ℝ) ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) := by positivity
  calc ‖digammaRemainderIoi s (2 * M + 1)‖
      ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ ((2 * M + 1) - 1) * ‖s‖ ^ (-(2 * M + 1 : ℤ)) := h1
    _ = ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) * ‖s‖ ^ (-(2 * M + 1 : ℝ)) := by
        rw [hzr, show (2 * M + 1) - 1 = 2 * M by lia]
    _ ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) * s.re ^ (-(2 * M + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono hCpos
private theorem integrableOn_digammaRemainderIoi_shift {M : ℕ} (hM : 1 ≤ M) {w : ℂ}
    (hw : 0 < w.re) :
    IntegrableOn (fun τ : ℝ ↦ digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1)) (Set.Ioi 0) := by
  set C : ℝ := ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M)
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hre : ∀ {τ : ℝ}, 0 < τ → 0 < (w + (τ : ℂ)).re := fun {τ} hτ ↦ by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hmaj : IntegrableOn (fun τ : ℝ ↦ C * (τ + w.re) ^ (-(2 * M + 1 : ℝ))) (Set.Ioi 0) :=
    (integrableOn_add_rpow_Ioi_of_lt (show (-(2 * M + 1 : ℝ)) < -1 by linarith)
      (show -w.re < 0 by linarith)).const_mul C
  have hmeas : AEStronglyMeasurable
      (fun τ : ℝ ↦ digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
      (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro τ hτ
    exact (continuousAt_digammaRemainderIoi_comp
      (Complex.continuous_ofReal.const_add w).continuousAt (hre hτ)).continuousWithinAt
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hb := norm_digammaRemainderIoi_le_re hM (hre hτ)
  rwa [show (w + (τ : ℂ)).re = τ + w.re by
    simp only [Complex.add_re, Complex.ofReal_re]; ring] at hb
private theorem logGamma_sub_logGammaStirling_shift_eq_integral {M : ℕ} (hM : 1 ≤ M)
    {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (logGamma w - logGammaStirling M w)
        - (logGamma (w + n) - logGammaStirling M (w + n))
      = ∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1) := by
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) (n : ℝ),
      HasDerivAt (fun t : ℝ ↦ logGamma (w + (t : ℂ)) - logGammaStirling M (w + (t : ℂ)))
        (-(digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))) τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) ≤ τ := by
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ))] at hτ; exact hτ.1
    have hre : 0 < (w + (τ : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    simpa using
      hasDerivAt_logGamma_sub_logGammaStirling_comp ((hasDerivAt_id (τ : ℂ)).const_add w) hre
  have hint : IntervalIntegrable
      (fun τ : ℝ ↦ -(digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))) volume 0 (n : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact ((integrableOn_digammaRemainderIoi_shift hM hw).mono_set Set.Ioc_subset_Ioi_self).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [Complex.ofReal_natCast, Complex.ofReal_zero, add_zero] at hFTC
  linear_combination hFTC
private theorem tendsto_bernoulli_tail {M : ℕ} :
    Tendsto (fun x : ℝ ↦ ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)) * x ^ (1 - 2 * (k : ℤ))) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ k ∈ Finset.Icc 1 M, (0 : ℝ) by simp]
  apply tendsto_finsetSum
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hlt : (1 - 2 * (k : ℤ)) < 0 := by lia
  simpa using (tendsto_zpow_atTop_zero hlt).const_mul
    ((bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)))
private theorem logGammaStirling_ofReal {M : ℕ} {x : ℝ} (hx : 0 < x) :
    logGammaStirling M (x : ℂ)
      = ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)
          + ∑ k ∈ Finset.Icc 1 M,
              (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)) * x ^ (1 - 2 * (k : ℤ)) : ℂ) := by
  rw [logGammaStirling]
  push_cast [Complex.ofReal_log hx.le, Complex.ofReal_zpow]
  ring
private theorem tendsto_g_ofReal_atTop {M : ℕ} :
    Tendsto (fun x : ℝ ↦ logGamma (x : ℂ) - logGammaStirling M (x : ℂ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ ↦ Real.log (Real.Gamma x)
      - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π))
      - ∑ k ∈ Finset.Icc 1 M,
          (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)) * x ^ (1 - 2 * (k : ℤ)))
      atTop (𝓝 0) := by
    simpa [Real.Stirling.stirlingRef] using
      Real.Stirling.tendsto_log_Gamma_sub_stirlingRef_atTop.sub tendsto_bernoulli_tail
  refine (hreal.ofReal).congr' ?_ |>.mono_right (by simp)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [logGamma_ofReal hx, logGammaStirling_ofReal hx]
  push_cast
  ring
private theorem tendsto_g_shift_atTop {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun n : ℕ ↦ logGamma (w + n) - logGammaStirling M (w + n)) atTop (𝓝 0) := by
  set C : ℝ := ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M)
  have hbn : Tendsto (fun n : ℕ ↦ C * (w.re + (n : ℝ)) ^ (-(2 * M + 1 : ℤ)) * |w.im|)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (w.re + (n : ℝ)) ^ (-(2 * M + 1 : ℤ))) atTop (𝓝 0) :=
      (tendsto_zpow_atTop_zero (show (-(2 * M + 1 : ℤ)) < 0 by lia)).comp
        (tendsto_atTop_add_const_left atTop w.re tendsto_natCast_atTop_atTop)
    simpa using (h1.const_mul C).mul_const |w.im|
  have hreal : Tendsto (fun n : ℕ ↦
      logGamma ((w.re + (n : ℝ) : ℝ) : ℂ) - logGammaStirling M ((w.re + (n : ℝ) : ℝ) : ℂ))
      atTop (𝓝 0) :=
    tendsto_g_ofReal_atTop.comp
      (tendsto_atTop_add_const_left atTop w.re tendsto_natCast_atTop_atTop)
  have htrans : Tendsto (fun n : ℕ ↦
      (logGamma (w + n) - logGammaStirling M (w + n))
        - (logGamma ((w.re + (n : ℝ) : ℝ) : ℂ)
          - logGammaStirling M ((w.re + (n : ℝ) : ℝ) : ℂ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm ?_ hbn
    intro n
    set b : ℝ := w.re + (n : ℝ) with hb
    have hbpos : 0 < b := by rw [hb]; positivity
    have hre_eq : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I).re = b := fun y ↦ by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    have hre : ∀ y : ℝ, 0 < ((b : ℂ) + (y : ℂ) * Complex.I).re := fun y ↦ by
      rw [hre_eq y]; exact hbpos
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) w.im,
        HasDerivAt (fun t : ℝ ↦ logGamma ((b : ℂ) + (t : ℂ) * Complex.I)
            - logGammaStirling M ((b : ℂ) + (t : ℂ) * Complex.I))
          (-(digammaRemainderIoi ((b : ℂ) + (y : ℂ) * Complex.I) (2 * M + 1)) * Complex.I) y := by
      intro y _
      have haff : HasDerivAt (fun z : ℂ ↦ (b : ℂ) + z * Complex.I) Complex.I (y : ℂ) := by
        simpa using ((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (b : ℂ)
      simpa using hasDerivAt_logGamma_sub_logGammaStirling_comp haff (hre y)
    have hcont : Continuous (fun y : ℝ ↦
        -(digammaRemainderIoi ((b : ℂ) + (y : ℂ) * Complex.I) (2 * M + 1)) * Complex.I) := by
      rw [continuous_iff_continuousAt]
      intro y
      exact ((continuousAt_digammaRemainderIoi_comp
        ((Complex.continuous_ofReal.mul continuous_const).const_add (b : ℂ)).continuousAt
        (hre y)).neg).mul continuousAt_const
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
    have hend1 : (b : ℂ) + (w.im : ℂ) * Complex.I = w + n := by
      rw [hb]; push_cast; linear_combination Complex.re_add_im w
    have hend0 : (b : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = ((w.re + (n : ℝ) : ℝ) : ℂ) := by
      rw [hb]; push_cast; ring
    rw [hend1, hend0] at hFTC
    rw [← hFTC, show |w.im| = |w.im - 0| by rw [sub_zero]]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y _
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    have hbnd := norm_digammaRemainderIoi_le_re hM (hre y)
    have hbz : b ^ (-(2 * M + 1 : ℝ)) = b ^ (-(2 * M + 1 : ℤ)) := by
      rw [show (-(2 * M + 1 : ℝ)) = ((-(2 * M + 1 : ℤ) : ℤ) : ℝ) by push_cast; ring,
        Real.rpow_intCast]
    rw [hre_eq y, hbz] at hbnd
    exact hbnd
  simpa using htrans.add hreal
theorem logGamma_eq_stirling_add_remainder {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    logGamma w = logGammaStirling M w + logGammaRemainderIoi M w := by
  have hconst : ∀ n : ℕ,
      logGamma w - logGammaStirling M w
        = (∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
          + (logGamma (w + n) - logGammaStirling M (w + n)) := by
    intro n
    have h := logGamma_sub_logGammaStirling_shift_eq_integral hM hw n
    linear_combination h
  have htend1 : Tendsto
      (fun n : ℕ ↦ ∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
      atTop (𝓝 (logGammaRemainderIoi M w)) := by
    have h := intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_digammaRemainderIoi_shift hM hw) tendsto_natCast_atTop_atTop
    rwa [logGammaRemainderIoi]
  have htend : Tendsto
      (fun n : ℕ ↦ (∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
          + (logGamma (w + n) - logGammaStirling M (w + n)))
      atTop (𝓝 (logGammaRemainderIoi M w + 0)) := htend1.add (tendsto_g_shift_atTop hM hw)
  have hlim : Tendsto (fun _ : ℕ ↦ logGamma w - logGammaStirling M w) atTop
      (𝓝 (logGammaRemainderIoi M w + 0)) := htend.congr fun n ↦ (hconst n).symm
  have hEq : logGamma w - logGammaStirling M w = logGammaRemainderIoi M w + 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  rw [add_zero] at hEq
  linear_combination hEq
end Complex.Stirling
end
end CertificatePort82
section CertificatePort83
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex
open scoped Nat
noncomputable def hardyZ (t : ℝ) : ℝ :=
  (Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) * riemannZeta (1 / 2 + Complex.I * t)).re
theorem continuous_logGamma_curve :
    Continuous fun u : ℝ ↦ logGamma (1 / 4 + Complex.I * ((u : ℂ) / 2)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hre : (0 : ℝ) < (1 / 4 + Complex.I * ((u : ℂ) / 2)).re := by simp
  exact ContinuousAt.comp (f := fun u : ℝ => (1 / 4 : ℂ) + Complex.I * ((u : ℂ) / 2))
    (hasDerivAt_logGamma hre).continuousAt (by fun_prop)
theorem riemannSiegelTheta_eq_im_logGamma {T : ℝ} (hT : 0 ≤ T) :
    riemannSiegelTheta T
      = (logGamma (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi := by
  have hre : ∀ u : ℝ, (0 : ℝ) < (1 / 4 + Complex.I * ((u : ℂ) / 2)).re := fun u => by simp
  have hcontlog : IsContLog 0 T (fun u => Complex.Gamma (1 / 4 + Complex.I * (u / 2)))
      (fun u ↦ logGamma (1 / 4 + Complex.I * (u / 2))) :=
    ⟨continuous_logGamma_curve.continuousOn, fun u _ ↦ cexp_logGamma (hre u)⟩
  rw [riemannSiegelTheta, argVariation_eq_of_isContLog hT hcontlog]
  have hg0 : (logGamma (1 / 4 + Complex.I * (((0 : ℝ) : ℂ) / 2))).im = 0 := by
    rw [show (1 : ℂ) / 4 + Complex.I * (((0 : ℝ) : ℂ) / 2) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
    exact logGamma_im_ofReal (by norm_num)
  simp only [hg0, sub_zero]
namespace Complex
theorem Gammaℝ_half_add_mul_I_eq_exp (t : ℝ) :
    Gammaℝ (1 / 2 + I * t)
      = exp (logGamma (1 / 4 + I * ((t : ℂ) / 2))
          - (1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)) := by
  have hwre : (0 : ℝ) < (1 / 4 + I * ((t : ℂ) / 2)).re := by simp
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsw2 : (1 / 2 + I * (t : ℂ)) / 2 = 1 / 4 + I * ((t : ℂ) / 2) := by ring
  have hΓw : Gamma ((1 / 2 + I * (t : ℂ)) / 2) = exp (logGamma (1 / 4 + I * ((t : ℂ) / 2))) := by
    rw [hsw2]
    exact (cexp_logGamma hwre).symm
  have hcpow : (Real.pi : ℂ) ^ (-(1 / 2 + I * (t : ℂ)) / 2)
      = exp (-(1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)) := by
    rw [cpow_def_of_ne_zero hpi]
    congr 1
    rw [show log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) from (ofReal_log Real.pi_pos.le).symm,
      show (-(1 / 2 + I * (t : ℂ)) / 2 : ℂ) = -((1 / 2 + I * (t : ℂ)) / 2) from by ring, hsw2]
    ring
  rw [Gammaℝ_def, hcpow, hΓw, ← exp_add]
  congr 1
  ring
theorem chi_half_add_mul_I {t : ℝ} (ht : 0 ≤ t) :
    chi (1 / 2 + I * t) = exp (-(2 * (riemannSiegelTheta t : ℂ)) * I) := by
  have hone_sub : (1 : ℂ) - (1 / 2 + I * (t : ℂ)) = starRingEnd ℂ (1 / 2 + I * (t : ℂ)) := by
    simp only [map_add, map_mul, conj_I, conj_ofReal, map_div₀, map_one, map_ofNat]
    ring
  have hLim : (logGamma (1 / 4 + I * ((t : ℂ) / 2))
      - (1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)).im = riemannSiegelTheta t := by
    have himeq : ((1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)).im
        = t / 2 * Real.log Real.pi := by
      rw [mul_im]; simp
    rw [sub_im, himeq]
    exact (riemannSiegelTheta_eq_im_logGamma ht).symm
  have hconjsub : ∀ z : ℂ, starRingEnd ℂ z - z = -(2 * (z.im : ℂ)) * I := fun z ↦ by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [chi, hone_sub, Gammaℝ_conj, Gammaℝ_half_add_mul_I_eq_exp t, ← exp_conj, ← exp_sub,
    hconjsub, hLim]
end Complex
theorem continuousOn_hardyZ : ContinuousOn hardyZ (Set.Ici (0 : ℝ)) := by
  have hlog : Continuous fun t : ℝ =>
      (logGamma (1 / 4 + Complex.I * ((t : ℂ) / 2))).im - t / 2 * Real.log Real.pi :=
    (Complex.continuous_im.comp continuous_logGamma_curve).sub (by fun_prop)
  have hθ : ContinuousOn riemannSiegelTheta (Set.Ici 0) :=
    hlog.continuousOn.congr fun t ht => riemannSiegelTheta_eq_im_logGamma ht
  have hne : ∀ t : ℝ, (1 / 2 + Complex.I * (t : ℂ)) ≠ 1 := fun t h => by
    simpa using congrArg Complex.re h
  have hζ : Continuous fun t : ℝ => riemannZeta (1 / 2 + Complex.I * (t : ℂ)) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ))
        (differentiableAt_riemannZeta (hne t)).continuousAt (by fun_prop)
  have hmul : ContinuousOn
      (fun t : ℝ => Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ))
        * riemannZeta (1 / 2 + Complex.I * (t : ℂ))) (Set.Ici 0) :=
    (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hθ).const_mul Complex.I)).mul hζ.continuousOn
  exact Complex.continuous_re.comp_continuousOn hmul
theorem hardyZ_eq_zero_iff_riemannZeta {t : ℝ} (ht : 0 ≤ t) :
    hardyZ t = 0 ↔ riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  set s : ℂ := 1 / 2 + Complex.I * (t : ℂ) with hs
  have hsre : s.re = 1 / 2 := by rw [hs]; simp
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; norm_num at hsre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre; norm_num at hsre
  have hconjs : starRingEnd ℂ s = 1 - s := by
    rw [hs]; simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_div₀, map_one, map_ofNat]; ring
  set w : ℂ := 1 / 4 + Complex.I * ((t : ℂ) / 2) with hw
  have hwim : w.im = t / 2 := by rw [hw]; simp
  set L : ℂ := logGamma w - w * (Real.log Real.pi : ℂ) with hL
  have hGammaℝ : Gammaℝ s = Complex.exp L := Complex.Gammaℝ_half_add_mul_I_eq_exp t
  have hLim : L.im = riemannSiegelTheta t := by
    have himeq : (w * (Real.log Real.pi : ℂ)).im = t / 2 * Real.log Real.pi := by
      rw [Complex.mul_im, hwim]; simp
    rw [hL, Complex.sub_im, himeq, hw]
    exact (riemannSiegelTheta_eq_im_logGamma ht).symm
  have hexpLre_ne : (Real.exp L.re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hsplit : Gammaℝ s
      = (Real.exp L.re : ℂ) * Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) := by
    rw [hGammaℝ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im L]
    rw [hLim]; ring
  have hexpiθ : Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ))
      = Gammaℝ s / (Real.exp L.re : ℂ) := by
    rw [eq_div_iff hexpLre_ne, mul_comm]; exact hsplit.symm
  have hQconj : starRingEnd ℂ ((1 / 2 : ℂ) * (s * (s - 1))) = (1 / 2 : ℂ) * (s * (s - 1)) := by
    simp only [map_mul, map_sub, map_one, map_div₀, map_ofNat, hconjs]; ring
  have hξconj : starRingEnd ℂ (riemannXi s) = riemannXi s := by
    rw [← riemannXi_conj, hconjs, riemannXi_one_sub]
  have hΓℝ_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hQ_ne : (1 / 2 : ℂ) * (s * (s - 1)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
  have hξ : riemannXi s = 1 / 2 * (s * (s - 1)) * Gammaℝ s * riemannZeta s :=
    riemannXi_eq_prefactor_mul hs0 hs1 hΓℝ_ne
  have hR : Gammaℝ s * riemannZeta s = riemannXi s / ((1 / 2 : ℂ) * (s * (s - 1))) := by
    rw [eq_div_iff hQ_ne, hξ]; ring
  have hξ_re : riemannXi s = ((riemannXi s).re : ℂ) := (Complex.conj_eq_iff_re.mp hξconj).symm
  have hQ_re : (1 / 2 : ℂ) * (s * (s - 1)) = (((1 / 2 : ℂ) * (s * (s - 1))).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp hQconj).symm
  have hR_eq : Gammaℝ s * riemannZeta s
      = (((riemannXi s).re / ((1 / 2 : ℂ) * (s * (s - 1))).re : ℝ) : ℂ) := by
    rw [hR]; conv_lhs => rw [hξ_re, hQ_re]
    rw [← Complex.ofReal_div]
  have hZC : ((hardyZ t : ℝ) : ℂ) = Gammaℝ s * riemannZeta s / (Real.exp L.re : ℂ) := by
    have hval : Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) * riemannZeta s
        = Gammaℝ s * riemannZeta s / (Real.exp L.re : ℂ) := by rw [hexpiθ]; ring
    rw [hardyZ, show (1 / 2 + Complex.I * (t : ℂ)) = s from hs.symm, hval, hR_eq,
      ← Complex.ofReal_div, Complex.ofReal_re]
  rw [← Complex.ofReal_eq_zero, hZC, div_eq_zero_iff, mul_eq_zero]
  simp only [hΓℝ_ne, hexpLre_ne, or_false, false_or]
theorem norm_expImul_sub_expImul_le_abs (α β : ℝ) :
    ‖Complex.exp (Complex.I * (α : ℂ)) - Complex.exp (Complex.I * (β : ℂ))‖ ≤ |α - β| := by
  have hunit : ‖Complex.exp (Complex.I * (β : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I β
  have hfac : Complex.exp (Complex.I * (α : ℂ)) - Complex.exp (Complex.I * (β : ℂ))
      = Complex.exp (Complex.I * (β : ℂ)) * (Complex.exp (Complex.I * ((α - β : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [hfac, norm_mul, hunit, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := α - β)
  rwa [Real.norm_eq_abs] at this
theorem norm_expImul_sub_expImul_le (α β : ℝ) (z w : ℂ) :
    ‖Complex.exp (Complex.I * (α : ℂ)) * z - Complex.exp (Complex.I * (β : ℂ)) * w‖
      ≤ |α - β| * ‖z‖ + ‖z - w‖ := by
  set a : ℂ := Complex.exp (Complex.I * (α : ℂ)) with ha
  set b : ℂ := Complex.exp (Complex.I * (β : ℂ)) with hb
  have hunit : ‖b‖ = 1 := by rw [hb, mul_comm]; exact Complex.norm_exp_ofReal_mul_I β
  have hphase : ‖a - b‖ ≤ |α - β| := norm_expImul_sub_expImul_le_abs α β
  have hsplit : a * z - b * w = (a - b) * z + b * (z - w) := by ring
  calc ‖a * z - b * w‖
      = ‖(a - b) * z + b * (z - w)‖ := by rw [hsplit]
    _ ≤ ‖(a - b) * z‖ + ‖b * (z - w)‖ := norm_add_le _ _
    _ = ‖a - b‖ * ‖z‖ + ‖z - w‖ := by rw [norm_mul, norm_mul, hunit, one_mul]
    _ ≤ |α - β| * ‖z‖ + ‖z - w‖ := by gcongr
theorem norm_expImul_sub_expImul_le' (α β : ℝ) (z w : ℂ) :
    ‖Complex.exp (Complex.I * (α : ℂ)) * z - Complex.exp (Complex.I * (β : ℂ)) * w‖
      ≤ |α - β| * ‖w‖ + ‖z - w‖ := by
  have h := norm_expImul_sub_expImul_le β α w z
  rwa [norm_sub_rev (Complex.exp (Complex.I * (β : ℂ)) * w), abs_sub_comm β α,
    norm_sub_rev w z] at h
theorem abs_hardyZ_sub_re_le' (t : ℝ) (θ' : ℝ) (ζ' : ℂ) :
    |hardyZ t - (Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re|
      ≤ |riemannSiegelTheta t - θ'| * ‖ζ'‖
        + ‖riemannZeta (1 / 2 + Complex.I * t) - ζ'‖ := by
  set ζv : ℂ := riemannZeta (1 / 2 + Complex.I * t) with hζv
  have hre : hardyZ t - (Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re
      = (Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) * ζv
          - Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re := by
    rw [hardyZ, hζv, Complex.sub_re]
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  exact norm_expImul_sub_expImul_le' (riemannSiegelTheta t) θ' ζv ζ'
open Complex.Stirling
noncomputable abbrev riemannSiegelThetaStirlingErrorBound (M N : ℕ) : ℝ :=
  ((2 * M + 1)! : ℝ) / (2 * M * (2 * Real.pi) ^ (2 * M)) * (1 / 4 + N : ℝ) ^ (-(2 * M : ℤ))
noncomputable abbrev riemannSiegelThetaStirlingErrorBound' (M N : ℕ) (t : ℝ) : ℝ :=
  ((2 * M + 1)! : ℝ) * 2 ^ (2 * M + 1) / (2 * M * (2 * Real.pi) ^ (2 * M))
    * ((1 / 4 + N) ^ 2 + (t / 2) ^ 2 : ℝ) ^ (-(M : ℤ))
noncomputable abbrev riemannSiegelThetaApproximant (M N : ℕ) (t : ℝ) : ℝ :=
  ((logGammaStirling M (1 / 4 + Complex.I * (t / 2) + N)
        - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
      - t / 2 * Real.log Real.pi : ℝ)
private theorem re_thetaArg_add_natCast (T : ℝ) (N : ℕ) :
    (1 / 4 + Complex.I * (T / 2) + (N : ℂ)).re = 1 / 4 + N := by
  simp
private theorem re_thetaArg_add_natCast_pos (T : ℝ) (N : ℕ) :
    0 < (1 / 4 + Complex.I * (T / 2) + (N : ℂ)).re := by
  rw [re_thetaArg_add_natCast]; positivity
private theorem riemannSiegelTheta_sub_approximant_eq {M N : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : 0 ≤ T) :
    riemannSiegelTheta T - riemannSiegelThetaApproximant M N T
      = (logGammaRemainderIoi M (1 / 4 + Complex.I * (T / 2) + N)).im := by
  have hreT : (0 : ℝ) < (1 / 4 + Complex.I * (T / 2)).re := by simp
  rw [riemannSiegelTheta_eq_im_logGamma hT, logGamma_eq_sub_sum_log_add hreT N,
    logGamma_eq_stirling_add_remainder hM (re_thetaArg_add_natCast_pos T N)]
  simp only [riemannSiegelThetaApproximant, Complex.add_im, Complex.sub_im]
  ring
theorem abs_riemannSiegelTheta_sub_stirling_shift_le {M N : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    |riemannSiegelTheta T - riemannSiegelThetaApproximant M N T|
      ≤ riemannSiegelThetaStirlingErrorBound M N := by
  rw [riemannSiegelTheta_sub_approximant_eq hM hT]
  refine (Complex.abs_im_le_norm _).trans
    ((norm_logGammaRemainderIoi_le hM (re_thetaArg_add_natCast_pos T N)).trans_eq ?_)
  simp only [logGammaRemainderBound, riemannSiegelThetaStirlingErrorBound]
  rw [re_thetaArg_add_natCast]
theorem abs_riemannSiegelTheta_sub_stirling_shift_le' {M N : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : 0 ≤ T) :
    |riemannSiegelTheta T - riemannSiegelThetaApproximant M N T|
      ≤ riemannSiegelThetaStirlingErrorBound' M N T := by
  rw [riemannSiegelTheta_sub_approximant_eq hM hT]
  refine (Complex.abs_im_le_norm _).trans
    ((norm_logGammaRemainderIoi_le' hM (re_thetaArg_add_natCast_pos T N)).trans_eq ?_)
  have hsq : ‖(1 / 4 + Complex.I * (T / 2) + (N : ℂ))‖ ^ 2 = (1 / 4 + N) ^ 2 + (T / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, re_thetaArg_add_natCast]
    simp [sq]
  simp only [logGammaRemainderNormBound, riemannSiegelThetaStirlingErrorBound']
  rw [show (-(2 * M : ℤ)) = 2 * (-(M : ℤ)) by ring, zpow_mul, zpow_ofNat, hsq]
theorem abs_riemannSiegelTheta_sub_stirling_le {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    |riemannSiegelTheta T
        - ((logGammaStirling M (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi)|
      ≤ riemannSiegelThetaStirlingErrorBound M 0 := by
  simpa [riemannSiegelThetaApproximant] using
    abs_riemannSiegelTheta_sub_stirling_shift_le (N := 0) hM hT
theorem abs_riemannSiegelTheta_sub_stirling_le' {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    |riemannSiegelTheta T
        - ((logGammaStirling M (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi)|
      ≤ logGammaRemainderNormBound M (1 / 4 + Complex.I * (T / 2)) := by
  have hre : (0 : ℝ) < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re := by simp
  have hdiff : riemannSiegelTheta T
      - ((logGammaStirling M (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi)
      = (logGammaRemainderIoi M (1 / 4 + Complex.I * (T / 2))).im := by
    rw [riemannSiegelTheta_eq_im_logGamma hT, logGamma_eq_stirling_add_remainder hM hre]
    simp only [Complex.add_im]
    ring
  rw [hdiff]
  exact (Complex.abs_im_le_norm _).trans (norm_logGammaRemainderIoi_le' hM hre)
theorem abs_riemannSiegelTheta_sub_approximant_two_le {t : ℝ} (ht : 0 < t) :
    |riemannSiegelTheta t - riemannSiegelThetaApproximant 2 0 t| ≤ 12 / t ^ 4 := by
  have him : (1 / 4 + Complex.I * ((t : ℂ) / 2)).im = t / 2 := by simp
  have hw : t / 2 ≤ ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ := by
    have h := Complex.abs_im_le_norm (1 / 4 + Complex.I * ((t : ℂ) / 2))
    rwa [him, abs_of_nonneg (by linarith)] at h
  have hpi : (1296 : ℝ) ≤ (2 * Real.pi) ^ 4 := by
    have h6 : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc (1296 : ℝ) = 6 ^ 4 := by norm_num
      _ ≤ (2 * Real.pi) ^ 4 := pow_le_pow_left₀ (by norm_num) h6 4
  have hz : ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ (-(2 * ((2 : ℕ) : ℤ))) ≤ 16 / t ^ 4 := by
    rw [show (-(2 * ((2 : ℕ) : ℤ))) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    calc (‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ 4)⁻¹ ≤ ((t / 2) ^ 4)⁻¹ :=
          inv_anti₀ (pow_pos (by linarith) 4) (pow_le_pow_left₀ (by linarith) hw 4)
      _ = 16 / t ^ 4 := by field_simp; ring
  have hexpand : logGammaRemainderNormBound 2 (1 / 4 + Complex.I * ((t : ℂ) / 2))
      = 960 / (2 * Real.pi) ^ 4
        * ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ (-(2 * ((2 : ℕ) : ℤ))) := by
    rw [logGammaRemainderNormBound]
    congr 1
    norm_num [Nat.factorial]
    ring
  have happrox : riemannSiegelThetaApproximant 2 0 t
      = (logGammaStirling 2 (1 / 4 + Complex.I * ((t : ℂ) / 2))).im
        - t / 2 * Real.log Real.pi := by
    simp [riemannSiegelThetaApproximant]
  rw [happrox]
  refine (abs_riemannSiegelTheta_sub_stirling_le' (M := 2) (by norm_num) ht.le).trans ?_
  rw [hexpand]
  calc 960 / (2 * Real.pi) ^ 4 * ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ (-(2 * ((2 : ℕ) : ℤ)))
      ≤ 960 / (2 * Real.pi) ^ 4 * (16 / t ^ 4) := mul_le_mul_of_nonneg_left hz (by positivity)
    _ ≤ 960 / 1296 * (16 / t ^ 4) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi) (by positivity)
    _ ≤ 12 / t ^ 4 := by
        rw [show (960 : ℝ) / 1296 * (16 / t ^ 4) = 320 / 27 / t ^ 4 from by ring]
        gcongr
        norm_num
def thetaShift (M : ℕ) : ℕ := 2 * M
noncomputable abbrev hardyZApproximantEM (M N : ℕ) (t : ℝ) : ℝ :=
  (Complex.exp (Complex.I * ((riemannSiegelThetaApproximant M (thetaShift M) t : ℝ) : ℂ))
      * zetaApproximant (1 / 2 + Complex.I * t) M N).re
noncomputable abbrev hardyZRemainderEM (M N : ℕ) (t : ℝ) : ℝ :=
  hardyZ t - hardyZApproximantEM M N t
noncomputable abbrev hardyZErrorBoundEM (M N : ℕ) (t : ℝ) : ℝ :=
  riemannSiegelThetaStirlingErrorBound M (thetaShift M)
      * ‖zetaApproximant (1 / 2 + Complex.I * t) M N‖
    + ‖zetaRemainder (1 / 2 + Complex.I * t) M N‖
theorem abs_hardyZRemainderEM_le {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    |hardyZRemainderEM M N t| ≤ hardyZErrorBoundEM M N t := by
  have hs1 : (1 / 2 + Complex.I * (t : ℂ)) ≠ 1 := fun h ↦ by
    simpa using congrArg Complex.re h
  have hsre : -(2 * M + 1 : ℝ) < (1 / 2 + Complex.I * (t : ℂ)).re := by
    rw [show (1 / 2 + Complex.I * (t : ℂ)).re = 1 / 2 by simp]
    have : (0 : ℝ) ≤ 2 * M + 1 := by positivity
    linarith
  have hzeta := riemannZeta_eq_approximant_add_remainder
    (1 / 2 + Complex.I * t) M N hN hsre hs1
  have hζdiff : riemannZeta (1 / 2 + Complex.I * t)
        - zetaApproximant (1 / 2 + Complex.I * t) M N
      = zetaRemainder (1 / 2 + Complex.I * t) M N := by
    rw [hzeta]; ring
  refine (abs_hardyZ_sub_re_le' t
      (riemannSiegelThetaApproximant M (thetaShift M) t)
      (zetaApproximant (1 / 2 + Complex.I * t) M N)).trans ?_
  rw [hardyZErrorBoundEM, hζdiff]
  gcongr
  exact abs_riemannSiegelTheta_sub_stirling_shift_le hM ht
end
end CertificatePort83
section CertificatePort84
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
namespace Complex
theorem deriv_digamma_add_one {s : ℂ} (hs : 0 < s.re) :
    deriv Complex.digamma (s + 1) = deriv Complex.digamma s - (s ^ 2)⁻¹ := by
  have hs1 : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hL : HasDerivAt (fun z ↦ Complex.digamma (z + 1)) (deriv Complex.digamma (s + 1)) s := by
    simpa [Function.comp_def] using
      (differentiableAt_digamma hs1).hasDerivAt.comp s ((hasDerivAt_id s).add_const 1)
  have heq : (fun z ↦ Complex.digamma (z + 1)) =ᶠ[nhds s] fun z ↦ Complex.digamma z + z⁻¹ := by
    filter_upwards [(isOpen_re_gt 0).mem_nhds hs] with z (hz : 0 < z.re)
    exact Complex.digamma_apply_add_one z (ne_neg_natCast_of_re_pos hz)
  rw [hL.unique <| ((differentiableAt_digamma hs).hasDerivAt.add
    (hasDerivAt_inv (Complex.ne_zero_of_re_pos hs))).congr_of_eventuallyEq heq]
  ring
theorem im_inv_sq_nonpos {w : ℂ} (hre : 0 ≤ w.re) (him : 0 ≤ w.im) : ((w ^ 2)⁻¹).im ≤ 0 := by
  rw [Complex.inv_im, neg_div, neg_nonpos, sq, Complex.mul_im]
  exact div_nonneg (by nlinarith [mul_nonneg hre him]) (Complex.normSq_nonneg _)
end Complex
end
end CertificatePort84
section CertificatePort85
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter
open scoped Topology Nat Real
namespace Complex
open Complex.Stirling
theorem norm_digamma_le {z : ℂ} (hz : 0 < z.re) (h1 : 1 ≤ ‖z‖) :
    ‖Complex.digamma z‖ ≤ Real.log ‖z‖ + (Real.pi + 3) := by
  have hlogpos : 0 ≤ Real.log ‖z‖ := Real.log_nonneg h1
  have hLog : ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, abs_of_nonneg hlogpos]
    linarith [Complex.abs_arg_le_pi z]
  have hinv : ‖(2 * z)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat]
    exact inv_le_one_of_one_le₀ (by nlinarith [h1])
  have hsum : ‖∑ k ∈ Finset.Icc 1 1, (bernoulli (2 * k) : ℂ) / (2 * k) * z ^ (-(2 * k : ℤ))‖
      ≤ 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, norm_mul]
    have hb : ‖(bernoulli (2 * 1) : ℂ) / (2 * (1 : ℕ))‖ ≤ 1 := by
      norm_num [bernoulli_two, Complex.norm_div]
    have hz2 : ‖z ^ (-(2 * (1 : ℕ) : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]; exact zpow_le_one_of_nonpos₀ h1 (by norm_num)
    exact mul_le_one₀ hb (norm_nonneg _) hz2
  have hrem : ‖digammaRemainderIoi z (2 * 1 + 1)‖ ≤ 1 := by
    have hb := norm_digammaRemainderIoi_le' z hz (2 * 1 + 1) (by norm_num)
    have hzp : ‖z‖ ^ (-(2 * 1 + 1 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ h1 (by norm_num)
    have hcoef : ((2 * 1 + 1)! : ℝ) / (2 * Real.pi) ^ ((2 * 1 + 1) - 1) ≤ 1 := by
      rw [show (2 * 1 + 1 : ℕ) = 3 from rfl, show (3 - 1 : ℕ) = 2 from rfl,
        show (3 ! : ℝ) = 6 from by norm_num, div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    exact hb.trans (mul_le_one₀ hcoef (zpow_nonneg (norm_nonneg _) _) hzp)
  rw [digamma_eq_log_sub z hz 1]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
  linarith [hLog, hinv, hsum, hrem]
private lemma re_sub_dist_le_re {c z : ℂ} {r : ℝ} (h : dist z c ≤ r) : c.re - r ≤ z.re := by
  have hab := Complex.abs_re_le_norm (c - z)
  rw [Complex.sub_re, show ‖c - z‖ = dist z c by rw [Complex.dist_eq, norm_sub_rev]] at hab
  linarith [(le_abs_self (c.re - z.re)).trans hab]
theorem tendsto_deriv_digamma_add_nat {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ ↦ deriv Complex.digamma (s + n)) atTop (𝓝 0) := by
  set L : ℝ := Real.pi + 3 with hL
  set K : ℝ := Real.log (2 * (‖s‖ + 1)) + L with hK
  have he : Tendsto (fun n : ℕ ↦ (2 * Real.log ↑n + 2 * K) / ↑n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ 2 * Real.log ↑n / ↑n) atTop (𝓝 0) := by
      have h0 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop).const_mul 2
      simp only [Function.comp_def, id_eq, mul_zero] at h0
      exact h0.congr fun n ↦ by rw [mul_div_assoc]
    have h2 : Tendsto (fun n : ℕ ↦ 2 * K / ↑n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (2 * K)
    simpa [add_div] using h1.add h2
  refine squeeze_zero_norm' ?_ he
  filter_upwards [eventually_ge_atTop (max 1 ⌈2 - s.re⌉₊)] with n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hnpos : 0 < (n : ℝ) := by linarith
  set c : ℂ := s + ↑n with hc
  have hcre : c.re = s.re + ↑n := by rw [hc, Complex.add_re, Complex.natCast_re]
  have hcre2 : 2 ≤ c.re := by
    rw [hcre]
    have hle : (⌈2 - s.re⌉₊ : ℝ) ≤ ↑n := by exact_mod_cast le_trans (le_max_right _ _) hn
    linarith [Nat.le_ceil (2 - s.re), hle]
  set R : ℝ := c.re / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hR1 : 1 ≤ R := by rw [hR]; linarith
  have hbound : ‖deriv Complex.digamma c‖ ≤ (Real.log (2 * (‖s‖ + ↑n)) + L) / R := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos
    · apply DifferentiableOn.diffContOnCl
      intro z hz
      have hzc : dist z c ≤ R :=
        Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hz)
      exact (differentiableAt_digamma (by linarith [re_sub_dist_le_re hzc])).differentiableWithinAt
    · intro z hz
      have hzc : dist z c = R := Metric.mem_sphere.mp hz
      have hzre : R ≤ z.re := by linarith [re_sub_dist_le_re hzc.le]
      have hznorm1 : 1 ≤ ‖z‖ := le_trans hR1 (hzre.trans (Complex.re_le_norm z))
      have hznorm : ‖z‖ ≤ 2 * (‖s‖ + ↑n) := by
        have hcn : ‖c‖ ≤ ‖s‖ + ↑n := by
          rw [hc]
          simpa [Complex.norm_natCast] using norm_add_le s (↑n : ℂ)
        have hzc' : ‖z - c‖ = R := by rw [← Complex.dist_eq]; exact hzc
        have hz1 : ‖z‖ ≤ ‖c‖ + R := hzc' ▸ norm_le_norm_add_norm_sub' z c
        have hRle : R ≤ ‖s‖ + ↑n := by
          rw [hR, hcre]; linarith [Complex.re_le_norm s, norm_nonneg s]
        linarith
      calc ‖Complex.digamma z‖ ≤ Real.log ‖z‖ + L := norm_digamma_le (by linarith [hzre]) hznorm1
        _ ≤ Real.log (2 * (‖s‖ + ↑n)) + L := by gcongr
  refine hbound.trans ?_
  have hnum : Real.log (2 * (‖s‖ + ↑n)) + L ≤ Real.log ↑n + K := by
    have hmul : (2 : ℝ) * (‖s‖ + ↑n) ≤ 2 * (‖s‖ + 1) * ↑n := by nlinarith [norm_nonneg s, hn1]
    have hlog : Real.log (2 * (‖s‖ + ↑n)) ≤ Real.log (2 * (‖s‖ + 1)) + Real.log ↑n := by
      rw [← Real.log_mul (by positivity) (by linarith)]
      exact Real.log_le_log (by positivity) hmul
    rw [hK]; linarith
  have hnum0 : 0 ≤ Real.log (2 * (‖s‖ + ↑n)) + L := by
    have : 0 ≤ Real.log (2 * (‖s‖ + ↑n)) := Real.log_nonneg (by nlinarith [norm_nonneg s, hn1])
    rw [hL]; linarith [Real.pi_pos]
  rw [hR]
  calc (Real.log (2 * (‖s‖ + ↑n)) + L) / (c.re / 2)
      ≤ (Real.log (2 * (‖s‖ + ↑n)) + L) / (↑n / 2) :=
        div_le_div_of_nonneg_left hnum0 (by positivity) (by rw [hcre]; linarith)
    _ = (Real.log (2 * (‖s‖ + ↑n)) + L) * 2 / ↑n := by rw [div_div_eq_mul_div]
    _ ≤ (2 * Real.log ↑n + 2 * K) / ↑n := by gcongr; linarith [hnum]
theorem im_deriv_digamma_nonpos {s : ℂ} (hs : 0 < s.re) (him : 0 ≤ s.im) :
    (deriv Complex.digamma s).im ≤ 0 := by
  have htel : ∀ n : ℕ, deriv Complex.digamma s
      = deriv Complex.digamma (s + ↑n) + ∑ k ∈ Finset.range n, ((s + ↑k) ^ 2)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have hsm : 0 < (s + ↑m).re := by
        simp only [Complex.add_re, Complex.natCast_re]
        linarith [Nat.cast_nonneg (α := ℝ) m]
      rw [show (s : ℂ) + ↑(m + 1) = (s + ↑m) + 1 by push_cast; ring, deriv_digamma_add_one hsm,
        Finset.sum_range_succ, ih]
      ring
  have hle : ∀ n : ℕ, (deriv Complex.digamma s).im ≤ (deriv Complex.digamma (s + ↑n)).im := by
    intro n
    rw [htel n, Complex.add_im, Complex.im_sum]
    have hsum : (∑ k ∈ Finset.range n, (((s + (k : ℂ)) ^ 2)⁻¹).im) ≤ 0 :=
      Finset.sum_nonpos fun k _ ↦ im_inv_sq_nonpos
        (by simp only [Complex.add_re, Complex.natCast_re];
            linarith [Nat.cast_nonneg (α := ℝ) k, hs.le])
        (by simp only [Complex.add_im, Complex.natCast_im, add_zero]; exact him)
    linarith
  have hlim : Tendsto (fun n : ℕ ↦ (deriv Complex.digamma (s + ↑n)).im) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_im.tendsto 0).comp (tendsto_deriv_digamma_add_nat hs)
  exact ge_of_tendsto' hlim hle
theorem monotoneOn_re_digamma_quarter_vertical :
    MonotoneOn (fun T : ℝ ↦ (Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).re)
      (Set.Ici 0) := by
  have hre : ∀ T : ℝ, 0 < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re := fun T ↦ by
    rw [show (1 / 4 + Complex.I * ((T : ℂ) / 2)).re = 1 / 4 by simp]; norm_num
  have hderiv : ∀ T : ℝ,
      HasDerivAt (fun t : ℝ ↦ (Complex.digamma (1 / 4 + Complex.I * ((t : ℂ) / 2))).re)
        (-(1 / 2) * (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im) T := by
    intro T
    have haff : HasDerivAt (fun z : ℂ ↦ (1 / 4 : ℂ) + Complex.I * (z / 2)) (Complex.I * (1 / 2))
        (T : ℂ) := (((hasDerivAt_id (T : ℂ)).div_const 2).const_mul Complex.I).const_add (1 / 4)
    have hcomp := ((differentiableAt_digamma (hre T)).hasDerivAt.comp (T : ℂ) haff).comp_ofReal
    have hg := Complex.reCLM.hasFDerivAt.comp_hasDerivAt T hcomp
    simp only [Complex.reCLM_apply, Function.comp_apply] at hg
    rw [show (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2)) * (Complex.I * (1 / 2))).re
        = -(1 / 2) * (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im by
      simp [Complex.mul_re]; ring] at hg
    exact hg
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr fun T ↦ (hderiv T).continuousAt).continuousOn
  · exact fun T _ ↦ (hderiv T).differentiableAt.differentiableWithinAt
  · intro T hT
    rw [interior_Ici] at hT
    rw [(hderiv T).deriv]
    have him : (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im ≤ 0 := by
      refine im_deriv_digamma_nonpos (hre T) ?_
      have hval : (1 / 4 + Complex.I * ((T : ℂ) / 2)).im = T / 2 := by simp
      rw [hval]; linarith [Set.mem_Ioi.mp hT]
    linarith
end Complex
end
end CertificatePort85
section CertificatePort86
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open MeasureTheory Filter
open scoped Topology Real
open Complex
theorem ConvexOn.integral_sub_left_le {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hfc : ContinuousOn f (Set.Icc a b)) :
    ∫ t in a..b, (f t - f a) ≤ (b - a) * (f b - f a) / 2 := by
  have hba : (0 : ℝ) < b - a := by linarith
  set k : ℝ := (f b - f a) / (b - a) with hk
  have hkval : k * (b - a) = f b - f a := div_mul_cancel₀ _ hba.ne'
  have hchord : ∀ t ∈ Set.Icc a b, f t - f a ≤ k * (t - a) := fun t ht ↦ by
    rcases eq_or_lt_of_le ht.1 with h | hlt
    · simp [← h]
    · rcases eq_or_lt_of_le ht.2 with h2 | hlt2
      · rw [h2]; exact hkval.ge
      · exact (div_le_iff₀ (by linarith : (0 : ℝ) < t - a)).1 (hk ▸ hf.secant_mono_aux2
          (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le) hlt hlt2)
  have hmono := intervalIntegral.integral_mono_on hab.le
    ((hfc.intervalIntegrable_of_Icc (μ := volume) hab.le).sub intervalIntegrable_const)
    ((by fun_prop : Continuous fun t ↦ k * (t - a)).intervalIntegrable a b) hchord
  have heval : ∫ t in a..b, k * (t - a) = (b - a) * (f b - f a) / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun t ↦ t) a, integral_id, ← hkval]
    ring
  rwa [heval] at hmono
theorem hasDerivAt_riemannSiegelTheta {T : ℝ} (hT : 0 < T) :
    HasDerivAt riemannSiegelTheta
      (1 / 2 * (Complex.digamma (1 / 4 + Complex.I * (T / 2))).re
        - 1 / 2 * Real.log Real.pi) T := by
  set w : ℂ := 1 / 4 + Complex.I * ((T : ℂ) / 2) with hw
  have hre : 0 < w.re := by rw [show w.re = 1 / 4 by rw [hw]; simp]; norm_num
  have hcurve := ((hasDerivAt_logGamma hre).comp (T : ℂ)
    ((((hasDerivAt_id (T : ℂ)).div_const 2).const_mul Complex.I).const_add (1 / 4))).comp_ofReal
  have hg := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt T hcurve).sub
    (((hasDerivAt_id T).div_const 2).mul_const (Real.log Real.pi))
  simp only [Complex.imCLM_apply, Function.comp_apply] at hg
  rw [show (Complex.digamma w * (Complex.I * (1 / 2))).im - 1 / 2 * Real.log Real.pi
      = 1 / 2 * (Complex.digamma w).re - 1 / 2 * Real.log Real.pi by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      show ((1 : ℂ) / 2).re = 1 / 2 by simp, show ((1 : ℂ) / 2).im = 0 by simp]
    ring] at hg
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with s (hs : (0 : ℝ) < s)
  exact riemannSiegelTheta_eq_im_logGamma hs.le
theorem continuousOn_riemannSiegelTheta : ContinuousOn riemannSiegelTheta (Set.Ici 0) := by
  have hline : Continuous fun T : ℝ ↦ (1 / 4 : ℂ) + Complex.I * ((T : ℂ) / 2) :=
    ((Complex.continuous_ofReal.div_const 2).const_mul Complex.I).const_add (1 / 4)
  have hcurve : Continuous fun T : ℝ ↦ logGamma (1 / 4 + Complex.I * ((T : ℂ) / 2)) :=
    continuous_iff_continuousAt.2 fun T ↦ ContinuousAt.comp
      (f := fun T : ℝ ↦ (1 / 4 : ℂ) + Complex.I * ((T : ℂ) / 2))
      (hasDerivAt_logGamma (show 0 < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re by
        rw [show (1 / 4 + Complex.I * ((T : ℂ) / 2)).re = 1 / 4 by simp]; norm_num)).continuousAt
      hline.continuousAt
  exact ((Complex.continuous_im.comp hcurve).sub
    ((continuous_id.div_const 2).mul continuous_const)).continuousOn.congr
      fun T hT ↦ riemannSiegelTheta_eq_im_logGamma hT
theorem convexOn_riemannSiegelTheta : ConvexOn ℝ (Set.Ici 0) riemannSiegelTheta := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) continuousOn_riemannSiegelTheta
    (fun T hT ↦ ?_) (fun x hx y hy hxy ↦ ?_)
  · rw [interior_Ici] at hT
    exact (hasDerivAt_riemannSiegelTheta hT).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at hx hy
    rw [(hasDerivAt_riemannSiegelTheta hx).deriv, (hasDerivAt_riemannSiegelTheta hy).deriv]
    linarith [monotoneOn_re_digamma_quarter_vertical (Set.mem_Ici.2 (Set.mem_Ioi.mp hx).le)
      (Set.mem_Ici.2 (Set.mem_Ioi.mp hy).le) hxy]
noncomputable def gramCoord (l t : ℝ) : ℝ := (riemannSiegelTheta t - riemannSiegelTheta l) / Real.pi
theorem integral_gramCoord_le {l h : ℝ} (hl : 0 ≤ l) (hh : 0 < h)
    (hgram : riemannSiegelTheta (l + h) - riemannSiegelTheta l = Real.pi) :
    ∫ t in l..l + h, gramCoord l t ≤ h / 2 := by
  have hsub : Set.Icc l (l + h) ⊆ Set.Ici 0 := fun x hx ↦ hl.trans hx.1
  have key : ∫ t in l..l + h, (riemannSiegelTheta t - riemannSiegelTheta l) ≤ h / 2 * Real.pi := by
    have h0 := ConvexOn.integral_sub_left_le (show l < l + h by linarith)
      (convexOn_riemannSiegelTheta.subset hsub (convex_Icc l (l + h)))
      (continuousOn_riemannSiegelTheta.mono hsub)
    rw [hgram] at h0
    exact h0.trans_eq (by ring)
  rw [show (∫ t in l..l + h, gramCoord l t)
        = (∫ t in l..l + h, (riemannSiegelTheta t - riemannSiegelTheta l)) / Real.pi by
      simp only [gramCoord, intervalIntegral.integral_div], div_le_iff₀ Real.pi_pos]
  linarith [key]
private theorem le_of_stepwise_lt {k : ℕ} {p : ℕ → ℝ} (hmono : ∀ i < k, p i < p (i + 1)) :
    ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ k → p i ≤ p j := by
  intro i j hij
  induction hij with
  | refl => exact fun _ ↦ le_rfl
  | @step m _ ih => exact fun hmk ↦ (ih (by lia)).trans (hmono m (by lia)).le
theorem sum_integral_gramCoord_le {k : ℕ} {p : ℕ → ℝ} (hp0 : 0 ≤ p 0)
    (hmono : ∀ i < k, p i < p (i + 1))
    (hgram : ∀ i < k, riemannSiegelTheta (p (i + 1)) - riemannSiegelTheta (p i) = Real.pi) :
    ∑ i ∈ Finset.range k, ∫ t in p i..p (i + 1), gramCoord (p i) t ≤ (p k - p 0) / 2 := by
  refine (Finset.sum_le_sum (g := fun i ↦ (p (i + 1) - p i) / 2) fun i hi ↦ ?_).trans
    (le_of_eq (by rw [← Finset.sum_div, Finset.sum_range_sub]))
  have hi' : i < k := Finset.mem_range.1 hi
  have e : p i + (p (i + 1) - p i) = p (i + 1) := by ring
  have hkey := integral_gramCoord_le (l := p i) (h := p (i + 1) - p i)
    (hp0.trans (le_of_stepwise_lt hmono (Nat.zero_le i) hi'.le))
    (by linarith [hmono i hi']) (by rw [e]; exact hgram i hi')
  rwa [e] at hkey
theorem integral_fract_gramCoord_le {k : ℕ} {p : ℕ → ℝ} (hp0 : 0 ≤ p 0)
    (hmono : ∀ i < k, p i < p (i + 1))
    (hsmono : StrictMonoOn riemannSiegelTheta (Set.Icc (p 0) (p k)))
    (hgram : ∀ i < k, riemannSiegelTheta (p (i + 1)) - riemannSiegelTheta (p i) = Real.pi) :
    ∫ t in p 0..p k, Int.fract (gramCoord (p 0) t) ≤ (p k - p 0) / 2 := by
  have hple := le_of_stepwise_lt hmono
  have htel : ∀ j, j ≤ k →
      riemannSiegelTheta (p j) = riemannSiegelTheta (p 0) + (j : ℝ) * Real.pi := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ m ih =>
      intro hj
      push_cast
      rw [show riemannSiegelTheta (p (m + 1)) = riemannSiegelTheta (p m) + Real.pi from by
        linarith [hgram m (by lia)], ih (by lia)]
      ring
  have hpt : ∀ i, i < k → ∀ t, p i < t → t < p (i + 1) →
      Int.fract (gramCoord (p 0) t) = gramCoord (p i) t := by
    intro i hik t htl htr
    have hmemi : p i ∈ Set.Icc (p 0) (p k) :=
      ⟨hple (Nat.zero_le i) hik.le, hple hik.le le_rfl⟩
    have hmemi1 : p (i + 1) ∈ Set.Icc (p 0) (p k) :=
      ⟨hple (Nat.zero_le _) hik, hple hik le_rfl⟩
    have hmemt : t ∈ Set.Icc (p 0) (p k) :=
      ⟨(hmemi.1.trans_lt htl).le, (htr.trans_le hmemi1.2).le⟩
    have hlow := hsmono.monotoneOn hmemi hmemt htl.le
    have hhigh : riemannSiegelTheta t < riemannSiegelTheta (p (i + 1)) := hsmono hmemt hmemi1 htr
    have hgx : gramCoord (p 0) t = gramCoord (p i) t + (i : ℝ) := by
      simp only [gramCoord]; rw [htel i hik.le]; field_simp; ring
    have h0 : 0 ≤ gramCoord (p i) t := div_nonneg (by linarith) Real.pi_pos.le
    have h1 : gramCoord (p i) t < 1 := by
      simp only [gramCoord]; rw [div_lt_one Real.pi_pos]; linarith [hgram i hik]
    rw [hgx, Int.fract_add_natCast]
    exact Int.fract_eq_self.mpr ⟨h0, h1⟩
  have hmain : ∀ i, i < k → ∀ᵐ t ∂volume,
      t ∈ Set.uIoc (p i) (p (i + 1)) → Int.fract (gramCoord (p 0) t) = gramCoord (p i) t := by
    intro i hik
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (p (i + 1)))] with t ht htmem
    rw [Set.uIoc_of_le (hmono i hik).le] at htmem
    exact hpt i hik t htmem.1 (lt_of_le_of_ne htmem.2 (by simpa using ht))
  have hcont : ∀ i, i < k → ContinuousOn (gramCoord (p i)) (Set.uIcc (p i) (p (i + 1))) := by
    intro i hik
    rw [Set.uIcc_of_le (hmono i hik).le]
    have hsub : Set.Icc (p i) (p (i + 1)) ⊆ Set.Ici 0 :=
      fun x hx ↦ Set.mem_Ici.mpr ((hp0.trans (hple (Nat.zero_le i) hik.le)).trans hx.1)
    unfold gramCoord
    exact ((continuousOn_riemannSiegelTheta.mono hsub).sub continuousOn_const).div_const _
  have hint : ∀ i, i < k →
      IntervalIntegrable (fun t ↦ Int.fract (gramCoord (p 0) t)) volume (p i) (p (i + 1)) :=
    fun i hik ↦ (intervalIntegrable_congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (hmain i hik))).mpr
        (hcont i hik).intervalIntegrable
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint,
    Finset.sum_congr rfl (fun i hi ↦ intervalIntegral.integral_congr_ae
      (hmain i (Finset.mem_range.mp hi)))]
  exact sum_integral_gramCoord_le hp0 hmono hgram
open Set
abbrev gramDomain : Set ℝ := Ici 7
private theorem log_pi_lt_re_digamma_quarter_seven :
    Real.log Real.pi < (Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re := by
  set s : ℂ := 1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2) with hs_def
  have hsre : s.re = 1 / 4 := by rw [hs_def]; simp
  have hsim : s.im = 7 / 2 := by rw [hs_def]; simp
  have hnormSq : Complex.normSq s = 197 / 16 := by
    rw [Complex.normSq_apply, hsre, hsim]; norm_num
  have hnorm_pos : 0 < ‖s‖ :=
    norm_pos_iff.mpr (Complex.ne_zero_of_re_pos (by rw [hsre]; norm_num))
  have hnorm_sq : ‖s‖ ^ 2 = 197 / 16 := by rw [Complex.sq_norm]; exact hnormSq
  have hnorm_lo : (3.5088 : ℝ) < ‖s‖ := by
    nlinarith [hnorm_sq, hnorm_pos, sq_nonneg (‖s‖ - 3.5088)]
  have hDbound : ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * ‖s‖ ^ (-(2 : ℤ)) :=
    Complex.Stirling.norm_digamma_sub_log_le' (by norm_num) s (by rw [hsre])
  have hinv_re : ((2 * s)⁻¹).re = 2 / 197 := by
    rw [Complex.inv_re, Complex.normSq_mul, Complex.mul_re]
    simp only [hsre, hsim, hnormSq]
    norm_num
  have hdecomp : (Complex.digamma s).re = Real.log ‖s‖ - 2 / 197
      + (Complex.digamma s - Complex.log s + (2 * s)⁻¹).re := by
    rw [Complex.add_re, Complex.sub_re, Complex.log_re, hinv_re]; ring
  have hDre : -‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (Complex.digamma s - Complex.log s + (2 * s)⁻¹).re :=
    (abs_le.1 (Complex.abs_re_le_norm _)).1
  have hπ2 : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hDbound2 : ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ 0.06 := by
    refine hDbound.trans ?_
    rw [show ‖s‖ ^ (-(2 : ℤ)) = 16 / 197 by
      rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hnorm_sq]; norm_num]
    have hv : 3 / (2 * π ^ 2 * (1 / 4)) < 0.6080 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [hπ2]
    nlinarith [hv]
  have hlogdiff : 1 - π / ‖s‖ ≤ Real.log ‖s‖ - Real.log π := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ‖s‖ / π by positivity)
    rwa [Real.log_div hnorm_pos.ne' Real.pi_pos.ne', inv_div] at h
  have hu : π / ‖s‖ < 0.8954 := by
    rw [div_lt_iff₀ hnorm_pos]; nlinarith [Real.pi_lt_d4, hnorm_lo]
  linarith [hdecomp, hDre, hDbound2, hlogdiff, hu]
private theorem le_deriv_riemannSiegelTheta {x : ℝ} (hx : 7 < x) :
    ((Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re - Real.log π) / 2
      ≤ deriv riemannSiegelTheta x := by
  rw [(hasDerivAt_riemannSiegelTheta (by linarith : (0 : ℝ) < x)).deriv]
  have hmono := Complex.monotoneOn_re_digamma_quarter_vertical
    (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 7)) (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ x)) hx.le
  simp only at hmono
  linarith
theorem strictMonoOn_riemannSiegelTheta_gramDomain :
    StrictMonoOn riemannSiegelTheta gramDomain := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 7)
    (continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num))) fun x hx ↦ ?_
  rw [interior_Ici] at hx
  linarith [le_deriv_riemannSiegelTheta (Set.mem_Ioi.mp hx), log_pi_lt_re_digamma_quarter_seven]
theorem continuousOn_riemannSiegelTheta_gramDomain : ContinuousOn riemannSiegelTheta gramDomain :=
  continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num))
theorem tendsto_riemannSiegelTheta_atTop : atTop.Tendsto riemannSiegelTheta atTop := by
  set c := ((Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re - Real.log π) / 2
    with hc
  have hc_pos : 0 < c := by rw [hc]; linarith [log_pi_lt_re_digamma_quarter_seven]
  have hcont := continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num : (0:ℝ) ≤ 7))
  have hdiff : DifferentiableOn ℝ riemannSiegelTheta (interior (Ici (7 : ℝ))) := by
    rw [interior_Ici]
    exact fun x hx ↦ (hasDerivAt_riemannSiegelTheta (by linarith [Set.mem_Ioi.mp hx] :
      (0 : ℝ) < x)).differentiableAt.differentiableWithinAt
  have hlin : ∀ x ∈ Ici (7 : ℝ), c * (x - 7) ≤ riemannSiegelTheta x - riemannSiegelTheta 7 :=
    fun x hx ↦ Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici 7) hcont hdiff
      (fun x hx ↦ hc ▸ le_deriv_riemannSiegelTheta (by rwa [interior_Ici] at hx))
      7 Set.self_mem_Ici x hx (Set.mem_Ici.mp hx)
  have hg : Tendsto (fun x : ℝ ↦ riemannSiegelTheta 7 + c * (x - 7)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (Tendsto.const_mul_atTop hc_pos (tendsto_atTop_add_const_right atTop (-7) tendsto_id))
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [eventually_ge_atTop (7 : ℝ)] with x hx
  linarith [hlin x (Set.mem_Ici.mpr hx)]
private theorem riemannSiegelTheta_seven_nonpos : riemannSiegelTheta 7 ≤ 0 := by
  have herr : riemannSiegelThetaStirlingErrorBound 1 0 = 12 / π ^ 2 := by
    simp only [riemannSiegelThetaStirlingErrorBound, Nat.cast_one, mul_one,
      Nat.cast_zero, add_zero]
    rw [show (Nat.factorial (2 * 1 + 1) : ℝ) = 6 by norm_num [Nat.factorial],
      show (2 * Real.pi) ^ (2 * 1) = 4 * π ^ 2 by ring,
      show ((1 / 4 : ℝ)) ^ (-2 : ℤ) = 16 by norm_num]
    have : (0 : ℝ) < π ^ 2 := by positivity
    field_simp
    ring
  have hθ := (abs_le.1 (abs_riemannSiegelTheta_sub_stirling_le (M := 1)
    (le_refl 1) (T := 7) (by norm_num : (0 : ℝ) ≤ 7))).2
  rw [herr] at hθ
  set w : ℂ := 1 / 4 + Complex.I * ((7 : ℝ) / 2) with hw_def
  have hwre : w.re = 1 / 4 := by rw [hw_def]; simp
  have hwim : w.im = 7 / 2 := by rw [hw_def]; simp
  have hnormSq : Complex.normSq w = 197 / 16 := by rw [Complex.normSq_apply, hwre, hwim]; norm_num
  have hnorm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr (Complex.ne_zero_of_re_pos (by rw [hwre]; norm_num))
  have hnorm_le4 : ‖w‖ ≤ 4 := by nlinarith [Complex.sq_norm w, hnormSq, norm_nonneg w]
  have hargnn : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.mpr (by rw [hwim]; norm_num)
  have hinvim : (w⁻¹).im ≤ 0 := by rw [Complex.inv_im, hwim, hnormSq]; norm_num
  have hlog_le : Real.log ‖w‖ ≤ Real.log 4 := Real.log_le_log hnorm_pos hnorm_le4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hIm : (Complex.Stirling.logGammaStirling 1 w).im ≤ 7 * Real.log 2 - 7 / 2 := by
    rw [Complex.Stirling.logGammaStirling]
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have hcoeff : (↑(bernoulli (2 * 1)) : ℂ) / (2 * (↑(1 : ℕ) : ℂ) * (2 * (↑(1 : ℕ) : ℂ) - 1))
        = ((1 / 12 : ℝ) : ℂ) := by
      rw [show (2 * 1 : ℕ) = 2 from rfl, bernoulli_two]; push_cast; norm_num
    have hval : ((w - 1 / 2) * Complex.log w - w + 1 / 2 * (↑(Real.log (2 * Real.pi)) : ℂ)
        + ((1 / 12 : ℝ) : ℂ) * w⁻¹).im
        = (w.re - 1 / 2) * Complex.arg w + w.im * Real.log ‖w‖ - w.im
          + (1 / 12) * (w⁻¹).im := by
      rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.sub_re,
        Complex.ofReal_im, Complex.ofReal_re, Complex.log_im, Complex.log_re]
      ring
    rw [show w ^ (1 - 2 * ((1 : ℕ) : ℤ)) = w⁻¹ by norm_num, hcoeff, hval, hwre, hwim]
    nlinarith [hargnn, hlog_le, hinvim, hlog4]
  have hπ2 : (9.84 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hlogπ : 1 < Real.log π := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9, Real.pi_gt_d6])
  have h12 : 12 / π ^ 2 < 1.22 := by rw [div_lt_iff₀ (by positivity)]; nlinarith [hπ2]
  nlinarith [hθ, hIm, h12, hlogπ, Real.log_two_lt_d9]
theorem riemannSiegelTheta_seven_le (n : ℕ) :
    riemannSiegelTheta 7 ≤ n * π :=
  le_trans riemannSiegelTheta_seven_nonpos (by positivity)
end
end CertificatePort86
section CertificatePort87
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f g : 𝕜 → F}
theorem iteratedDeriv_succ_of_hasDerivAt (h : ∀ x, HasDerivAt f (g x) x) (n : ℕ) :
    iteratedDeriv (n + 1) f = iteratedDeriv n g := by
  rw [iteratedDeriv_succ', funext fun x ↦ (h x).deriv]
end
end CertificatePort87
section CertificatePort88
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open MeasureTheory Real
open scoped Nat
namespace Real
theorem exp_neg_pi_mul_sq_add_mul_abs_le (b w : ℝ) :
    exp (-(π * w ^ 2) + b * |w|)
      ≤ exp (b ^ 2 / (4 * π)) *
        (exp (-π * (w - b / (2 * π)) ^ 2) + exp (-π * (w + b / (2 * π)) ^ 2)) := by
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  rcases abs_cases w with ⟨hw, -⟩ | ⟨hw, -⟩
  · have key : -(π * w ^ 2) + b * |w| = b ^ 2 / (4 * π) + -π * (w - b / (2 * π)) ^ 2 := by
      rw [hw]; field_simp; ring
    rw [key, exp_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (exp_pos _).le) (exp_pos _).le
  · have key : -(π * w ^ 2) + b * |w| = b ^ 2 / (4 * π) + -π * (w + b / (2 * π)) ^ 2 := by
      rw [hw]; field_simp; ring
    rw [key, exp_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (exp_pos _).le) (exp_pos _).le
end Real
private theorem integrable_exp_neg_pi_mul_sub_sq (c : ℝ) :
    Integrable fun w : ℝ ↦ exp (-π * (w - c) ^ 2) :=
  (integrable_exp_neg_mul_sq pi_pos).comp_sub_right c
private theorem integrable_exp_neg_pi_mul_add_sq (c : ℝ) :
    Integrable fun w : ℝ ↦ exp (-π * (w + c) ^ 2) := by
  simpa [sub_neg_eq_add] using integrable_exp_neg_pi_mul_sub_sq (-c)
private theorem integrable_majorant (b : ℝ) :
    Integrable fun w : ℝ ↦ exp (b ^ 2 / (4 * π)) *
      (exp (-π * (w - b / (2 * π)) ^ 2) + exp (-π * (w + b / (2 * π)) ^ 2)) :=
  ((integrable_exp_neg_pi_mul_sub_sq _).add (integrable_exp_neg_pi_mul_add_sq _)).const_mul _
theorem integrable_exp_neg_pi_mul_sq_add_mul_abs (b : ℝ) :
    Integrable fun w : ℝ ↦ exp (-(π * w ^ 2) + b * |w|) := by
  refine (integrable_majorant b).mono' (by fun_prop) (Filter.Eventually.of_forall fun w ↦ ?_)
  rw [norm_of_nonneg (exp_pos _).le]
  exact exp_neg_pi_mul_sq_add_mul_abs_le b w
theorem integrable_rpow_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {q : ℝ} (hq : -1 < q) :
    Integrable fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2) := by
  have hIoi : IntegrableOn (fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2)) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq hb hq).congr_fun
      (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi
  have hIio : IntegrableOn (fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2)) (Set.Iio 0) := by
    simpa using hIoi.comp_neg
  rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hIio, hIoi⟩
theorem integrable_rpow_abs_mul_exp_neg_pi_mul_sq_add_mul_abs {q : ℝ} (hq : -1 < q) (b : ℝ) :
    Integrable fun w : ℝ ↦ |w| ^ q * exp (-(π * w ^ 2) + b * |w|) := by
  have hmaj : Integrable fun w : ℝ ↦ exp (b ^ 2 / (2 * π)) * (|w| ^ q * exp (-(π / 2) * w ^ 2)) :=
    (integrable_rpow_abs_mul_exp_neg_mul_sq (by positivity) hq).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ ↦ |w| ^ q * exp (-(π * w ^ 2) + b * |w|)) volume := by
    have h1 := (integrable_rpow_abs_mul_exp_neg_mul_sq pi_pos hq).aestronglyMeasurable
    have h2 : Continuous fun w : ℝ ↦ exp (b * |w|) := by fun_prop
    refine (h1.mul h2.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.mul_apply]
    rw [mul_assoc, ← exp_add, show -π * w ^ 2 + b * |w| = -(π * w ^ 2) + b * |w| by ring]
  refine hmaj.mono' hmeas (Filter.Eventually.of_forall fun w ↦ ?_)
  have hkey : -(π * w ^ 2) + b * |w| ≤ b ^ 2 / (2 * π) + -(π / 2) * w ^ 2 := by
    rw [← sub_nonneg, ← sq_abs w,
      show b ^ 2 / (2 * π) + -(π / 2) * |w| ^ 2 - (-(π * |w| ^ 2) + b * |w|)
        = (π * |w| - b) ^ 2 / (2 * π) by field_simp; ring]
    positivity
  rw [norm_of_nonneg (by positivity)]
  calc |w| ^ q * exp (-(π * w ^ 2) + b * |w|)
      ≤ |w| ^ q * exp (b ^ 2 / (2 * π) + -(π / 2) * w ^ 2) := by gcongr
    _ = exp (b ^ 2 / (2 * π)) * (|w| ^ q * exp (-(π / 2) * w ^ 2)) := by
        rw [exp_add]; ring
section Moments
variable {b : ℝ}
theorem integrableOn_pow_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun w : ℝ ↦ w ^ n * exp (-b * w ^ 2)) (Set.Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_sq hb
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
theorem integrable_abs_pow_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2) := by
  simpa using integrable_rpow_abs_mul_exp_neg_mul_sq hb
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
theorem integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs (hb : 0 < b) (c : ℝ) (n : ℕ) :
    Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2 + c * |w|) := by
  have hmaj : Integrable fun w : ℝ ↦ exp (c ^ 2 / (2 * b)) * (|w| ^ n * exp (-(b / 2) * w ^ 2)) :=
    (integrable_abs_pow_mul_exp_neg_mul_sq (by positivity) n).const_mul _
  refine hmaj.mono' (by fun_prop) (.of_forall fun w ↦ ?_)
  have hkey : -b * w ^ 2 + c * |w| ≤ c ^ 2 / (2 * b) + -(b / 2) * w ^ 2 := by
    rw [← sub_nonneg, ← sq_abs w,
      show c ^ 2 / (2 * b) + -(b / 2) * |w| ^ 2 - (-b * |w| ^ 2 + c * |w|)
        = (b * |w| - c) ^ 2 / (2 * b) by field_simp; ring]
    positivity
  rw [norm_of_nonneg (by positivity)]
  calc |w| ^ n * exp (-b * w ^ 2 + c * |w|)
      ≤ |w| ^ n * exp (c ^ 2 / (2 * b) + -(b / 2) * w ^ 2) := by gcongr
    _ = exp (c ^ 2 / (2 * b)) * (|w| ^ n * exp (-(b / 2) * w ^ 2)) := by rw [exp_add]; ring
theorem integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs (hb : 0 < b) {A β : ℝ}
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (c : ℝ) (n : ℕ) :
    Integrable fun w : ℝ ↦ (A + β * |w|) ^ n * exp (-b * w ^ 2 + c * |w|) := by
  have h0 : Integrable fun w : ℝ ↦ exp (-b * w ^ 2 + c * |w|) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs hb c 0
  have hn : Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2 + c * |w|) :=
    integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs hb c n
  have hmaj : Integrable fun w : ℝ ↦ 2 ^ (n - 1) * (A ^ n * exp (-b * w ^ 2 + c * |w|)
      + β ^ n * (|w| ^ n * exp (-b * w ^ 2 + c * |w|))) :=
    ((h0.const_mul (A ^ n)).add (hn.const_mul (β ^ n))).const_mul _
  refine hmaj.mono' (by fun_prop) (.of_forall fun w ↦ ?_)
  rw [norm_of_nonneg (by positivity)]
  calc (A + β * |w|) ^ n * exp (-b * w ^ 2 + c * |w|)
      ≤ 2 ^ (n - 1) * (A ^ n + (β * |w|) ^ n) * exp (-b * w ^ 2 + c * |w|) := by
        gcongr
        exact add_pow_le hA (by positivity) n
    _ = 2 ^ (n - 1) * (A ^ n * exp (-b * w ^ 2 + c * |w|)
          + β ^ n * (|w| ^ n * exp (-b * w ^ 2 + c * |w|))) := by rw [mul_pow]; ring
private theorem tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (hb : 0 < b) (n : ℕ) :
    Filter.Tendsto (fun w : ℝ ↦ w ^ n * exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun x : ℝ ↦ exp (-(1 / 2) * x)) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun x : ℝ ↦ -(1 / 2) * x) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (by norm_num)
    exact tendsto_exp_atBot.comp h
  refine ((rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb
    ((n : ℝ))).isBigO.trans_tendsto hexp).congr fun x ↦ ?_
  rw [rpow_natCast]
theorem integral_Ioi_mul_exp_neg_mul_sq (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Ioi c, w * exp (-b * w ^ 2) = exp (-b * c ^ 2) / (2 * b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt (fun w : ℝ ↦ -exp (-b * w ^ 2))
      (2 * b * (w * exp (-b * w ^ 2))) w := by
    intro w
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2))
        (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    rw [show 2 * b * (w * exp (-b * w ^ 2)) = -(exp (-b * w ^ 2) * (-b * (2 * w))) by ring]
    exact h2.neg
  have hlim : Filter.Tendsto (fun w : ℝ ↦ -exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 0).neg
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := c)
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x)
    ((integrable_mul_exp_neg_mul_sq hb).const_mul (2 * b)).integrableOn hlim
  rw [integral_const_mul, zero_sub, neg_neg] at key
  rw [eq_div_iff (by positivity : (2 : ℝ) * b ≠ 0)]
  linear_combination key
theorem integral_Ioi_pow_add_two_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    ∫ w in Set.Ioi (0 : ℝ), w ^ (n + 2) * exp (-b * w ^ 2)
      = ((n : ℝ) + 1) / (2 * b) * ∫ w in Set.Ioi (0 : ℝ), w ^ n * exp (-b * w ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt (fun w : ℝ ↦ -(w ^ (n + 1) * exp (-b * w ^ 2)))
      (2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
        - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ ↦ w ^ (n + 1)) (((n : ℝ) + 1) * w ^ n) w := by
      simpa using hasDerivAt_pow (n + 1) w
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2))
        (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    rw [show 2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
        - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))
        = -(((n : ℝ) + 1) * w ^ n * exp (-b * w ^ 2)
          + w ^ (n + 1) * (exp (-b * w ^ 2) * (-b * (2 * w)))) by ring]
    exact (h1.mul h2).neg
  have hint : IntegrableOn (fun w : ℝ ↦ 2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
      - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))) (Set.Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul_sq hb (n + 2)).const_mul _).sub
      ((integrableOn_pow_mul_exp_neg_mul_sq hb n).const_mul _)
  have hlim : Filter.Tendsto (fun w : ℝ ↦ -(w ^ (n + 1) * exp (-b * w ^ 2)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb (n + 1)).neg
  have key := integral_Ioi_of_hasDerivAt_of_tendsto
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x) hint hlim
  rw [integral_sub ((integrableOn_pow_mul_exp_neg_mul_sq hb (n + 2)).const_mul _)
    ((integrableOn_pow_mul_exp_neg_mul_sq hb n).const_mul _), integral_const_mul,
    integral_const_mul] at key
  rw [show -((0 : ℝ) ^ (n + 1) * exp (-b * (0 : ℝ) ^ 2)) = 0 by simp, sub_zero] at key
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity : (2 : ℝ) * b ≠ 0)]
  linear_combination key
private theorem integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul (n : ℕ) :
    ∫ w : ℝ, |w| ^ n * exp (-b * w ^ 2)
      = 2 * ∫ w in Set.Ioi (0 : ℝ), w ^ n * exp (-b * w ^ 2) := by
  have h := integral_comp_abs (f := fun u : ℝ ↦ u ^ n * exp (-b * u ^ 2))
  simp only [sq_abs] at h
  exact h
theorem integral_abs_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, |w| * exp (-b * w ^ 2) = 1 / b := by
  have h := integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul (b := b) 1
  simp only [pow_one] at h
  rw [h, integral_Ioi_mul_exp_neg_mul_sq hb 0, show -b * (0 : ℝ) ^ 2 = 0 by ring, Real.exp_zero]
  field_simp
theorem integral_abs_pow_add_two_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    ∫ w : ℝ, |w| ^ (n + 2) * exp (-b * w ^ 2)
      = ((n : ℝ) + 1) / (2 * b) * ∫ w : ℝ, |w| ^ n * exp (-b * w ^ 2) := by
  rw [integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul,
    integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul,
    integral_Ioi_pow_add_two_mul_exp_neg_mul_sq hb n]
  ring
theorem integral_abs_pow_even_mul_exp_neg_mul_sq (hb : 0 < b) (m : ℕ) :
    ∫ w : ℝ, |w| ^ (2 * m) * exp (-b * w ^ 2)
      = (2 * m)! / (4 ^ m * m !) * (√(π / b) / b ^ m) := by
  induction m with
  | zero => simpa using integral_gaussian b
  | succ m ih =>
      have hb0 : b ≠ 0 := hb.ne'
      have hm : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
      have hfac : ((2 * m + 2)! : ℝ) = ((2 : ℝ) * m + 2) * (2 * m + 1) * (2 * m)! := by
        rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, integral_abs_pow_add_two_mul_exp_neg_mul_sq hb,
        ih, hfac, Nat.factorial_succ]
      push_cast
      field_simp
      ring
theorem integral_abs_pow_odd_mul_exp_neg_mul_sq (hb : 0 < b) (m : ℕ) :
    ∫ w : ℝ, |w| ^ (2 * m + 1) * exp (-b * w ^ 2) = m ! / b ^ (m + 1) := by
  induction m with
  | zero => simpa using integral_abs_mul_exp_neg_mul_sq hb
  | succ m ih =>
      have hb0 : b ≠ 0 := hb.ne'
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring,
        integral_abs_pow_add_two_mul_exp_neg_mul_sq hb, ih, Nat.factorial_succ]
      push_cast
      field_simp
      ring
theorem integral_sq_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 2 * exp (-b * w ^ 2) = √(π / b) / (2 * b) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 1
  simp only [show 2 * 1 = 2 from rfl, sq_abs, pow_one, Nat.factorial] at h
  rw [h]
  push_cast
  field_simp
  ring
private theorem even_four : Even 4 := ⟨2, rfl⟩
private theorem even_six : Even 6 := ⟨3, rfl⟩
theorem integral_pow_four_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 4 * exp (-b * w ^ 2) = 3 * √(π / b) / (4 * b ^ 2) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 2
  simp only [show 2 * 2 = 4 from rfl, even_four.pow_abs] at h
  rw [h, show ((4 : ℕ)! : ℝ) = 24 by norm_num [Nat.factorial],
    show ((2 : ℕ)! : ℝ) = 2 by norm_num [Nat.factorial]]
  field_simp
  ring
theorem integral_pow_six_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 6 * exp (-b * w ^ 2) = 15 * √(π / b) / (8 * b ^ 3) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 3
  simp only [show 2 * 3 = 6 from rfl, even_six.pow_abs] at h
  rw [h, show ((6 : ℕ)! : ℝ) = 720 by norm_num [Nat.factorial],
    show ((3 : ℕ)! : ℝ) = 6 by norm_num [Nat.factorial]]
  field_simp
  ring
theorem integral_abs_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, |w| ^ 3 * exp (-b * w ^ 2) = 1 / b ^ 2 := by
  simpa using integral_abs_pow_odd_mul_exp_neg_mul_sq hb 1
theorem integral_Ioi_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in Set.Ioi c, exp (-b * w ^ 2) ≤ exp (-b * c ^ 2) / (2 * b * c) := by
  have h1 : IntegrableOn (fun w : ℝ ↦ exp (-b * w ^ 2)) (Set.Ioi c) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have h2 : IntegrableOn (fun w : ℝ ↦ c⁻¹ * (w * exp (-b * w ^ 2))) (Set.Ioi c) :=
    ((integrable_mul_exp_neg_mul_sq hb).const_mul c⁻¹).integrableOn
  calc ∫ w in Set.Ioi c, exp (-b * w ^ 2)
      ≤ ∫ w in Set.Ioi c, c⁻¹ * (w * exp (-b * w ^ 2)) := by
        refine setIntegral_mono_on h1 h2 measurableSet_Ioi fun w hw ↦ ?_
        have hcw : (1 : ℝ) ≤ c⁻¹ * w := by
          rw [← div_eq_inv_mul]
          exact (one_le_div hc).2 (le_of_lt hw)
        calc exp (-b * w ^ 2) = 1 * exp (-b * w ^ 2) := (one_mul _).symm
          _ ≤ c⁻¹ * w * exp (-b * w ^ 2) :=
              mul_le_mul_of_nonneg_right hcw (exp_pos _).le
          _ = c⁻¹ * (w * exp (-b * w ^ 2)) := by ring
    _ = exp (-b * c ^ 2) / (2 * b * c) := by
        rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hb c]
        field_simp
theorem integral_Ioi_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Ioi c, w ^ 3 * exp (-b * w ^ 2)
      = exp (-b * c ^ 2) * (c ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt
      (fun w : ℝ ↦ -((w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) * exp (-b * w ^ 2)))
      (w ^ 3 * exp (-b * w ^ 2)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ ↦ w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) (2 * w / (2 * b)) w := by
      simpa using ((hasDerivAt_pow 2 w).div_const (2 * b)).add_const (1 / (2 * b ^ 2))
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2)) (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    refine (h1.mul h2).neg.congr_deriv ?_
    field_simp
    ring
  have hint : Integrable fun w : ℝ ↦ w ^ 3 * exp (-b * w ^ 2) := by
    refine (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).mono' (by fun_prop)
      (.of_forall fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (exp_pos _).le]
  have hlim : Filter.Tendsto
      (fun w : ℝ ↦ -((w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) * exp (-b * w ^ 2)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun w : ℝ ↦ exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
      simpa using tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 0
    have h := ((tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 2).const_mul
      (-(1 / (2 * b)))).add (h0.const_mul (-(1 / (2 * b ^ 2))))
    rw [show -(1 / (2 * b)) * (0 : ℝ) + -(1 / (2 * b ^ 2)) * 0 = 0 by ring] at h
    exact h.congr fun w ↦ by ring
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := c)
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x) hint.integrableOn hlim
  rw [key, zero_sub, neg_neg]
  ring
private theorem lt_abs_of_mem_compl_Icc {c w : ℝ} (hw : w ∈ (Set.Icc (-c) c)ᶜ) : c < |w| := by
  rwa [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le] at hw
theorem integral_compl_Icc_eq_two_mul_integral_Ioi {f : ℝ → ℝ} (hf : Integrable f)
    (hfe : ∀ w : ℝ, f (-w) = f w) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, f w = 2 * ∫ w in Set.Ioi c, f w := by
  have hcompl : (Set.Icc (-c) c)ᶜ = Set.Iio (-c) ∪ Set.Ioi c := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-c)) (Set.Ioi c) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have h1 : w < -c := hw
    have h2 : c < w := hw'
    linarith
  have hIio : ∫ w in Set.Iio (-c), f w = ∫ w in Set.Ioi c, f w := by
    have h := integral_comp_neg_Iic (-c) f
    rw [neg_neg] at h
    rw [← integral_Iic_eq_integral_Iio, ← h]
    exact setIntegral_congr_fun measurableSet_Iic fun w _ ↦ (hfe w).symm
  rw [hcompl, setIntegral_union hdisj measurableSet_Ioi hf.integrableOn hf.integrableOn, hIio]
  ring
theorem integral_compl_Icc_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, exp (-b * w ^ 2) ≤ exp (-b * c ^ 2) / (b * c) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hc0 : c ≠ 0 := hc.ne'
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi (integrable_exp_neg_mul_sq hb)
    (fun w ↦ by rw [neg_sq]) hc.le]
  have heq : 2 * (exp (-b * c ^ 2) / (2 * b * c)) = exp (-b * c ^ 2) / (b * c) := by
    field_simp
  linarith [integral_Ioi_exp_neg_mul_sq_le hb hc]
theorem integral_compl_Icc_abs_mul_exp_neg_mul_sq (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, |w| * exp (-b * w ^ 2) = exp (-b * c ^ 2) / b := by
  have hb0 : b ≠ 0 := hb.ne'
  have hint : Integrable fun w : ℝ ↦ |w| * exp (-b * w ^ 2) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_sq hb 1
  have hIoi : ∫ w in Set.Ioi c, |w| * exp (-b * w ^ 2) = ∫ w in Set.Ioi c, w * exp (-b * w ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      rw [abs_of_pos (lt_of_le_of_lt hc hw)]
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi hint (fun w ↦ by rw [abs_neg, neg_sq]) hc, hIoi,
    integral_Ioi_mul_exp_neg_mul_sq hb c]
  field_simp
theorem integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, |w| ^ 3 * exp (-b * w ^ 2)
      = exp (-b * c ^ 2) * (c ^ 2 / b + 1 / b ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hint : Integrable fun w : ℝ ↦ |w| ^ 3 * exp (-b * w ^ 2) :=
    integrable_abs_pow_mul_exp_neg_mul_sq hb 3
  have hIoi : ∫ w in Set.Ioi c, |w| ^ 3 * exp (-b * w ^ 2)
      = ∫ w in Set.Ioi c, w ^ 3 * exp (-b * w ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      rw [abs_of_pos (lt_of_le_of_lt hc hw)]
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi hint (fun w ↦ by rw [abs_neg, neg_sq]) hc, hIoi,
    integral_Ioi_pow_three_mul_exp_neg_mul_sq hb c]
  ring
theorem integral_compl_Icc_sq_mul_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, w ^ 2 * exp (-b * w ^ 2)
      ≤ exp (-b * c ^ 2) * (c / b + 1 / (b ^ 2 * c)) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have h2 : IntegrableOn (fun w : ℝ ↦ w ^ 2 * exp (-b * w ^ 2)) (Set.Icc (-c) c)ᶜ := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).integrableOn
  have h3 : IntegrableOn (fun w : ℝ ↦ c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2))) (Set.Icc (-c) c)ᶜ :=
    ((integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c⁻¹).integrableOn
  calc ∫ w in (Set.Icc (-c) c)ᶜ, w ^ 2 * exp (-b * w ^ 2)
      ≤ ∫ w in (Set.Icc (-c) c)ᶜ, c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2)) := by
        refine setIntegral_mono_on h2 h3 measurableSet_Icc.compl fun w hw ↦ ?_
        have hwc : c ≤ |w| := (lt_abs_of_mem_compl_Icc hw).le
        have hpow : w ^ 2 ≤ c⁻¹ * |w| ^ 3 := by
          rw [← sq_abs w, inv_mul_eq_div, le_div_iff₀ hc]
          nlinarith [abs_nonneg w]
        calc w ^ 2 * exp (-b * w ^ 2) ≤ c⁻¹ * |w| ^ 3 * exp (-b * w ^ 2) :=
              mul_le_mul_of_nonneg_right hpow (exp_pos _).le
          _ = c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2)) := by ring
    _ = c⁻¹ * (exp (-b * c ^ 2) * (c ^ 2 / b + 1 / b ^ 2)) := by
        rw [integral_const_mul, integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq hb hc.le]
    _ = exp (-b * c ^ 2) * (c / b + 1 / (b ^ 2 * c)) := by
        field_simp
private theorem exp_neg_mul_sq_mul_poly_eq (b c₀ c₁ c₂ c₃ : ℝ) :
    (fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3))
      = fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
          + c₂ * (w ^ 2 * exp (-b * w ^ 2)) + c₃ * (|w| ^ 3 * exp (-b * w ^ 2)) := by
  funext w
  ring
theorem integrable_exp_neg_mul_sq_mul_poly (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3) := by
  rw [exp_neg_mul_sq_mul_poly_eq]
  refine (((((integrable_exp_neg_mul_sq hb).const_mul c₀).add ?_).add ?_).add ?_)
  · simpa using (integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁
  · simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  · exact (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃
theorem integral_exp_neg_mul_sq_mul_poly (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ w : ℝ, exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3)
      = c₀ * √(π / b) + c₁ / b + c₂ * (√(π / b) / (2 * b)) + c₃ / b ^ 2 := by
  have e0 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul c₀
  have e1 : Integrable fun w : ℝ ↦ c₁ * (|w| * exp (-b * w ^ 2)) := by
    simpa using (integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁
  have e2 : Integrable fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2)) := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  have e3 : Integrable fun w : ℝ ↦ c₃ * (|w| ^ 3 * exp (-b * w ^ 2)) :=
    (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃
  have e01 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2)) :=
    e0.add e1
  have e012 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
      + c₂ * (w ^ 2 * exp (-b * w ^ 2)) := e01.add e2
  rw [exp_neg_mul_sq_mul_poly_eq, integral_add e012 e3, integral_add e01 e2, integral_add e0 e1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_gaussian, integral_abs_mul_exp_neg_mul_sq hb, integral_sq_mul_exp_neg_mul_sq hb,
    integral_abs_pow_three_mul_exp_neg_mul_sq hb]
  ring
theorem integral_compl_Icc_exp_neg_mul_sq_mul_poly_le (hb : 0 < b) {A : ℝ} (hA : 0 < A)
    (hbA : 1 ≤ b * A ^ 2) {c₀ c₁ c₂ c₃ : ℝ} (h₀ : 0 ≤ c₀) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) :
    ∫ w in (Set.Icc (-A) A)ᶜ, exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3)
      ≤ exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hA0 : A ≠ 0 := hA.ne'
  have hE : (0 : ℝ) < exp (-b * A ^ 2) := exp_pos _
  set s : Set ℝ := (Set.Icc (-A) A)ᶜ with hs
  have e0 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2)) s :=
    ((integrable_exp_neg_mul_sq hb).const_mul c₀).integrableOn
  have e1 : IntegrableOn (fun w : ℝ ↦ c₁ * (|w| * exp (-b * w ^ 2))) s := by
    simpa using ((integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁).integrableOn
  have e2 : IntegrableOn (fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2))) s := by
    simpa [sq_abs] using ((integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂).integrableOn
  have e3 : IntegrableOn (fun w : ℝ ↦ c₃ * (|w| ^ 3 * exp (-b * w ^ 2))) s :=
    ((integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃).integrableOn
  have e01 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))) s :=
    e0.add e1
  have e012 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
      + c₂ * (w ^ 2 * exp (-b * w ^ 2))) s := e01.add e2
  have b0 : ∫ w in s, c₀ * exp (-b * w ^ 2) ≤ c₀ * (exp (-b * A ^ 2) / (b * A)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le hb hA) h₀
  have b1 : ∫ w in s, c₁ * (|w| * exp (-b * w ^ 2)) = c₁ * (exp (-b * A ^ 2) / b) := by
    rw [integral_const_mul, integral_compl_Icc_abs_mul_exp_neg_mul_sq hb hA.le]
  have b2 : ∫ w in s, c₂ * (w ^ 2 * exp (-b * w ^ 2))
      ≤ c₂ * (exp (-b * A ^ 2) * (A / b + 1 / (b ^ 2 * A))) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_compl_Icc_sq_mul_exp_neg_mul_sq_le hb hA) h₂
  have b3 : ∫ w in s, c₃ * (|w| ^ 3 * exp (-b * w ^ 2))
      = c₃ * (exp (-b * A ^ 2) * (A ^ 2 / b + 1 / b ^ 2)) := by
    rw [integral_const_mul, integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq hb hA.le]
  have hd2 : 1 / (b ^ 2 * A) ≤ A / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith
  have hd3 : 1 / b ^ 2 ≤ A ^ 2 / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith
  have g2 : c₂ * (exp (-b * A ^ 2) * (A / b + 1 / (b ^ 2 * A)))
      ≤ c₂ * (exp (-b * A ^ 2) * (2 * A / b)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE.le) h₂
    rw [show 2 * A / b = A / b + A / b by ring]
    linarith
  have g3 : c₃ * (exp (-b * A ^ 2) * (A ^ 2 / b + 1 / b ^ 2))
      ≤ c₃ * (exp (-b * A ^ 2) * (2 * A ^ 2 / b)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE.le) h₃
    rw [show 2 * A ^ 2 / b = A ^ 2 / b + A ^ 2 / b by ring]
    linarith
  have hsum : c₀ * (exp (-b * A ^ 2) / (b * A)) + c₁ * (exp (-b * A ^ 2) / b)
      + c₂ * (exp (-b * A ^ 2) * (2 * A / b)) + c₃ * (exp (-b * A ^ 2) * (2 * A ^ 2 / b))
      = exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
    field_simp
  rw [exp_neg_mul_sq_mul_poly_eq, integral_add e012 e3, integral_add e01 e2, integral_add e0 e1]
  linarith
private theorem setIntegral_comp_add_right_le_of_nonneg {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ u : ℝ, 0 ≤ f u) {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) (d : ℝ)
    (hst : ∀ w ∈ s, w + d ∈ t) :
    ∫ w in s, f (w + d) ≤ ∫ u in t, f u := by
  have hR : ∫ w : ℝ, t.indicator f (w + d) = ∫ u : ℝ, t.indicator f u :=
    integral_add_right_eq_self (t.indicator f) d
  rw [← integral_indicator hs, ← integral_indicator ht, ← hR]
  refine integral_mono ((hf.comp_add_right d).indicator hs)
    ((hf.indicator ht).comp_add_right d) fun w ↦ ?_
  by_cases hw : w ∈ s
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hst w hw)]
  · rw [Set.indicator_of_notMem hw]
    exact Set.indicator_nonneg (fun u _ ↦ hf0 u) _
theorem integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le (hb : 0 < b) {W d A : ℝ}
    (hA : 0 < A) (hAW : A + |d| ≤ W) (hbA : 1 ≤ b * A ^ 2) {c₀ c₁ c₂ c₃ : ℝ} (h₀ : 0 ≤ c₀)
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) :
    ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₁ * |w + d| + c₂ * (w + d) ^ 2 + c₃ * |w + d| ^ 3)
      ≤ exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
  refine le_trans (setIntegral_comp_add_right_le_of_nonneg
    (integrable_exp_neg_mul_sq_mul_poly hb c₀ c₁ c₂ c₃)
    (fun u ↦ by positivity) measurableSet_Icc.compl measurableSet_Icc.compl d fun w hw ↦ ?_)
    (integral_compl_Icc_exp_neg_mul_sq_mul_poly_le hb hA hbA h₀ h₂ h₃)
  have hwW : W < |w| := lt_abs_of_mem_compl_Icc hw
  have hshift : A < |w + d| := by
    have h := abs_sub_abs_le_abs_sub w (-d)
    rw [abs_neg, sub_neg_eq_add] at h
    linarith
  rw [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
  exact hshift
theorem integral_compl_Icc_exp_neg_mul_sq_comp_add_right_le (hb : 0 < b) {W d A : ℝ} (hA : 0 < A)
    (hAW : A + |d| ≤ W) (hbA : 1 ≤ b * A ^ 2) :
    ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2) ≤ exp (-b * A ^ 2) / (b * A) := by
  have h := integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le hb hA hAW hbA
    (c₀ := 1) (c₁ := 0) (c₂ := 0) (c₃ := 0) zero_le_one le_rfl le_rfl le_rfl
  simp only [mul_zero, zero_mul, add_zero, mul_one] at h
  calc ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2)
      ≤ exp (-b * A ^ 2) / b * (1 / A) := h
    _ = exp (-b * A ^ 2) / (b * A) := by ring
private theorem exp_neg_mul_sq_mul_even_poly_eq (b c₀ c₂ c₄ c₆ : ℝ) :
    (fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6))
      = fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2))
          + c₄ * (w ^ 4 * exp (-b * w ^ 2)) + c₆ * (w ^ 6 * exp (-b * w ^ 2)) := by
  funext w
  ring
theorem integrable_exp_neg_mul_sq_mul_even_poly (hb : 0 < b) (c₀ c₂ c₄ c₆ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6) := by
  rw [exp_neg_mul_sq_mul_even_poly_eq]
  refine ((((integrable_exp_neg_mul_sq hb).const_mul c₀).add ?_).add ?_).add ?_
  · simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  · simpa [even_four.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 4).const_mul c₄
  · simpa [even_six.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 6).const_mul c₆
theorem integral_exp_neg_mul_sq_mul_even_poly (hb : 0 < b) (c₀ c₂ c₄ c₆ : ℝ) :
    ∫ w : ℝ, exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2) + 15 * c₆ / (8 * b ^ 3)) * √(π / b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have e0 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul c₀
  have e2 : Integrable fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2)) := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  have e4 : Integrable fun w : ℝ ↦ c₄ * (w ^ 4 * exp (-b * w ^ 2)) := by
    simpa [even_four.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 4).const_mul c₄
  have e6 : Integrable fun w : ℝ ↦ c₆ * (w ^ 6 * exp (-b * w ^ 2)) := by
    simpa [even_six.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 6).const_mul c₆
  have e02 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2)) :=
    e0.add e2
  have e024 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2))
      + c₄ * (w ^ 4 * exp (-b * w ^ 2)) := e02.add e4
  rw [exp_neg_mul_sq_mul_even_poly_eq, integral_add e024 e6, integral_add e02 e4,
    integral_add e0 e2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gaussian, integral_sq_mul_exp_neg_mul_sq hb,
    integral_pow_four_mul_exp_neg_mul_sq hb, integral_pow_six_mul_exp_neg_mul_sq hb]
  field_simp
theorem integral_exp_neg_mul_sq_mul_even_poly_comp_add_right (hb : 0 < b) (c₀ c₂ c₄ c₆ d : ℝ) :
    ∫ w : ℝ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4 + c₆ * (w + d) ^ 6)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2) + 15 * c₆ / (8 * b ^ 3)) * √(π / b) := by
  rw [show (∫ w : ℝ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4 + c₆ * (w + d) ^ 6))
      = ∫ w : ℝ, (fun u : ℝ ↦ exp (-b * u ^ 2) *
        (c₀ + c₂ * u ^ 2 + c₄ * u ^ 4 + c₆ * u ^ 6)) (w + d) from rfl,
    integral_add_right_eq_self (fun u : ℝ ↦ exp (-b * u ^ 2) *
      (c₀ + c₂ * u ^ 2 + c₄ * u ^ 4 + c₆ * u ^ 6)) d,
    integral_exp_neg_mul_sq_mul_even_poly hb]
theorem integrable_exp_neg_mul_sq_mul_even_quartic (hb : 0 < b) (c₀ c₂ c₄ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4) := by
  simpa using integrable_exp_neg_mul_sq_mul_even_poly hb c₀ c₂ c₄ 0
theorem integral_exp_neg_mul_sq_mul_even_quartic_comp_add_right (hb : 0 < b) (c₀ c₂ c₄ d : ℝ) :
    ∫ w : ℝ, exp (-b * (w + d) ^ 2) * (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2)) * √(π / b) := by
  simpa using integral_exp_neg_mul_sq_mul_even_poly_comp_add_right hb c₀ c₂ c₄ 0 d
end Moments
end
end CertificatePort88


