-- Prove2me | solution 1 for AnalyticGeometry.zLaurentGT_isSubring
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:43:29.236297+00:00
-- url     : https://prove2.me/submissions/9044633b-dda1-47b5-b2fe-e0bd74f8c2a1

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

set_option autoImplicit false

open Filter Topology

theorem pc2b_mono {s t : ℝ} {f : LaurentSeries ℤ} (ht : 0 < t) (hts : t ≤ s)
    (h : AnalyticGeometry.DecaysAt s f) : AnalyticGeometry.DecaysAt t f := by
  unfold AnalyticGeometry.DecaysAt at *
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (abs_nonneg _)
    (zpow_nonneg ht.le _)) ?_ h
  filter_upwards [eventually_ge_atTop (0:ℤ)] with n hn
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hn ht.le hts) (abs_nonneg _)

theorem pc2b_add {s : ℝ} {f g : LaurentSeries ℤ} (hs : 0 < s)
    (hf : AnalyticGeometry.DecaysAt s f) (hg : AnalyticGeometry.DecaysAt s g) :
    AnalyticGeometry.DecaysAt s (f + g) := by
  unfold AnalyticGeometry.DecaysAt at *
  have hsum := hf.add hg
  rw [add_zero] at hsum
  refine squeeze_zero (fun n => mul_nonneg (abs_nonneg _) (zpow_nonneg hs.le _)) (fun n => ?_) hsum
  rw [HahnSeries.coeff_add, Int.cast_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (zpow_nonneg hs.le _)

theorem pc2b_neg {s : ℝ} {f : LaurentSeries ℤ}
    (hf : AnalyticGeometry.DecaysAt s f) : AnalyticGeometry.DecaysAt s (-f) := by
  unfold AnalyticGeometry.DecaysAt at *
  simpa only [HahnSeries.coeff_neg, Int.cast_neg, abs_neg] using hf

theorem pc2b_zero (s : ℝ) : AnalyticGeometry.DecaysAt s (0 : LaurentSeries ℤ) := by
  unfold AnalyticGeometry.DecaysAt
  simp only [HahnSeries.coeff_zero, Int.cast_zero, abs_zero, zero_mul]
  exact tendsto_const_nhds

theorem pc2b_one (s : ℝ) : AnalyticGeometry.DecaysAt s (1 : LaurentSeries ℤ) := by
  unfold AnalyticGeometry.DecaysAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℤ)] with n hn
  rw [HahnSeries.coeff_one, if_neg hn.ne']
  simp

theorem pc2b_bdd {s : ℝ} {f : LaurentSeries ℤ} (hf : AnalyticGeometry.DecaysAt s f) :
    ∃ C : ℝ, ∀ n : ℤ, |(f.coeff n : ℝ)| * s ^ n ≤ C := by
  unfold AnalyticGeometry.DecaysAt at hf
  have hc : Tendsto (fun n : ℤ => |(f.coeff n : ℝ)| * s ^ n) cofinite (𝓝 0) := by
    rw [Int.cofinite_eq, tendsto_sup]
    refine ⟨?_, hf⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot f.order] with n hn
    rw [HahnSeries.coeff_eq_zero_of_lt_order hn]
    simp
  obtain ⟨C, hC⟩ := hc.bddAbove_range_of_cofinite
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

theorem pc2b_lim {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c : ℝ) :
    Tendsto (fun n : ℤ => ((n : ℝ) + c) * q ^ n) atTop (𝓝 0) := by
  rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
  have h1 := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul c
  have h3 := h1.add h2
  rw [mul_zero, add_zero] at h3
  refine h3.congr (fun k => ?_)
  simp only [Function.comp_apply, Int.cast_natCast, zpow_natCast]
  ring

theorem pc2b_card (f g : LaurentSeries ℤ) (n : ℤ) :
    ((Finset.antidiagonal f.isPWO_support g.isPWO_support n).card : ℤ) ≤
      max (n + 1 - 2 * min f.order g.order) 0 := by
  set m := min f.order g.order with hm
  have hle : (Finset.antidiagonal f.isPWO_support g.isPWO_support n).card ≤
      (Finset.Icc m (n - m)).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro ij hij
      rw [Finset.mem_coe, Finset.mem_antidiagonal] at hij
      obtain ⟨h1, h2, h3⟩ := hij
      have o1 : f.order ≤ ij.1 := HahnSeries.order_le_of_coeff_ne_zero h1
      have o2 : g.order ≤ ij.2 := HahnSeries.order_le_of_coeff_ne_zero h2
      rw [Finset.mem_coe, Finset.mem_Icc]
      constructor
      · exact le_trans (min_le_left _ _) o1
      · have : m ≤ ij.2 := le_trans (min_le_right _ _) o2
        omega
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_antidiagonal] at ha hb
      have : a.2 = b.2 := by
        have := ha.2.2
        have := hb.2.2
        have : a.1 = b.1 := hab
        omega
      exact Prod.ext hab this
  rw [Int.card_Icc] at hle
  have : ((n - m + 1 - m).toNat : ℤ) = max (n - m + 1 - m) 0 := Int.toNat_eq_max _
  have h2 : ((Finset.antidiagonal f.isPWO_support g.isPWO_support n).card : ℤ) ≤
      ((n - m + 1 - m).toNat : ℤ) := by exact_mod_cast hle
  rw [this] at h2
  have e : n - m + 1 - m = n + 1 - 2 * m := by ring
  rw [e] at h2
  exact h2

theorem pc2b_mul {s t : ℝ} {f g : LaurentSeries ℤ} (ht : 0 < t) (hts : t < s)
    (hf : AnalyticGeometry.DecaysAt s f) (hg : AnalyticGeometry.DecaysAt s g) :
    AnalyticGeometry.DecaysAt t (f * g) := by
  obtain ⟨C1, hC1⟩ := pc2b_bdd hf
  obtain ⟨C2, hC2⟩ := pc2b_bdd hg
  have hs : 0 < s := ht.trans hts
  have hC1n : 0 ≤ C1 := le_trans (mul_nonneg (abs_nonneg _) (zpow_nonneg hs.le _)) (hC1 0)
  have hC2n : 0 ≤ C2 := le_trans (mul_nonneg (abs_nonneg _) (zpow_nonneg hs.le _)) (hC2 0)
  have hq0 : 0 ≤ t / s := div_nonneg ht.le hs.le
  have hq1 : t / s < 1 := (div_lt_one hs).2 hts
  have key : ∀ n : ℤ, |((f * g).coeff n : ℝ)| * s ^ n ≤
      ((Finset.antidiagonal f.isPWO_support g.isPWO_support n).card : ℝ) * (C1 * C2) := by
    intro n
    rw [HahnSeries.coeff_mul, Int.cast_sum]
    calc _ ≤ (∑ ij ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support n,
            |((f.coeff ij.1 * g.coeff ij.2 : ℤ) : ℝ)|) * s ^ n :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (zpow_nonneg hs.le _)
      _ = ∑ ij ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support n,
            (|(f.coeff ij.1 : ℝ)| * s ^ ij.1) * (|(g.coeff ij.2 : ℝ)| * s ^ ij.2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun ij hij => ?_)
          rw [Finset.mem_antidiagonal] at hij
          rw [← hij.2.2, zpow_add₀ hs.ne', Int.cast_mul, abs_mul]
          ring
      _ ≤ ∑ ij ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support n, C1 * C2 :=
          Finset.sum_le_sum (fun ij _ => mul_le_mul (hC1 _) (hC2 _)
            (mul_nonneg (abs_nonneg _) (zpow_nonneg hs.le _)) hC1n)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  unfold AnalyticGeometry.DecaysAt
  set m := min f.order g.order with hm
  have hlim := (pc2b_lim hq0 hq1 (1 - 2 * (m : ℝ))).const_mul (C1 * C2)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (abs_nonneg _)
    (zpow_nonneg ht.le _)) ?_ hlim
  filter_upwards [eventually_ge_atTop (2 * m)] with n hn
  have hcard := pc2b_card f g n
  rw [← hm, max_eq_left (by omega)] at hcard
  have hcardR : ((Finset.antidiagonal f.isPWO_support g.isPWO_support n).card : ℝ) ≤
      (n : ℝ) + (1 - 2 * (m : ℝ)) := by
    have := (Int.cast_le (R := ℝ)).2 hcard
    push_cast at this
    linarith
  have htq : t ^ n = s ^ n * (t / s) ^ n := by
    rw [div_zpow, mul_div_cancel₀ _ (zpow_ne_zero n hs.ne')]
  calc |((f * g).coeff n : ℝ)| * t ^ n
        = (|((f * g).coeff n : ℝ)| * s ^ n) * (t / s) ^ n := by rw [htq]; ring
    _ ≤ (((Finset.antidiagonal f.isPWO_support g.isPWO_support n).card : ℝ) * (C1 * C2))
          * (t / s) ^ n := mul_le_mul_of_nonneg_right (key n) (zpow_nonneg hq0 _)
    _ ≤ (((n : ℝ) + (1 - 2 * (m : ℝ))) * (C1 * C2)) * (t / s) ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcardR
            (mul_nonneg hC1n hC2n)) (zpow_nonneg hq0 _)
    _ = C1 * C2 * (((n : ℝ) + (1 - 2 * (m : ℝ))) * (t / s) ^ n) := by ring

open AnalyticGeometry in
theorem solution (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ R : Subring (LaurentSeries ℤ), (R : Set (LaurentSeries ℤ)) = zLaurentGT r := by
  refine ⟨{ carrier := zLaurentGT r
            mul_mem' := fun {f g} hf hg => ?_
            one_mem' := ⟨(r + 1) / 2, by linarith, pc2b_one _⟩
            add_mem' := fun {f g} hf hg => ?_
            zero_mem' := ⟨(r + 1) / 2, by linarith, pc2b_zero _⟩
            neg_mem' := fun {f} hf => ?_ }, rfl⟩
  · obtain ⟨s1, hs1, hf⟩ := hf
    obtain ⟨s2, hs2, hg⟩ := hg
    have hr : r < min s1 s2 := lt_min hs1 hs2
    have hmpos : 0 < min s1 s2 := hr0.trans hr
    refine ⟨(r + min s1 s2) / 2, by linarith, ?_⟩
    exact pc2b_mul (by linarith) (by linarith) (pc2b_mono hmpos (min_le_left _ _) hf)
      (pc2b_mono hmpos (min_le_right _ _) hg)
  · obtain ⟨s1, hs1, hf⟩ := hf
    obtain ⟨s2, hs2, hg⟩ := hg
    have hr : r < min s1 s2 := lt_min hs1 hs2
    have hmpos : 0 < min s1 s2 := hr0.trans hr
    exact ⟨min s1 s2, hr, pc2b_add hmpos (pc2b_mono hmpos (min_le_left _ _) hf)
      (pc2b_mono hmpos (min_le_right _ _) hg)⟩
  · obtain ⟨s, hs, hf⟩ := hf
    exact ⟨s, hs, pc2b_neg hf⟩
