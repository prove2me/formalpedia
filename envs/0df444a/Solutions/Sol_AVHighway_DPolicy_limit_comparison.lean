-- Prove2me | solution 1 for AVHighway.DPolicy.limit_comparison
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:46:24.87265+00:00
-- url     : https://prove2.me/submissions/023a287c-9816-4ead-99d2-b35d506ed14f

import Mathlib
import Definitions.Def_AVHighway_DPolicy_Setting

set_option autoImplicit false
open AVHighway.DPolicy

theorem avh_wpos (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : n ≤ cap) :
    0 < weight L V lam n := by
  unfold weight
  apply div_pos (pow_pos (mul_pos hlam hL) _)
  exact mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
    (Finset.prod_pos fun k hk => hV k (Finset.mem_Icc.1 hk).1 (le_trans (Finset.mem_Icc.1 hk).2 hn))

theorem avh_shift (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (m : ℕ) (hm : m + 1 ≤ cap) :
    ((m + 1 : ℕ) : ℝ) * weight L V lam (m + 1) = lam * L * weight L V lam m / V (m + 1) := by
  have hVm : 0 < V (m + 1) := hV (m + 1) (by omega) hm
  have hP : 0 < ∏ k ∈ Finset.Icc 1 m, V k :=
    Finset.prod_pos fun k hk => hV k (Finset.mem_Icc.1 hk).1 (by have := (Finset.mem_Icc.1 hk).2; omega)
  have hf : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  unfold weight
  rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem avh_key (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (hlam : 0 < lam) :
    meanTravelTime L V cap lam =
      L * (∑ n ∈ Finset.range cap, weight L V lam n / V (n + 1)) /
        ∑ n ∈ Finset.range cap, weight L V lam n := by
  have hw := avh_wpos L hL V cap hV lam hlam
  have hS : 0 < ∑ n ∈ Finset.range cap, weight L V lam n :=
    Finset.sum_pos (fun n hn => hw n (by have := Finset.mem_range.1 hn; omega))
      ⟨0, Finset.mem_range.2 (by omega)⟩
  have hZ : ∑ m ∈ Finset.range (cap + 1), weight L V lam m
      = ∑ n ∈ Finset.range cap, weight L V lam n + weight L V lam cap := Finset.sum_range_succ _ _
  have hZpos : 0 < ∑ m ∈ Finset.range (cap + 1), weight L V lam m := by
    rw [hZ]; exact add_pos hS (hw cap le_rfl)
  have hnum : ∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * weight L V lam n
      = lam * L * ∑ n ∈ Finset.range cap, weight L V lam n / V (n + 1) := by
    have h1 : ∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * weight L V lam n
        = ∑ n ∈ Finset.range cap, ((n + 1 : ℕ) : ℝ) * weight L V lam (n + 1) := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) * weight L V lam n) 0 cap 1]
      rfl
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [avh_shift L hL V cap hV lam m (by have := Finset.mem_range.1 hm; omega)]
    ring
  unfold meanTravelTime throughput stationary
  have : ∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * (weight L V lam n / ∑ m ∈ Finset.range (cap + 1), weight L V lam m)
      = (∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * weight L V lam n) /
        ∑ m ∈ Finset.range (cap + 1), weight L V lam m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [this, hnum]
  rw [hZ] at hZpos ⊢
  have hS' := hS.ne'
  have hZ' := hZpos.ne'
  have h3 : 1 - weight L V lam cap / (∑ n ∈ Finset.range cap, weight L V lam n + weight L V lam cap)
      = (∑ n ∈ Finset.range cap, weight L V lam n) /
        (∑ n ∈ Finset.range cap, weight L V lam n + weight L V lam cap) := by
    field_simp
    ring
  rw [h3]
  field_simp

theorem avh_eq20 (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) :
    Filter.Tendsto (meanTravelTime L V cap) Filter.atTop (nhds (L / V cap)) := by
  obtain ⟨c, rfl⟩ : ∃ c, cap = c + 1 := ⟨cap - 1, by omega⟩
  set cc : ℕ → ℝ := fun m => 1 / ((m.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 m, V k) with hcc
  set a : ℕ → ℝ := fun m => 1 / V (m + 1) with ha
  have hccpos : ∀ m, m ≤ c + 1 → 0 < cc m := by
    intro m hm
    simp only [hcc]
    apply one_div_pos.2
    exact mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
      (Finset.prod_pos fun k hk => hV k (Finset.mem_Icc.1 hk).1 (by have := (Finset.mem_Icc.1 hk).2; omega))
  have hw : ∀ (l : ℝ) (m : ℕ), weight L V l m = (l * L) ^ m * cc m := by
    intro l m; simp only [weight, hcc]; rw [div_eq_mul_one_div]
  have hcpos : 0 < cc c := hccpos c (by omega)
  -- the rescaled weights
  set u : ℝ → ℕ → ℝ := fun t m => cc m / cc c * t ^ (c - m) with hu
  set F : ℝ → ℝ := fun t => L * ((∑ m ∈ Finset.range c, u t m * a m) + a c) /
      ((∑ m ∈ Finset.range c, u t m) + 1) with hF
  have hEq : ∀ lam : ℝ, 0 < lam → meanTravelTime L V (c + 1) lam = F ((lam * L)⁻¹) := by
    intro lam hlam
    have hx : 0 < lam * L := mul_pos hlam hL
    rw [avh_key L hL V (c + 1) hcap hV lam hlam]
    have hwc : ∀ m ∈ Finset.range c, weight L V lam m = weight L V lam c * u ((lam * L)⁻¹) m := by
      intro m hm
      have hm := Finset.mem_range.1 hm
      rw [hw, hw]
      simp only [hu]
      have h1 : (lam * L) ^ c = (lam * L) ^ m * (lam * L) ^ (c - m) := by
        rw [← pow_add]; congr 1; omega
      have h2 : ((lam * L)⁻¹) ^ (c - m) * (lam * L) ^ (c - m) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hx.ne', one_pow]
      have h3 : cc c ≠ 0 := hcpos.ne'
      calc (lam * L) ^ m * cc m
          = (lam * L) ^ m * cc m * ((lam * L)⁻¹ ^ (c - m) * (lam * L) ^ (c - m)) := by rw [h2, mul_one]
        _ = (lam * L) ^ c * cc c * (cc m / cc c * (lam * L)⁻¹ ^ (c - m)) := by
            rw [h1]; field_simp
    have hwcpos : 0 < weight L V lam c := avh_wpos L hL V (c + 1) hV lam hlam c (by omega)
    have hN : ∑ m ∈ Finset.range c, weight L V lam m / V (m + 1)
        = weight L V lam c * ∑ m ∈ Finset.range c, u ((lam * L)⁻¹) m * a m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hwc m hm]; simp only [ha]; ring
    have hD : ∑ m ∈ Finset.range c, weight L V lam m
        = weight L V lam c * ∑ m ∈ Finset.range c, u ((lam * L)⁻¹) m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hwc
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hN, hD]
    simp only [hF, ha]
    have hVc : 0 < V (c + 1) := hV (c + 1) (by omega) le_rfl
    have hsum : 0 ≤ ∑ m ∈ Finset.range c, u ((lam * L)⁻¹) m := by
      apply Finset.sum_nonneg
      intro m hm
      have := hccpos m (by have := Finset.mem_range.1 hm; omega)
      simp only [hu]
      positivity
    field_simp
  have ht : Filter.Tendsto (fun lam : ℝ => (lam * L)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Filter.tendsto_id.atTop_mul_const hL)
  have hu0 : ∀ m ∈ Finset.range c, Filter.Tendsto (fun t => u t m) (nhds 0) (nhds 0) := by
    intro m hm
    have hm := Finset.mem_range.1 hm
    have : Filter.Tendsto (fun t : ℝ => cc m / cc c * t ^ (c - m)) (nhds 0) (nhds (cc m / cc c * 0 ^ (c - m))) :=
      (continuous_const.mul (continuous_id.pow _)).tendsto 0
    rw [zero_pow (by omega), mul_zero] at this
    exact this
  have hF0 : Filter.Tendsto F (nhds 0) (nhds (L * (0 + a c) / (0 + 1))) := by
    simp only [hF]
    refine Filter.Tendsto.div (Filter.Tendsto.const_mul _ ?_) ?_ (by norm_num)
    · refine Filter.Tendsto.add ?_ tendsto_const_nhds
      have := tendsto_finset_sum (Finset.range c) (fun m hm => (hu0 m hm).mul_const (a m))
      simpa using this
    · refine Filter.Tendsto.add ?_ tendsto_const_nhds
      have := tendsto_finset_sum (Finset.range c) hu0
      simpa using this
  have hlim : L * (0 + a c) / (0 + 1) = L / V (c + 1) := by
    simp only [ha]; ring
  rw [hlim] at hF0
  refine (hF0.comp ht).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with lam hlam
  exact (hEq lam hlam).symm

theorem avh_lc (N c : ℕ) (L : ℝ) (hL : 0 < L) (VB VDA VDH : ℕ → ℝ)
    (hVBjam : 0 < VB (N * c)) (hVDAjam : 0 < VDA c) (hVDHjam : 0 < VDH ((N - 1) * c))
    (hAV : VDH ((N - 1) * c) < VDA c) (p : ℝ) :
    p * L / VDA c + (1 - p) * L / VDH ((N - 1) * c) ≤ L / VB (N * c) ↔
      pDW N c VB VDA VDH ≤ p := by
  unfold pDW
  generalize VDA c = a at *
  generalize VDH ((N - 1) * c) = h at *
  generalize VB (N * c) = b at *
  have hden : 0 < a * b - b * h := by nlinarith [mul_pos hVBjam (sub_pos.2 hAV)]
  rw [div_le_iff₀ hden, div_add_div _ _ hVDAjam.ne' hVDHjam.ne',
    div_le_div_iff₀ (mul_pos hVDAjam hVDHjam) hVBjam]
  have e : L * (a * h) - (p * L * h + a * ((1 - p) * L)) * b
      = L * ((a * b - b * h) * p - (a * b - a * h)) := by ring
  constructor
  · intro H
    have h1 : 0 ≤ L * ((a * b - b * h) * p - (a * b - a * h)) := by rw [← e]; linarith
    have h2 := (mul_nonneg_iff_of_pos_left hL).1 h1
    linarith
  · intro H
    have h1 : 0 ≤ L * ((a * b - b * h) * p - (a * b - a * h)) :=
      mul_nonneg hL.le (by linarith)
    rw [← e] at h1
    linarith

theorem avh_lc_lt (N c : ℕ) (L : ℝ) (hL : 0 < L) (VB VDA VDH : ℕ → ℝ)
    (hVBjam : 0 < VB (N * c)) (hVDAjam : 0 < VDA c) (hVDHjam : 0 < VDH ((N - 1) * c))
    (hAV : VDH ((N - 1) * c) < VDA c) (p : ℝ) :
    p * L / VDA c + (1 - p) * L / VDH ((N - 1) * c) < L / VB (N * c) ↔
      pDW N c VB VDA VDH < p := by
  unfold pDW
  generalize VDA c = a at *
  generalize VDH ((N - 1) * c) = h at *
  generalize VB (N * c) = b at *
  have hden : 0 < a * b - b * h := by nlinarith [mul_pos hVBjam (sub_pos.2 hAV)]
  rw [div_lt_iff₀ hden, div_add_div _ _ hVDAjam.ne' hVDHjam.ne',
    div_lt_div_iff₀ (mul_pos hVDAjam hVDHjam) hVBjam]
  have e : L * (a * h) - (p * L * h + a * ((1 - p) * L)) * b
      = L * ((a * b - b * h) * p - (a * b - a * h)) := by ring
  constructor
  · intro H
    have h1 : 0 < L * ((a * b - b * h) * p - (a * b - a * h)) := by rw [← e]; linarith
    have h2 := (mul_pos_iff_of_pos_left hL).1 h1
    linarith
  · intro H
    have h1 : 0 < L * ((a * b - b * h) * p - (a * b - a * h)) :=
      mul_pos hL (by linarith)
    rw [← e] at h1
    linarith

theorem solution (N c : ℕ) (L : ℝ) (hL : 0 < L) (VB VDA VDH : ℕ → ℝ)
    (hVBjam : 0 < VB (N * c)) (hVDAjam : 0 < VDA c) (hVDHjam : 0 < VDH ((N - 1) * c))
    (hAV : VDH ((N - 1) * c) < VDA c) (p : ℝ) :
    p * L / VDA c + (1 - p) * L / VDH ((N - 1) * c) ≤ L / VB (N * c) ↔
      pDW N c VB VDA VDH ≤ p := avh_lc N c L hL VB VDA VDH hVBjam hVDAjam hVDHjam hAV p
