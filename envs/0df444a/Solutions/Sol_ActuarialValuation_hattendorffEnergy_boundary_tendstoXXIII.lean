-- Prove2me | solution 1 for ActuarialValuation.hattendorffEnergy_boundary_tendstoXXIII
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T23:17:22.849411+00:00
-- url     : https://prove2.me/submissions/ef9520bf-9764-4643-ad1c-718d5541cb19

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (S A a : ℕ → ℝ)
    (hS : ∀ n, 0 < S n)
    (hStendsto : Filter.Tendsto S Filter.atTop (nhds 0))
    (ha : Summable a) (han : ∀ n, 0 ≤ a n)
    (hEnergy : ∀ T N, T ≤ N →
      S N * (A N - A T) ^ 2 ≤ ∑ t ∈ Finset.Ico T N, a t) :
  Filter.Tendsto (fun N => S N * (A N) ^ 2) Filter.atTop (nhds 0) := by
  classical
  let V : ℝ := ∑' t : ℕ, a t
  have hpartial (n : ℕ) :
      (∑ t ∈ Finset.range n, a t) ≤ V := by
    exact ha.sum_le_tsum (Finset.range n)
      (by intro t ht; exact han t)
  have hsplit (T N : ℕ) (hTN : T ≤ N) :
      (∑ t ∈ Finset.Ico T N, a t) =
        (∑ t ∈ Finset.range N, a t) -
          (∑ t ∈ Finset.range T, a t) := by
    have hs := Finset.sum_range_add_sum_Ico a hTN
    linarith [hs]
  have haT :
      Filter.Tendsto (fun n : ℕ => ∑ t ∈ Finset.range n, a t)
        Filter.atTop (nhds V) := by
    simpa only [V] using ha.tendsto_sum_tsum_nat
  have htailT :
      Filter.Tendsto (fun n : ℕ =>
        V - ∑ t ∈ Finset.range n, a t) Filter.atTop (nhds 0) := by
    convert tendsto_const_nhds.sub haT using 1 <;> simp
  have hbd (T N : ℕ) (hTN : T ≤ N) :
      S N * (A N) ^ 2 ≤
        2 * S N * (A T) ^ 2 +
          2 * (V - ∑ t ∈ Finset.range T, a t) := by
    have he := hEnergy T N hTN
    rw [hsplit T N hTN] at he
    have hp := hpartial N
    have hsq : (A N) ^ 2 ≤
        2 * (A T) ^ 2 + 2 * (A N - A T) ^ 2 := by
      nlinarith [sq_nonneg (A N - 2 * A T)]
    have hm := mul_le_mul_of_nonneg_left hsq (le_of_lt (hS N))
    nlinarith
  refine (tendsto_order).2 ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [] with n
    have hn := mul_nonneg (le_of_lt (hS n)) (sq_nonneg (A n))
    linarith
  · intro b hb
    have htev : ∀ᶠ T in Filter.atTop,
        V - (∑ t ∈ Finset.range T, a t) < b / 4 :=
      ((tendsto_order).1 htailT).2 (b / 4) (by linarith)
    obtain ⟨T, hT⟩ := htev.exists
    have hmt :
        Filter.Tendsto (fun n : ℕ => 2 * S n * (A T) ^ 2)
          Filter.atTop (nhds 0) := by
      have hh := hStendsto.mul_const (2 * (A T) ^ 2)
      have heq : (fun n : ℕ => 2 * S n * (A T) ^ 2) =
          (fun n : ℕ => S n * (2 * (A T) ^ 2)) := by
        funext n
        ring
      simpa only [heq, zero_mul] using hh
    have hnev : ∀ᶠ n in Filter.atTop,
        2 * S n * (A T) ^ 2 < b / 2 :=
      ((tendsto_order).1 hmt).2 (b / 2) (by linarith)
    filter_upwards [hnev, Filter.eventually_ge_atTop T] with n hn hnT
    have hv := hbd T n hnT
    linarith

