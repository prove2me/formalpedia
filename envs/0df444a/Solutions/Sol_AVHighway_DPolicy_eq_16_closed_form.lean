-- Prove2me | solution 1 for AVHighway.DPolicy.eq_16_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:06:25.915073+00:00
-- url     : https://prove2.me/submissions/cfcfba71-d96a-424c-aed4-44034b76a5bd

import Mathlib
import Definitions.Def_AVHighway_DPolicy_LossQueue

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

theorem solution (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (hlam : 0 < lam) :
    meanTravelTime L V cap lam =
      L * (∑ n ∈ Finset.range cap,
          (L * lam) ^ n / ((n.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 (n + 1), V k)) /
        (1 + ∑ n ∈ Finset.Icc 1 (cap - 1),
          (L * lam) ^ n / ((n.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 n, V k)) := by
  rw [avh_key L hL V cap hcap hV lam hlam]
  have h1 : ∀ n ∈ Finset.range cap, weight L V lam n / V (n + 1)
      = (L * lam) ^ n / ((n.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 (n + 1), V k) := by
    intro n hn
    have hVm : 0 < V (n + 1) := hV (n + 1) (by omega) (by have := Finset.mem_range.1 hn; omega)
    unfold weight
    rw [Finset.prod_Icc_succ_top (by omega), mul_comm lam L]
    have hP : 0 < ∏ k ∈ Finset.Icc 1 n, V k :=
      Finset.prod_pos fun k hk => hV k (Finset.mem_Icc.1 hk).1
        (by have := (Finset.mem_Icc.1 hk).2; have := Finset.mem_range.1 hn; omega)
    have hf : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
    field_simp
  have h2 : ∑ n ∈ Finset.range cap, weight L V lam n
      = 1 + ∑ n ∈ Finset.Icc 1 (cap - 1),
          (L * lam) ^ n / ((n.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 n, V k) := by
    obtain ⟨c, rfl⟩ : ∃ c, cap = c + 1 := ⟨cap - 1, by omega⟩
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.add_sub_cancel]
    congr 1
    · simp [weight]
    · have hI : Finset.Ico 1 (c + 1) = Finset.Icc 1 c := by ext; simp
      rw [hI]
      refine Finset.sum_congr rfl fun n _ => ?_
      unfold weight
      rw [mul_comm lam L]
  rw [Finset.sum_congr rfl h1, h2]
