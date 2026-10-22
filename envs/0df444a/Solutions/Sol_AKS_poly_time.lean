-- Prove2me | solution 1 for AKS.poly_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:06:44.074066+00:00
-- url     : https://prove2.me/submissions/946018d7-efbd-463a-b58f-4d14010876a8

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS

theorem g71b_smallestR_le (n : ℕ) : smallestR n ≤ max 3 (logUp n ^ 5) := by
  unfold smallestR
  split
  · omega
  · rename_i r l h
    have hm : r ∈ (List.range (max 3 ((logUp n) ^ 5) + 1)).filter
        (fun r => decide (1 < r ∧ logUp n ^ 2 < ordR r n)) := by
      rw [h]; exact List.mem_cons_self
    rw [List.mem_filter, List.mem_range] at hm
    omega

theorem g71b_L_pos (n : ℕ) : 1 ≤ logUp n := by unfold logUp; omega

theorem solution : ∃ C : ℕ, ∀ n : ℕ, aksWork n ≤ C * (logUp n) ^ 15 := by
  refine ⟨71, fun n => ?_⟩
  have hL := g71b_L_pos n
  set L := logUp n with hLdef
  have hr : smallestR n ≤ 3 * L ^ 5 := by
    have := g71b_smallestR_le n
    have h1 : 1 ≤ L ^ 5 := Nat.one_le_pow _ _ hL
    rw [← hLdef] at this
    omega
  set r := smallestR n with hrdef
  have hell2 : ell r n ^ 2 ≤ 3 * L ^ 7 := by
    unfold ell
    calc Nat.sqrt (Nat.totient r * L ^ 2) ^ 2 ≤ Nat.totient r * L ^ 2 := Nat.sqrt_le' _
      _ ≤ r * L ^ 2 := Nat.mul_le_mul_right _ (Nat.totient_le r)
      _ ≤ 3 * L ^ 5 * L ^ 2 := Nat.mul_le_mul_right _ hr
      _ = 3 * L ^ 7 := by ring
  have hell : ell r n ≤ 2 * L ^ 4 := by
    by_contra hc
    push Not at hc
    have h1 : (2 * L ^ 4) ^ 2 < ell r n ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
    have h2 : 3 * L ^ 7 ≤ (2 * L ^ 4) ^ 2 := by
      have : L ^ 7 ≤ L ^ 8 := Nat.pow_le_pow_right hL (by norm_num)
      nlinarith
    omega
  have hr1 : r + 1 ≤ 4 * L ^ 5 := by
    have h1 : 1 ≤ L ^ 5 := Nat.one_le_pow _ _ hL
    omega
  have hL1 : L + 1 ≤ 2 * L := by omega
  unfold aksWork
  rw [← hLdef, ← hrdef]
  have e1 : L ^ 6 ≤ L ^ 15 := Nat.pow_le_pow_right hL (by norm_num)
  have e2 : r * (L + 1) ≤ 6 * L ^ 15 := by
    calc r * (L + 1) ≤ (3 * L ^ 5) * (2 * L) := Nat.mul_le_mul hr hL1
      _ = 6 * L ^ 6 := by ring
      _ ≤ 6 * L ^ 15 := Nat.mul_le_mul_left _ e1
  have e3 : ell r n * (L + 1) * (r + 1) ^ 2 ≤ 64 * L ^ 15 := by
    calc ell r n * (L + 1) * (r + 1) ^ 2 ≤ (2 * L ^ 4) * (2 * L) * (4 * L ^ 5) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul hell hL1) (Nat.pow_le_pow_left hr1 2)
      _ = 64 * L ^ 15 := by ring
  omega
