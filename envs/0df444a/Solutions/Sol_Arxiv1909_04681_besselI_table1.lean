-- Prove2me | solution 1 for Arxiv1909_04681.besselI_table1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:57:54.8528+00:00
-- url     : https://prove2.me/submissions/cb9aafdb-1f3a-4a1a-836b-bca97ed6864a

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

set_option autoImplicit false

namespace S78BT
open Arxiv1909_04681

noncomputable def tt (z : ℝ) (n k : ℕ) : ℝ :=
  (z / 2) ^ n * ((z ^ 2 / 4) ^ k / ((k.factorial : ℝ) * ((n + k).factorial : ℝ)))

lemma summ (n : ℕ) (z : ℝ) :
    Summable (fun k : ℕ => (z ^ 2 / 4) ^ k / ((k.factorial : ℝ) * ((n + k).factorial : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (Real.summable_pow_div_factorial (z ^ 2 / 4))
  have h1 : (1 : ℝ) ≤ ((n + k).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  apply div_le_div_of_nonneg_left (by positivity) h2
  nlinarith

lemma hasI (n : ℕ) (z : ℝ) : HasSum (tt z n) (besselI n z) :=
  (summ n z).hasSum.mul_left ((z / 2) ^ n)

lemma key (m : ℕ) (z : ℝ) (hz : z ≠ 0) (k : ℕ) :
    z * tt z m (k + 1) - z * tt z (m + 2) k = 2 * (m + 1) * tt z (m + 1) (k + 1) := by
  unfold tt
  rw [show m + (k + 1) = (m + k) + 1 by ring, show m + 2 + k = (m + k) + 1 + 1 by ring,
    show m + 1 + (k + 1) = (m + k) + 1 + 1 by ring]
  rw [Nat.factorial_succ (m + k + 1), Nat.factorial_succ (m + k), Nat.factorial_succ k]
  push_cast
  have h1 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (0 : ℝ) < ((m + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [pow_succ, pow_succ, pow_succ (z / 2) (m + 1)]
  field_simp
  ring

lemma key0 (m : ℕ) (z : ℝ) : z * tt z m 0 = 2 * (m + 1) * tt z (m + 1) 0 := by
  unfold tt
  rw [add_zero, add_zero, Nat.factorial_succ m]
  push_cast
  have h2 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [pow_succ]
  field_simp
  ring

lemma recI (m : ℕ) (z : ℝ) (hz : z ≠ 0) :
    besselI (m + 2) z = besselI m z - 2 * (m + 1) / z * besselI (m + 1) z := by
  have hA : HasSum (fun k => z * tt z m (k + 1)) (z * besselI m z - ∑ i ∈ Finset.range 1, z * tt z m i) :=
    (hasSum_nat_add_iff' 1).2 ((hasI m z).mul_left z)
  have hB : HasSum (fun k => z * tt z (m + 2) k) (z * besselI (m + 2) z) := (hasI (m + 2) z).mul_left z
  have hC : HasSum (fun k => 2 * (m + 1) * tt z (m + 1) (k + 1))
      (2 * (m + 1) * besselI (m + 1) z - ∑ i ∈ Finset.range 1, 2 * (m + 1) * tt z (m + 1) i) :=
    (hasSum_nat_add_iff' 1).2 ((hasI (m + 1) z).mul_left (2 * ((m : ℝ) + 1)))
  have hD := (hA.sub hB).congr_fun (fun k => (key m z hz k).symm)
  have hu := hD.unique hC
  simp only [Finset.range_one, Finset.sum_singleton] at hu
  rw [key0 m z] at hu
  field_simp
  linarith

end S78BT

open Arxiv1909_04681 in
theorem solution (k : ℝ) (hk : 0 < k) :
    besselI 4 k = (1 + 24 / k ^ 2) * besselI 0 k + (-8 / k - 48 / k ^ 3) * besselI 1 k ∧
    besselI 5 k = (1 + 48 / k ^ 2) * besselI 1 k + (-12 / k - 192 / k ^ 3) * besselI 2 k ∧
    besselI 6 k = (1 + 144 / k ^ 2 + 1920 / k ^ 4) * besselI 0 k +
      (-18 / k - 768 / k ^ 3 - 3840 / k ^ 5) * besselI 1 k ∧
    besselI 7 k = (1 + 240 / k ^ 2 + 5760 / k ^ 4) * besselI 1 k +
      (-24 / k - 1920 / k ^ 3 - 23040 / k ^ 5) * besselI 2 k ∧
    besselI 8 k = (1 + 480 / k ^ 2 + 28800 / k ^ 4 + 322560 / k ^ 6) * besselI 0 k +
      (-32 / k - 4800 / k ^ 3 - 138240 / k ^ 5 - 645120 / k ^ 7) * besselI 1 k ∧
    besselI 9 k = (1 + 720 / k ^ 2 + 67200 / k ^ 4 + 1290240 / k ^ 6) * besselI 1 k +
      (-40 / k - 9600 / k ^ 3 - 483840 / k ^ 5 - 5160960 / k ^ 7) * besselI 2 k ∧
    besselI 10 k =
      (1 + 1200 / k ^ 2 + 201600 / k ^ 4 + 9031680 / k ^ 6 + 92897280 / k ^ 8) * besselI 0 k +
      (-50 / k - 19200 / k ^ 3 - 1693440 / k ^ 5 - 41287680 / k ^ 7 - 185794560 / k ^ 9) *
        besselI 1 k := by
  have hk0 : k ≠ 0 := hk.ne'
  have e2 := S78BT.recI 0 k hk0
  have e3 := S78BT.recI 1 k hk0
  have e4 := S78BT.recI 2 k hk0
  have e5 := S78BT.recI 3 k hk0
  have e6 := S78BT.recI 4 k hk0
  have e7 := S78BT.recI 5 k hk0
  have e8 := S78BT.recI 6 k hk0
  have e9 := S78BT.recI 7 k hk0
  have e10 := S78BT.recI 8 k hk0
  norm_num at e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [e10, e9, e8, e7, e6, e5, e4, e3, e2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring
