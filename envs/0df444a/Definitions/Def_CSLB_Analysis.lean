-- Prove2me | Definitions.Def_CSLB_Analysis
-- name    : CSLB_Analysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T11:47:11.023799+00:00
-- url     : https://prove2.me/theorems/2127cc67-1fd8-49eb-a6d9-fd2b8fd1a169
-- title:
--   Coded sorting bridge: Analysis
-- statement:
--   # Real-number estimates for assembling Theorem 3.1
--
--   Conversions between the parameter conventions: the word-size bounds `c₁ log₂ N ≤ w ≤ c₂ log₂ N`
--   give `⌈log₂ N⌉ ≤ ⌈1/c₁⌉·w`, `w ln 2 ≤ max(c₂,0) ln N` and `2^w ≤ N^⌈max(c₂,0)⌉`; the I/O factor
--   with natural logarithms equals the one with base-2 logarithms; and below a memory threshold
--   `Mc` the base-2 factor is at least `1` and at least `log₂ N / log₂ Mc`.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Mathlib
import Definitions.Def_CodedSorting_Exponent

/-! # Real-number estimates for assembling Theorem 3.1

Conversions between the parameter conventions: the word-size bounds `c₁ log₂ N ≤ w ≤ c₂ log₂ N`
give `⌈log₂ N⌉ ≤ ⌈1/c₁⌉·w`, `w ln 2 ≤ max(c₂,0) ln N` and `2^w ≤ N^⌈max(c₂,0)⌉`; the I/O factor
with natural logarithms equals the one with base-2 logarithms; and below a memory threshold
`Mc` the base-2 factor is at least `1` and at least `log₂ N / log₂ Mc`. -/

set_option autoImplicit false

namespace CSLB.Analysis
open Real

theorem logb_nat_nonneg (N : ℕ) (hN : 1 ≤ N) : 0 ≤ logb 2 (N : ℝ) :=
  logb_nonneg (by norm_num) (by exact_mod_cast hN)

theorem covers_of (c₁ : ℝ) (hc₁ : 0 < c₁) (N w : ℕ) (hN : 2 ≤ N)
    (h : c₁ * logb 2 (N : ℝ) ≤ w) : Nat.clog 2 N ≤ ⌈1 / c₁⌉₊ * w := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  have hl : logb 2 (N : ℝ) ≤ ((⌈1 / c₁⌉₊ * w : ℕ) : ℝ) := by
    have h1 : logb 2 (N : ℝ) ≤ w / c₁ := by rw [le_div_iff₀ hc₁]; linarith
    have h2 : (w : ℝ) / c₁ ≤ (⌈1 / c₁⌉₊ : ℝ) * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    push_cast
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have : (N : ℝ) ≤ (2 : ℝ) ^ ((⌈1 / c₁⌉₊ * w : ℕ) : ℝ) := by
    calc (N : ℝ) = (2 : ℝ) ^ (logb 2 (N : ℝ)) := (rpow_logb (by norm_num) (by norm_num) hNpos).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) hl
  rw [rpow_natCast] at this
  exact_mod_cast this

theorem word_log (c₂ : ℝ) (N w : ℕ) (hN : 2 ≤ N) (h : (w : ℝ) ≤ c₂ * logb 2 (N : ℝ)) :
    (w : ℝ) * log 2 ≤ max c₂ 0 * log (N : ℝ) := by
  have hl : 0 ≤ logb 2 (N : ℝ) := logb_nat_nonneg N (by omega)
  have h2 : (w : ℝ) ≤ max c₂ 0 * logb 2 (N : ℝ) :=
    h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have := mul_le_mul_of_nonneg_right h2 hlog2.le
  rw [logb, mul_assoc, div_mul_cancel₀ _ hlog2.ne'] at this
  exact this

theorem word_le_logb (c₂ : ℝ) (N w : ℕ) (hN : 2 ≤ N) (h : (w : ℝ) ≤ c₂ * logb 2 (N : ℝ)) :
    (w : ℝ) ≤ max c₂ 0 * logb 2 (N : ℝ) :=
  h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (logb_nat_nonneg N (by omega)))

theorem two_pow_le (c₂ : ℝ) (N w : ℕ) (hN : 2 ≤ N) (h : (w : ℝ) ≤ c₂ * logb 2 (N : ℝ)) :
    2 ^ w ≤ N ^ ⌈max c₂ 0⌉₊ := by
  have hw := word_le_logb c₂ N w hN h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have : (2 : ℝ) ^ (w : ℝ) ≤ (N : ℝ) ^ ((⌈max c₂ 0⌉₊ : ℕ) : ℝ) := by
    calc (2 : ℝ) ^ (w : ℝ) ≤ (2 : ℝ) ^ (max c₂ 0 * logb 2 (N : ℝ)) :=
          rpow_le_rpow_of_exponent_le (by norm_num) hw
      _ = ((2 : ℝ) ^ (logb 2 (N : ℝ))) ^ (max c₂ 0) := by
          rw [mul_comm, rpow_mul (by norm_num)]
      _ = (N : ℝ) ^ (max c₂ 0) := by rw [rpow_logb (by norm_num) (by norm_num) hNpos]
      _ ≤ (N : ℝ) ^ ((⌈max c₂ 0⌉₊ : ℕ) : ℝ) :=
          rpow_le_rpow_of_exponent_le hN1 (Nat.le_ceil _)
  rw [rpow_natCast, rpow_natCast] at this
  exact_mod_cast this

/-- The I/O factor with natural logarithms equals the base-2 one. -/
theorem factor_eq (N M B : ℕ) (hB : 1 ≤ B) (hBM : 2 * B ≤ M) (e : ℝ) :
    1 + log (N : ℝ) / (log ((M : ℝ) / B) ^ (1 - e) * log (M : ℝ) ^ e) =
      1 + logb 2 (N : ℝ) / ((logb 2 ((M : ℝ) / B)) ^ (1 - e) * (logb 2 (M : ℝ)) ^ e) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hMB : (2 : ℝ) ≤ (M : ℝ) / B := by
    rw [le_div_iff₀ hBpos]; exact_mod_cast (by omega : 2 * B ≤ M)
  have ha : 0 < log ((M : ℝ) / B) := log_pos (by linarith)
  have hm : 0 < log (M : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < M))
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  simp only [logb]
  rw [div_rpow ha.le hl2.le, div_rpow hm.le hl2.le]
  have hp : log 2 ^ (1 - e) * log 2 ^ e = log 2 := by
    rw [← rpow_add hl2]; simp
  have hx : 0 < log ((M : ℝ) / B) ^ (1 - e) := rpow_pos_of_pos ha _
  have hy : 0 < log (M : ℝ) ^ e := rpow_pos_of_pos hm _
  have hq : 0 < log 2 ^ (1 - e) := rpow_pos_of_pos hl2 _
  have hr : 0 < log 2 ^ e := rpow_pos_of_pos hl2 _
  congr 1
  rw [div_mul_div_comm, hp]
  field_simp

/-- The base-2 factor below a memory threshold. -/
theorem factor_small (N M B : ℕ) (hB : 1 ≤ B) (hBM : 2 * B ≤ M) (Mc : ℝ) (hMc : (M : ℝ) ≤ Mc)
    (hN : 2 ≤ N) (e : ℝ) (he1 : e ≤ 1) :
    1 ≤ 1 + logb 2 (N : ℝ) / ((logb 2 ((M : ℝ) / B)) ^ (1 - e) * (logb 2 (M : ℝ)) ^ e) ∧
    logb 2 (N : ℝ) / logb 2 Mc ≤
      1 + logb 2 (N : ℝ) / ((logb 2 ((M : ℝ) / B)) ^ (1 - e) * (logb 2 (M : ℝ)) ^ e) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMB : (2 : ℝ) ≤ (M : ℝ) / B := by
    rw [le_div_iff₀ hBpos]; exact_mod_cast (by omega : 2 * B ≤ M)
  have ha : 1 ≤ logb 2 ((M : ℝ) / B) := by
    rw [le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hMB
  have hab : logb 2 ((M : ℝ) / B) ≤ logb 2 (M : ℝ) := by
    apply logb_le_logb_of_le (by norm_num) (by linarith)
    rw [div_le_iff₀ hBpos]; nlinarith
  have hn : 0 ≤ logb 2 (N : ℝ) := logb_nat_nonneg N (by omega)
  set D := (logb 2 ((M : ℝ) / B)) ^ (1 - e) * (logb 2 (M : ℝ)) ^ e with hD
  have hDpos : 0 < D := by
    apply mul_pos <;> apply rpow_pos_of_pos <;> linarith
  have hDle : D ≤ logb 2 (M : ℝ) := by
    calc D ≤ (logb 2 (M : ℝ)) ^ (1 - e) * (logb 2 (M : ℝ)) ^ e := by
          apply mul_le_mul_of_nonneg_right _ (rpow_nonneg (by linarith) _)
          exact rpow_le_rpow (by linarith) hab (by linarith)
      _ = logb 2 (M : ℝ) := by rw [← rpow_add (by linarith)]; simp
  have hMc' : logb 2 (M : ℝ) ≤ logb 2 Mc := logb_le_logb_of_le (by norm_num) hMpos hMc
  refine ⟨by have := div_nonneg hn hDpos.le; linarith, ?_⟩
  have h1 : logb 2 (N : ℝ) / logb 2 Mc ≤ logb 2 (N : ℝ) / D :=
    div_le_div_of_nonneg_left hn hDpos (hDle.trans hMc')
  linarith

end CSLB.Analysis


