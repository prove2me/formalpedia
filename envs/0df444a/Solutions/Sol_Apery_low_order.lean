-- Prove2me | solution 1 for Apery.low_order
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T14:22:38.680933+00:00
-- url     : https://prove2.me/submissions/bfa4c53e-1afc-42d7-a5a6-3f730d4a45a6

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The lower-order terms of the growth estimate are $o(K^2)$ (source `Apery/Growth.lean`)

This file proves the platform theorem `Apery.low_order`: for every $\delta > 0$,

$$6\cdot 37n\,\bigl(\sqrt{200n}+1\bigr)\log(200n) + 3\cdot 10^9\,n \;\le\; \delta\,K^2,
\qquad K = 40n,$$

for all large $n$. It absorbs the elementary error terms of the four prime ranges of the
growth estimate for the normaliser. A faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Growth.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstants

set_option autoImplicit false

section Port0
/-!
# The lower-order terms of the growth estimate are `o(K²)`

For every `δ > 0`,

`6 · 37n · ((√(200n) + 1) log(200 n)) + 3·10⁹ n ≤ δ · K²`

for all large `n`, with `K = 40 n`. This is `Apery.low_order` of
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Growth.lean`; it absorbs the
elementary error terms of the four prime ranges (the `√`-counting term of the small range and
the `θ ≤ 2y` errors of the remaining ranges).
-/

open Filter Finset

namespace Apery

/-- The lower-order terms are `o(K²)`. -/
lemma low_order {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 6 * (37 * (n : ℝ)) * ((Real.sqrt (200 * n) + 1) * Real.log (200 * n)) +
      3 * 10 ^ 9 * n ≤ δ * Kr n ^ 2 := by
  set A : ℝ := (1776 + 3 * 10 ^ 9) / (8 * δ) + 1 with hA
  have hy : Tendsto (fun n : ℕ => (200 * (n : ℝ)) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  filter_upwards [hy.eventually_ge_atTop A, eventually_ge_atTop 1] with n hs hn
  set s := (200 * (n : ℝ)) ^ ((1 : ℝ) / 4) with hsdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy0 : (0 : ℝ) ≤ 200 * n := by positivity
  have hA1 : 1 ≤ A := by rw [hA]; have : 0 ≤ (1776 + 3 * 10 ^ 9) / (8 * δ) := by positivity
                         linarith
  have hs1 : 1 ≤ s := le_trans hA1 hs
  have hs4 : s ^ 4 = 200 * n := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have hsqrt : Real.sqrt (200 * n) = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog : Real.log (200 * n) ≤ 4 * s := by
    rw [← hs4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    push_cast; linarith
  have hlog0 : 0 ≤ Real.log (200 * n) := Real.log_nonneg (by linarith)
  rw [hsqrt]
  have h1 : (s ^ 2 + 1) * Real.log (200 * n) ≤ 8 * s ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ s ^ 2 + 1 by positivity)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs1 2]
  have hKr : Kr n ^ 2 = 8 * s ^ 4 * n := by simp only [Kr]; rw [hs4]; ring
  rw [hKr]
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
  have hkey : 1776 * s ^ 3 + 3 * 10 ^ 9 ≤ 8 * δ * s ^ 4 := by
    have hAs : (1776 + 3 * 10 ^ 9) / (8 * δ) ≤ s := by linarith
    have : 1776 + 3 * 10 ^ 9 ≤ 8 * δ * s := by
      rw [div_le_iff₀ (by positivity)] at hAs; linarith
    nlinarith [mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ s ^ 3 by positivity)]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6 * (37 * n) by positivity),
    mul_le_mul_of_nonneg_left hkey hn0]

end Apery
end Port0


open Filter in
/-- The platform target `Apery.low_order`, restated at top level as `solution`. -/
theorem solution {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 6 * (37 * (n : ℝ)) * ((Real.sqrt (200 * n) + 1) * Real.log (200 * n)) +
      3 * 10 ^ 9 * n ≤ δ * Apery.Kr n ^ 2 :=
  Apery.low_order hδ
