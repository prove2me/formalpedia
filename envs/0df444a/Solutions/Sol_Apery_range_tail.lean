-- Prove2me | solution 1 for Apery.range_tail
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T14:46:08.453934+00:00
-- url     : https://prove2.me/submissions/9776cf8d-db45-466e-a274-997fa546ea6c

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The tail prime range $K/400 < p \le K/20$ — reduction to `range2_le` and `tail_psum_limit`

This file proves the platform theorem `Apery.range_tail`:

$$\sum_{K/400 < p \le K/20} c(k)\,\bigl(-L_k\bigr) \;\le\; \Bigl(-\frac{6843153}{128000000} +
\varepsilon\Bigr) K^2 \quad\text{eventually in } n,$$

from the source's two lemmas: `Apery.range2_le` (per-prime point bounds summed over the range,
producing `psum (x F(x) + 27/16) 20 400 K + 10^7 θ(2n)`) and `Apery.tail_psum_limit` (the limit
of the weighted prime sum). The error term $10^7\theta(2n) \le 4\cdot 10^7 n$ is absorbed with
$\theta \le 2y$ and the proved `Apery.low_order`. Ported from
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, modules
`Apery/Growth/Assembly3.lean` and `Apery/Growth/Assembly4.lean` (with the $\theta \le 2y$ step
of `Apery/Growth.lean`).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Theorems.Thm_Apery_range2_le
import Theorems.Thm_Apery_tail_psum_limit
import Theorems.Thm_Apery_low_order

set_option autoImplicit false

section Port0
/-!
# The tail prime range `K/400 < p ≤ K/20` — reduction to `range2_le` and `tail_psum_limit`

This file proves the platform theorem `Apery.range_tail`:

`∑_{K/400 < p ≤ K/20} c(k)(-L_k) ≤ (-6843153/128000000 + ε) K²` eventually,

from the source's two lemmas: `Apery.range2_le` (the per-prime bounds summed over the range,
giving `psum (x F(x) + 27/16) 20 400 K + 10^7 θ(2n)`) and `Apery.tail_psum_limit` (the limit of
the weighted prime sum, `-6843153/128000000 + δ`). The error term `10^7 θ(2n) ≤ 4·10^7 n` is
absorbed with `θ ≤ 2y` and the proved `Apery.low_order`. Ported from
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Growth/Assembly3.lean`
(`range2_le`) and `Apery/Growth/Assembly4.lean` (`tail_psum_limit`) with the `θ ≤ 2y` step of
`Apery/Growth.lean`.
-/

open Finset Filter

namespace Apery

lemma theta_le_two (y : ℝ) (hy : 0 ≤ y) : Chebyshev.theta y ≤ 2 * y := by
  have h := Chebyshev.theta_le_log4_mul_x hy
  have : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  nlinarith

/-- The tail range, from the per-prime bounds and the prime-sum limit. -/
theorem range_tail : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (n / 10) (2 * n), cPrime k * (-(Lp n k : ℝ)) ≤
      (-6843153 / 128000000 + ε) * Kr n ^ 2 := by
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  have hKr : Tendsto Kr atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 40)
  have hpsum : ∀ᶠ n : ℕ in atTop,
      psum (fun x => x * Ftail x + 27 / 16) 20 400 (Kr n) / Kr n ^ 2 ≤
        -6843153 / 128000000 + ε / 2 :=
    hKr.eventually (tail_psum_limit hδ)
  filter_upwards [hpsum, low_order hδ, eventually_ge_atTop 10400] with n hp hlow hn
  have hK0 : 0 < Kr n ^ 2 := by
    simp only [Kr]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    positivity
  have hp' : psum (fun x => x * Ftail x + 27 / 16) 20 400 (Kr n) ≤
      (-6843153 / 128000000 + ε / 2) * Kr n ^ 2 := (div_le_iff₀ hK0).mp hp
  have hθ : Chebyshev.theta (2 * n : ℕ) ≤ 4 * n := by
    have h2 := theta_le_two ((2 * n : ℕ) : ℝ) (by positivity)
    push_cast at h2 ⊢
    linarith
  have h3e9 : 3 * 10 ^ 9 * n ≤ ε / 2 * Kr n ^ 2 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog : 0 ≤ Real.log (200 * (n : ℝ)) := by
      apply Real.log_nonneg
      nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n)]
    have hs : 0 ≤ Real.sqrt (200 * (n : ℝ)) := Real.sqrt_nonneg _
    have hbr : 0 ≤ (Real.sqrt (200 * (n : ℝ)) + 1) * Real.log (200 * (n : ℝ)) :=
      mul_nonneg (by linarith) hlog
    have h1 : (0 : ℝ) ≤
        6 * (37 * (n : ℝ)) * ((Real.sqrt (200 * n) + 1) * Real.log (200 * n)) :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hn0)) hbr
    linarith [hlow]
  have herr : 10 ^ 7 * Chebyshev.theta (2 * n : ℕ) ≤ ε / 2 * Kr n ^ 2 := by
    have h1 : (10 : ℝ) ^ 7 * Chebyshev.theta (2 * n : ℕ) ≤ 10 ^ 7 * (4 * n) :=
      mul_le_mul_of_nonneg_left hθ (by norm_num)
    nlinarith [h1, h3e9]
  have h2 := range2_le hn
  linarith

end Apery
end Port0


open Finset Filter in
/-- The platform target `Apery.range_tail`, restated at top level as `solution`. -/
theorem solution : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (n / 10) (2 * n), Apery.cPrime k * (-(Apery.Lp n k : ℝ)) ≤
      (-6843153 / 128000000 + ε) * Apery.Kr n ^ 2 :=
  Apery.range_tail
