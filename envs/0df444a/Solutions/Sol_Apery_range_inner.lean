-- Prove2me | solution 1 for Apery.range_inner
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T15:33:21.812062+00:00
-- url     : https://prove2.me/submissions/ed675e7d-cdf7-4ee0-8092-bb5c6a3bcd77

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The inner prime range $K/20 < p \le K/3$ — reduction to `range3_le` and `inner_psum_limit`

This file proves the platform theorem `Apery.range_inner`: eventually in $n$,

$$\sum_{K/20 < p \le K/3} c(k)\,\bigl(-L_k\bigr) \;\le\;
   \Bigl(\frac{322437603634266857629}{7535670527041937280000} + \varepsilon\Bigr) K^2,
   \qquad K = 40n,$$

from the source's two lemmas: `Apery.range3_le` (per-prime bounds summed over the range,
producing $\operatorname{psum} F_{\mathrm{in}}\,3\,20\,K + 10^8\theta(\lfloor 40n/3\rfloor)$)
and `Apery.inner_psum_limit` (the limit of the weighted prime sum). The error term
$10^8\theta(\lfloor 40n/3\rfloor) \le 10^8 \cdot \frac{80n}{3} = 2.67\cdot 10^9 n$ is
absorbed with $\theta \le 2y$, $\lfloor 40n/3\rfloor \le 40n/3$ and the proved
`Apery.low_order`. Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
modules `Apery/Growth/Assembly3.lean` and `Apery/Growth/Assembly4.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Theorems.Thm_Apery_range3_le
import Theorems.Thm_Apery_inner_psum_limit
import Theorems.Thm_Apery_low_order

set_option autoImplicit false

section Port0
open Finset Filter

namespace Apery

lemma theta_le_two' (y : ℝ) (hy : 0 ≤ y) : Chebyshev.theta y ≤ 2 * y := by
  have h := Chebyshev.theta_le_log4_mul_x hy
  have : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  nlinarith

/-- The inner range, from the per-prime bounds and the prime-sum limit. -/
theorem range_inner : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (2 * n) (40 * n / 3), cPrime k * (-(Lp n k : ℝ)) ≤
      (322437603634266857629 / 7535670527041937280000 + ε) * Kr n ^ 2 := by
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  have hKr : Tendsto Kr atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 40)
  have hpsum : ∀ᶠ n : ℕ in atTop,
      psum fIn 3 20 (Kr n) / Kr n ^ 2 ≤
        322437603634266857629 / 7535670527041937280000 + ε / 2 :=
    hKr.eventually (inner_psum_limit hδ)
  filter_upwards [hpsum, low_order hδ, eventually_ge_atTop 10400] with n hp hlow hn
  have hK0 : 0 < Kr n ^ 2 := by
    simp only [Kr]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    positivity
  have hp' : psum fIn 3 20 (Kr n) ≤
      (322437603634266857629 / 7535670527041937280000 + ε / 2) * Kr n ^ 2 :=
    (div_le_iff₀ hK0).mp hp
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
  have hcase : ((40 * n / 3 : ℕ) : ℝ) ≤ 40 * (n : ℝ) / 3 := by
    have hR : ((40 * n / 3 : ℕ) : ℝ) * 3 ≤ 40 * (n : ℝ) := by
      have h := Nat.div_mul_le_self (40 * n) 3
      push_cast
      exact_mod_cast h
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hθ : Chebyshev.theta (40 * n / 3 : ℕ) ≤ 2 * (40 * (n : ℝ) / 3) := by
    have h2 := theta_le_two' ((40 * n / 3 : ℕ) : ℝ) (by positivity)
    linarith
  have herr : 10 ^ 8 * Chebyshev.theta (40 * n / 3 : ℕ) ≤ ε / 2 * Kr n ^ 2 := by
    have h1 : (10 : ℝ) ^ 8 * Chebyshev.theta (40 * n / 3 : ℕ) ≤
        10 ^ 8 * (2 * (40 * (n : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left hθ (by norm_num)
    nlinarith [h1, h3e9]
  have h2 := range3_le hn
  linarith

end Apery
end Port0


open Finset Filter in
/-- The platform target `Apery.range_inner`, restated at top level as `solution`. -/
theorem solution : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (2 * n) (40 * n / 3), Apery.cPrime k * (-(Apery.Lp n k : ℝ)) ≤
      (322437603634266857629 / 7535670527041937280000 + ε) * Apery.Kr n ^ 2 :=
  Apery.range_inner
