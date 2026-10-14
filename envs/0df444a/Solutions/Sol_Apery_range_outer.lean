-- Prove2me | solution 1 for Apery.range_outer
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T15:30:43.403173+00:00
-- url     : https://prove2.me/submissions/86aad4a8-0056-4bdc-926a-f353a0661b83

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The outer prime range $K/3 < p \le 2h$ — reduction to `range4_le` and `outer_psum_limit`

This file proves the platform theorem `Apery.range_outer`: eventually in $n$,

$$\sum_{K/3 < p \le 74n} c(k)\,\bigl(-L_k\bigr) \;\le\;
   \Bigl(\frac{129101}{96000} + \varepsilon\Bigr) K^2, \qquad K = 40n,$$

from the source's two lemmas: `Apery.range4_le` (per-prime bounds summed over the range,
producing $\operatorname{psum} E_{\mathrm{out}}\,20/37\,3\,K + 10^5\theta(74n)$) and
`Apery.outer_psum_limit` (the limit of the weighted prime sum). The error term
$10^5\theta(74n) \le 10^5 \cdot 148n = 1.48\cdot 10^7 n$ is absorbed with $\theta \le 2y$ and
the proved `Apery.low_order`. Ported from mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, modules `Apery/Growth/Assembly3.lean` and
`Apery/Growth/Assembly4.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Theorems.Thm_Apery_range4_le
import Theorems.Thm_Apery_outer_psum_limit
import Theorems.Thm_Apery_low_order

set_option autoImplicit false

section Port0
open Finset Filter

namespace Apery

lemma theta_le_two (y : ℝ) (hy : 0 ≤ y) : Chebyshev.theta y ≤ 2 * y := by
  have h := Chebyshev.theta_le_log4_mul_x hy
  have : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  nlinarith

/-- The outer range, from the per-prime bounds and the prime-sum limit. -/
theorem range_outer : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), cPrime k * (-(Lp n k : ℝ)) ≤
      (129101 / 96000 + ε) * Kr n ^ 2 := by
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  have hKr : Tendsto Kr atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 40)
  have hpsum : ∀ᶠ n : ℕ in atTop,
      psum Eout (20 / 37) 3 (Kr n) / Kr n ^ 2 ≤ 129101 / 96000 + ε / 2 :=
    hKr.eventually (outer_psum_limit hδ)
  filter_upwards [hpsum, low_order hδ, eventually_ge_atTop 10400] with n hp hlow hn
  have hK0 : 0 < Kr n ^ 2 := by
    simp only [Kr]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    positivity
  have hp' : psum Eout (20 / 37) 3 (Kr n) ≤ (129101 / 96000 + ε / 2) * Kr n ^ 2 :=
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
  have hθ : Chebyshev.theta (2 * (37 * n) : ℕ) ≤ 4 * (37 * n) := by
    have h2 := theta_le_two ((2 * (37 * n) : ℕ) : ℝ) (by positivity)
    push_cast at h2 ⊢
    linarith
  have herr : 10 ^ 5 * Chebyshev.theta (2 * (37 * n) : ℕ) ≤ ε / 2 * Kr n ^ 2 := by
    have h1 : (10 : ℝ) ^ 5 * Chebyshev.theta (2 * (37 * n) : ℕ) ≤ 10 ^ 5 * (4 * (37 * n)) :=
      mul_le_mul_of_nonneg_left hθ (by norm_num)
    nlinarith [h1, h3e9]
  have h2 := range4_le hn
  linarith

end Apery
end Port0


open Finset Filter in
/-- The platform target `Apery.range_outer`, restated at top level as `solution`. -/
theorem solution : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), Apery.cPrime k * (-(Apery.Lp n k : ℝ)) ≤
      (129101 / 96000 + ε) * Apery.Kr n ^ 2 :=
  Apery.range_outer
