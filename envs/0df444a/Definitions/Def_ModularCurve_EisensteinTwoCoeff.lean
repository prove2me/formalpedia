-- Prove2me | Definitions.Def_ModularCurve_EisensteinTwoCoeff
-- name    : ModularCurve_EisensteinTwoCoeff
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/3b6ffc1f-9642-5502-8835-1fd99feebf14
-- title:
--   Prime-to-p divisor sums and weight-two Eisenstein coefficients
-- statement:
--   Two arithmetic functions of natural numbers are introduced. For natural numbers $p$ and $n$, `sigmaPrimeTo p n` is the natural number $\sum_{d \mid n,\ p \nmid d} d$, the sum taken over those divisors $d$ of $n$ (in the sense of `Nat.divisors`, so over the positive divisors, and over the empty set when $n = 0$) that are not divisible by $p$. Thus `sigmaPrimeTo p 0 = 0`, and for $n \ge 1$ it is the prime-to-$p$ part of the usual divisor sum $\sigma_1(n)$, namely $\sigma_1(n)$ with the terms divisible by $p$ removed.
--
--   The second definition, `eisensteinTwoCoeff p n`, is an integer defined by cases on $n$: it is $p - 1$, computed in $\mathbb{Z}$, when $n = 0$, and $24 \cdot \mathrm{sigmaPrimeTo}(p, n)$ otherwise. This is the integral coefficient sequence of $24$ times the weight-two Eisenstein series of level $p$, whose $q$-expansion is $\tfrac{p-1}{24} + \sum_{n \ge 1} \big(\sum_{d \mid n,\ p \nmid d} d\big) q^n$; multiplying by $24$ clears the denominator of the constant term, so that all coefficients lie in $\mathbb{Z}$. What is defined here is exactly this integer sequence: no modular form, $q$-expansion or level structure is constructed, and no primality hypothesis on $p$ is imposed. Two accompanying lemmas record the two branches of the definition, `eisensteinTwoCoeff_zero` giving the constant term $p - 1$ and `eisensteinTwoCoeff_of_ne_zero` giving $24\,\mathrm{sigmaPrimeTo}(p, n)$ for $n \ne 0$; small numerical values, for instance at $p = 11$ and $p = 2$, are checked by evaluation.
--
--   **Relation to Mathlib.** Mathlib supplies `Nat.divisors` and the divisor-sum functions; the prime-to-$p$ restricted divisor sum and the associated integral coefficient sequence are the project's own definitions.
--
--   **Where it is used.** These coefficients provide the integral $q$-expansion data of the weight-two Eisenstein series at prime level, as used in arguments about the Eisenstein ideal and congruences between Eisenstein and cuspidal Hecke eigensystems; the constant term $p-1$ against the normalising factor $24$ is what produces the numerator of $(p-1)/12$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_EisensteinTwoCoeff.lean

import Mathlib.NumberTheory.Divisors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurve

def sigmaPrimeTo (p n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), d

def eisensteinTwoCoeff (p n : ℕ) : ℤ := if n = 0 then (p : ℤ) - 1 else 24 * (sigmaPrimeTo p n : ℤ)

theorem eisensteinTwoCoeff_zero (p : ℕ) : eisensteinTwoCoeff p 0 = (p : ℤ) - 1 := by
  simp [eisensteinTwoCoeff]

theorem eisensteinTwoCoeff_of_ne_zero (p : ℕ) {n : ℕ} (hn : n ≠ 0) :
    eisensteinTwoCoeff p n = 24 * (sigmaPrimeTo p n : ℤ) := by
  simp [eisensteinTwoCoeff, hn]

example : eisensteinTwoCoeff 11 0 = 10 := by decide
example : eisensteinTwoCoeff 11 1 = 24 := by decide
example : eisensteinTwoCoeff 11 2 = 72 := by decide
example : eisensteinTwoCoeff 11 11 = 24 := by decide
example : eisensteinTwoCoeff 11 22 = 72 := by decide
example : eisensteinTwoCoeff 2 0 = 1 := by decide
example : eisensteinTwoCoeff 2 4 = 24 := by decide

end ModularCurve


