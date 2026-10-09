-- Prove2me | Definitions.Def_RamanujanNotebooks_ch06_ch06EMConstant
-- name    : RamanujanNotebooks_ch06_ch06EMConstant
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T22:18:13.370464+00:00
-- url     : https://prove2.me/theorems/3935adc9-00ef-4c07-98ec-58632fb7596b
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 6: ch06EMConstant
-- statement:
--   The Euler-Maclaurin constant `C_n` of `f` with parameter `a`, equation (1.3), p. 135:
--   `C_n = ∫_0^a f(t) dt - f(0)/2 - ∑_{k=1}^n B_{2k}/(2k)! f^{(2k-1)}(0)
--          + ∫_0^∞ P_{2n+1}(t) f^{(2n+1)}(t) dt`.
--   This is the book's precise version (after Hardy) of Ramanujan's "constant of the series
--   `∑ f(k)`".  It depends on a choice, the lower limit `a` of the integral in the summation
--   formula, which is the parameter `a` here; the book's normalisation in Ramanujan's own
--   definition is `a = 0`.  The index `n` is the number of Bernoulli terms kept; the book asserts
--   that the value does not depend on `n` when all the integrals exist.
--   The sum over `k = 1, …, n` is written over `k + 1` with `k ∈ range n`; `B_{2k}` is Mathlib's
--   rational `bernoulli (2k)`; `f^{(j)}` is `iteratedDeriv j f`.
--   Domain (the book's assumptions): `f` has `2n+1` continuous derivatives on `[0, ∞)`, `f` is
--   integrable between `0` and `a`, and `P_{2n+1} f^{(2n+1)}` is integrable on `(0, ∞)`.
--   Outside: a non-integrable integrand makes Lean's integral `0` and a missing derivative makes
--   `iteratedDeriv` return `0`, and the value is then meaningless (for example `f(t) = t`, `n = 0`
--   gives `0` instead of `-1/12`).
--   Reference: `f = 1`: `-1/2` for every `n`; `f(t) = t`, `a = 0`, `n ≥ 1`: `-1/12`;
--   `f(t) = 1/(t+1)`, `a = 0`: `γ - 1 = -0.42278433509846713939…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 6.

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch06_ch06PeriodicBernoulli

namespace RamanujanNotebooks

/-- The Euler-Maclaurin constant `C_n` of `f` with parameter `a`, equation (1.3), p. 135:
`C_n = ∫_0^a f(t) dt - f(0)/2 - ∑_{k=1}^n B_{2k}/(2k)! f^{(2k-1)}(0)
       + ∫_0^∞ P_{2n+1}(t) f^{(2n+1)}(t) dt`.
This is the book's precise version (after Hardy) of Ramanujan's "constant of the series
`∑ f(k)`".  It depends on a choice, the lower limit `a` of the integral in the summation
formula, which is the parameter `a` here; the book's normalisation in Ramanujan's own
definition is `a = 0`.  The index `n` is the number of Bernoulli terms kept; the book asserts
that the value does not depend on `n` when all the integrals exist.
The sum over `k = 1, …, n` is written over `k + 1` with `k ∈ range n`; `B_{2k}` is Mathlib's
rational `bernoulli (2k)`; `f^{(j)}` is `iteratedDeriv j f`.
Domain (the book's assumptions): `f` has `2n+1` continuous derivatives on `[0, ∞)`, `f` is
integrable between `0` and `a`, and `P_{2n+1} f^{(2n+1)}` is integrable on `(0, ∞)`.
Outside: a non-integrable integrand makes Lean's integral `0` and a missing derivative makes
`iteratedDeriv` return `0`, and the value is then meaningless (for example `f(t) = t`, `n = 0`
gives `0` instead of `-1/12`).
Reference: `f = 1`: `-1/2` for every `n`; `f(t) = t`, `a = 0`, `n ≥ 1`: `-1/12`;
`f(t) = 1/(t+1)`, `a = 0`: `γ - 1 = -0.42278433509846713939…`. -/
noncomputable def ch06EMConstant (f : ℝ → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  (∫ t in (0 : ℝ)..a, f t) - f 0 / 2
    - (∑ k ∈ Finset.range n,
        ((bernoulli (2 * (k + 1)) : ℚ) : ℝ) / ((2 * (k + 1)).factorial : ℝ)
          * iteratedDeriv (2 * k + 1) f 0)
    + ∫ t in Set.Ioi (0 : ℝ),
        ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t

end RamanujanNotebooks


