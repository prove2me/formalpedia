-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_Conjecture71
-- name    : FasterPrimeEnum_Supplement_Conjecture71
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:49:29.124294+00:00
-- url     : https://prove2.me/theorems/e7ff061c-955d-440c-8191-5d5f9c327533
-- title:
--   Conjecture 7.1: few square-primes in $(x, x+\log^3x]$
-- statement:
--   Let $\tilde\pi(x)$ be the number of pairs $(m,p)$ with $m\ge1$, $p$ prime and $m^2p\le x$ (equation (7.1)), the counting function of the square-primes. **Conjecture 7.1** asserts that for every real $x\ge2$,
--
--   $$
--   \tilde\pi(x+\log^3x)-\tilde\pi(x)<3\log^2x,
--   $$
--
--   that is, the interval $(x,x+\log^3x]$ contains fewer than $3\log^2x$ square-primes. Logarithms are natural.
--
--   It is the hypothesis under which the heuristic algorithm (Theorem 1.4) never fails; the paper regards it as very likely true but far beyond current technology.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §7, eq. (7.1) and Conjecture 7.1, p.57

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open Classical in
/-- **The square-prime counting function `π̃(x)`** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), eq. (7.1), p.57: "π̃(x) := Σ_{m⩾1} Σ_{m²p⩽x,
p prime} 1", the number of pairs `(m, p)` with `m ≥ 1`, `p` prime and `m²p ≤ x`. Every such pair
has `m, p ≤ x`, so the pairs range over `[1, ⌊x⌋]²`. -/
noncomputable def sqPrimeCount (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun mp =>
    mp.2.Prime ∧ ((mp.1 ^ 2 * mp.2 : ℕ) : ℝ) ≤ x).card

/-- **Conjecture 7.1** — p.57: "For all x ⩾ 2 we have π̃(x + log³ x) − π̃(x) < 3 log² x, i.e., the
interval (x, x + log³ x] contains fewer than 3 log² x square-primes." Natural logarithms; `x` real. -/
def Conjecture71 : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    (sqPrimeCount (x + Real.log x ^ 3) : ℝ) - (sqPrimeCount x : ℝ) < 3 * Real.log x ^ 2

end Supplement

end FasterPrimeEnum


