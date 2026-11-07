-- Prove2me | Definitions.Def_QPACLarge_Seed
-- name    : QPACLarge_Seed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:08.630071+00:00
-- url     : https://prove2.me/theorems/773e1d97-40e4-4d61-9278-ad265238769c
-- title:
--   Seeds $a=(a_\emptyset,\{a_i\},\{a_{ij}\}_{i<j})$ of the quadratic family
-- statement:
--   With $r = 1 + n + \binom n2$, a **seed** $a \in \{0,1\}^r$ is interpreted as
--   $$
--   a = (a_\emptyset, \{a_i\}_{i=1}^n, \{a_{ij}\}_{1 \le i < j \le n}),
--   $$
--   a constant, $n$ linear and $\binom n2$ quadratic coefficients. The seed set $A$ has $M = 2^r$ elements.
--
--   **Formalization Note** Indices are $0$-based; the quadratic coefficients are indexed by the pairs $i < j$, so the seed set has exactly $2^{1+n+\binom n2}$ elements.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.1.1, p.19

import Mathlib

namespace QPACLarge

/-- **Seeds of the quadratic Boolean family.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.1.1, p.19: "Let `r ≜ 1 + n + (n choose 2)`. A seed `a ∈ {0,1}^r` is interpreted as
`a = (a_∅, {aᵢ}_{i=1}^n, {aᵢⱼ}_{1≤i<j≤n})`."

A seed is the constant coefficient `a_∅`, the linear coefficients `aᵢ` and the quadratic
coefficients `aᵢⱼ` for `i < j`; there are exactly `2^r` seeds.

**Formalization Note.** Indices are `0`-based (`Fin n`); the quadratic coefficients are indexed by
the pairs `i < j`, so the seed set has `2^{1+n+n(n−1)/2}` elements, as on the page. -/
abbrev Seed (n : ℕ) : Type :=
  Bool × (Fin n → Bool) × ({p : Fin n × Fin n // p.1 < p.2} → Bool)

end QPACLarge


