-- Prove2me | Definitions.Def_SubexpPrimes_primeMass
-- name    : SubexpPrimes_primeMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:43.580319+00:00
-- url     : https://prove2.me/theorems/cf0f097d-245d-4d87-b5e6-913a8bf7c2d1
-- title:
--   The prime mass $W_C$
-- statement:
--   For a constraint $C$ on $n$-bit strings, the **prime mass** is
--
--   $$
--   W_C=\sum_{p<2^n,\ p\text{ prime}} C(p)\ln p,
--   $$
--
--   where $C(p)$ is $1$ if the $n$-bit string of $p$ satisfies the constraint and $0$ otherwise. It is $0$ when no prime qualifies and at least $\ln 2$ otherwise, and this gap is what the search for the least prime uses.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), equation (1), p.7

import Mathlib
import Definitions.Def_SubexpPrimes_bitsToNat

set_option autoImplicit false

namespace SubexpPrimes

open scoped Classical in
/-- **The prime mass** — Gajulapalli, *Deterministic Construction of Primes in Subexponential
Time* (manuscript, sha256 6ad4d3de…), equation (1), p.7:
`W_C = ∑_{p < 2ⁿ, p prime} C(p) ln p`, where `C(p)` is `1` if the `n`-bit string of `p` satisfies
the constraint and `0` otherwise. -/
noncomputable def primeMass (n : ℕ) (C : List Bool → Prop) : ℝ :=
  ∑ p ∈ (Finset.range (2 ^ n)).filter Nat.Prime, if C (bitsOf n p) then Real.log p else 0

end SubexpPrimes


