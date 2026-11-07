-- Prove2me | Definitions.Def_SubexpPrimes_harmonicCount
-- name    : SubexpPrimes_harmonicCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:33.975213+00:00
-- url     : https://prove2.me/theorems/67981cda-6b4c-4627-9927-c2d84ac411ff
-- title:
--   The lattice count $N(b)$
-- statement:
--   With $B=2^{Q+2}$ and $P=n+2Q+4$,
--
--   $$
--   N(b)=\#\{(u,y)\in\mathbb Z^2:\ B<u\le Bb,\ y\ge0,\ u(y+1)\le 2^P\}.
--   $$
--
--   The scaled count $2^{-P}N(b)$ approximates $\ln b$ from below.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 5.2, p.25

import Mathlib

set_option autoImplicit false

namespace SubexpPrimes

/-- **The lattice count `N(b)`** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), Lemma 5.2, p.25: with `B = 2^{Q+2}` and
`P = n + 2Q + 4`,
`N(b) = #{(u, y) ∈ ℤ² : B < u ≤ Bb, y ≥ 0, u(y + 1) ≤ 2^P}`.

**Formalization Note.** All counted pairs are natural numbers, and `y < 2^P` holds for each of
them because `u ≥ 1`, so the count over `ℕ × ℕ` with `y < 2^P` is the printed one. -/
def harmonicCount (n Q b : ℕ) : ℕ :=
  (((Finset.Ioc (2 ^ (Q + 2)) (2 ^ (Q + 2) * b)) ×ˢ (Finset.range (2 ^ (n + 2 * Q + 4)))).filter
    fun p => p.1 * (p.2 + 1) ≤ 2 ^ (n + 2 * Q + 4)).card

end SubexpPrimes


