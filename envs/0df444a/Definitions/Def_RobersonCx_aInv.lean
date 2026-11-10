-- Prove2me | Definitions.Def_RobersonCx_aInv
-- name    : RobersonCx_aInv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:49.662479+00:00
-- url     : https://prove2.me/theorems/239efa97-e93e-4481-b439-362415d64396
-- title:
--   $a_n$, $d_r(n)$ and $b_r(n)$
-- statement:
--   For $n>2r$ with $\gcd(n,r)=1$, let $a_n$ be the unique integer with
--   $$1\le a_n<n,\qquad r\,a_n\equiv 1\pmod n,$$
--   and define
--   $$d_r(n)=\min\{a_n,\ n-a_n\},\qquad b_r(n)=\min\{2a_n-1,\ 2n-2a_n+1\}.$$
--   These are the cyclic distances between the endpoints of a short edge on the specified Hamilton cycles of $D^{(r)}_n$ and $B^{(r)}_n$; they enter the counting inequalities of Lemma 20.
--
--   **Formalization Note** `aInv n r` is the representative in $[0,n)$ of $r^{-1}$ in `ZMod n`, which is $a_n$ when $\gcd(n,r)=1$ and $n\ge2$; otherwise `ZMod`'s inverse returns a junk value, and every statement using these functions assumes $\gcd(n,r)=1$ and $n>2r$. The subtractions are natural-number subtractions, exact because $1\le a_n<n$.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. B, eq. (6), p.17 (PDF p.19)

import Mathlib

set_option autoImplicit false

namespace RobersonCx

/-- `a_n` (App. B, eq. (6), p.17 (PDF p.19)): for `n > 2r` with `gcd(n, r) = 1`, the unique integer with
`1 ≤ a_n < n` and `r a_n ≡ 1 (mod n)`.

**Formalization Note** `aInv n r` is the canonical representative in `[0, n)` of the inverse of `r` in
`ZMod n`. When `gcd(n, r) = 1` and `n ≥ 2` this is the paper's `a_n`; otherwise `ZMod`'s inverse returns a junk
value, and every statement using `aInv`, `dR`, `bR` assumes `gcd(n, r) = 1` and `n > 2r`. -/
def aInv (n r : ℕ) : ℕ := ((r : ZMod n)⁻¹).val

/-- `d_r(n) = min{a_n, n − a_n}`, eq. (6), p.17. **Formalization Note** natural-number subtraction, exact since
`a_n < n` under the hypotheses of every statement using it. -/
def dR (n r : ℕ) : ℕ := min (aInv n r) (n - aInv n r)

/-- `b_r(n) = min{2a_n − 1, 2n − 2a_n + 1}`, eq. (6), p.17. **Formalization Note** natural-number subtraction,
exact since `1 ≤ a_n < n` under the hypotheses of every statement using it. -/
def bR (n r : ℕ) : ℕ := min (2 * aInv n r - 1) (2 * n - 2 * aInv n r + 1)

end RobersonCx


