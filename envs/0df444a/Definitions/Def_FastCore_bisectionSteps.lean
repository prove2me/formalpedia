-- Prove2me | Definitions.Def_FastCore_bisectionSteps
-- name    : FastCore_bisectionSteps
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:47.788564+00:00
-- url     : https://prove2.me/theorems/eff81d23-d19f-49f1-b9ab-81952e25d847
-- title:
--   Bisection step bound $\lceil\log_2(n/\epsilon)\rceil_+$
-- statement:
--   This is the natural number $\lceil\log_2(n/\epsilon)\rceil_+$, the positive part of the ceiling. It bounds the number of bisection steps of one run of Core-Search on a set of at most $n$ bidders: after $k$ steps $\Delta_h-\Delta_l=2^{-k}$, and the search stops once this is at most $\epsilon/|S|$.
--
--   **Formalization Note** For $n/\epsilon\le1$ the value is $0$, which is correct, since no step is made. The paper writes $\log(|S_{t+1}|/\epsilon)$ without a ceiling.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, p.20

import Mathlib

namespace FastCore

/-- `⌈log₂(n/ε)⌉₊`, the bound on the number of bisection steps of one Core-Search on a set of at most
`n` bidders (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, p.20).

**Formalization Note.** After `k` steps `Δh − Δl = 2⁻ᵏ`, so the exact count on `S` is
`⌈log₂(|S|/ε)⌉₊`. For `n/ε ≤ 1` the value is `0`, which is correct: no step is made. The paper writes
`log(|S|/ε)` without the ceiling. -/
noncomputable def bisectionSteps (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ((n : ℝ) / ε)⌉₊

end FastCore


