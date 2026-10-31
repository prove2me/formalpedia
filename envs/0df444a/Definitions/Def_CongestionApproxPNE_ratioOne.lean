-- Prove2me | Definitions.Def_CongestionApproxPNE_ratioOne
-- name    : CongestionApproxPNE_ratioOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:40.814019+00:00
-- url     : https://prove2.me/theorems/2613046b-7d00-4294-b0a3-8db2aa590915
-- title:
--   The first ratio of (3), $\frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta}$
-- statement:
--   For $d,n,k\in\mathbb N$ and reals $w,\beta$, the first ratio of the nonexistence bound (3) is
--
--   $$
--   r_1(n,k,w,\beta)=\frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta}.
--   $$
--
--   In the gadget $\mathcal G^d_{(n,k,w,\beta)}$ it is the factor by which the heavy player improves when she is alone on her hub resource (Case 1 of the proof of Theorem 1). For $w,\beta\ge 0$ the denominator is at least $1$.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Theorem 1, display (3), p.4 (PDF p.5); proof of Theorem 1, Case 1, p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The first ratio of (3)**, `(1 + nβ(1+w)^d) / ((1+nw)^k + nβ)`.
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, Theorem 1, display
(3), p.4 (the heavy player's improvement factor in Case 1 of the proof, p.5).

**Formalization Note** `n, k, d : ℕ` and `w, β : ℝ`. The denominator is at least `1` whenever
`w, β ≥ 0`, so the division is never by `0` on the domain of (3). -/
noncomputable def ratioOne (d n k : ℕ) (w β : ℝ) : ℝ :=
  (1 + (n : ℝ) * β * (1 + w) ^ d) / ((1 + (n : ℝ) * w) ^ k + (n : ℝ) * β)

end CongestionApproxPNE


