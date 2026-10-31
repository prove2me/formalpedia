-- Prove2me | Definitions.Def_CongestionApproxPNE_ratioTwo
-- name    : CongestionApproxPNE_ratioTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:44.237997+00:00
-- url     : https://prove2.me/theorems/7bf6c8da-e1e6-4ea6-a0ac-7995ac88b8cf
-- title:
--   The second ratio of (3), $\frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d}$
-- statement:
--   For $d,n,k\in\mathbb N$ and reals $w,\beta$, the second ratio of the nonexistence bound (3) is
--
--   $$
--   r_2(n,k,w,\beta)=\frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d}.
--   $$
--
--   In the gadget it bounds below the improvement factor of a light player who shares the heavy player's hub (Case 2 of the proof of Theorem 1).
--
--   **Formalization Note** The denominator vanishes exactly when $nw=0$ and $\beta=0$ (for $k\ge 1$); there (3) is undefined, and the definition of $\alpha(d)$ excludes those points rather than using Lean's convention $x/0=0$.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Theorem 1, display (3), p.4 (PDF p.5); proof of Theorem 1, Case 2, p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The second ratio of (3)**, `((1+w)^k + βw^d) / ((nw)^k + β(1+w)^d)`.
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, Theorem 1, display
(3), p.4 (a light player's improvement factor in Case 2 of the proof, p.5).

**Formalization Note** `n, k, d : ℕ` and `w, β : ℝ`. The denominator vanishes when `nw = 0` and
`β = 0` (with `k ≥ 1`), where (3) is undefined; Lean's `x / 0 = 0` is never used there, since
`alphaBound` only takes points with a positive denominator. -/
noncomputable def ratioTwo (d n k : ℕ) (w β : ℝ) : ℝ :=
  ((1 + w) ^ k + β * w ^ d) / (((n : ℝ) * w) ^ k + β * (1 + w) ^ d)

end CongestionApproxPNE


