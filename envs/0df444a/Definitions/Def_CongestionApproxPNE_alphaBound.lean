-- Prove2me | Definitions.Def_CongestionApproxPNE_alphaBound
-- name    : CongestionApproxPNE_alphaBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:42.484986+00:00
-- url     : https://prove2.me/theorems/b81668a6-4b5e-491e-b99d-8d04796f53a3
-- title:
--   The nonexistence bound $\alpha(d)$, (3)
-- statement:
--   For an integer $d$, the **nonexistence bound** of Theorem 1 is
--
--   $$
--   \alpha(d)=\sup_{n,k,w,\beta}\ \min\left\{\frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta},\ \frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d}\right\}
--   \quad\text{s.t. } n\in\mathbb N,\ k\in\{1,\dots,d\},\ w\in[0,1],\ \beta\in[0,1]. \tag{3}
--   $$
--
--   It is the best lower bound obtained from the family of gadgets $\mathcal G^d_{(n,k,w,\beta)}$: each gadget has no $\alpha$-PNE for $\alpha$ below both ratios. The paper reports $\alpha(2)\approx 1.054$, $\alpha(3)\approx 1.107$, $\alpha(4)\approx 1.153$.
--
--   **Formalization Note** The supremum is the real `sSup` over the points at which (3) is defined, i.e. where the second denominator $(nw)^k+\beta(1+w)^d$ is positive; the excluded points ($nw=0$, $\beta=0$) would contribute the value $1$ under the convention $1/0=+\infty$, and $1$ is already attained (at $n=0$, $k=d$, $w=\beta=1$), so the supremum is unchanged. $n$ ranges over $\mathbb N$ including $0$. The set is nonempty and bounded above by $2^d$, so the supremum is a genuine real supremum.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Theorem 1, display (3), p.4 (PDF p.5)

import Mathlib
import Definitions.Def_CongestionApproxPNE_ratioOne
import Definitions.Def_CongestionApproxPNE_ratioTwo

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The nonexistence bound `α(d)`**, display (3).
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, Theorem 1, p.4:
"α(d) = sup_{n,k,w,β} min{ (1 + nβ(1 + w)^d)/((1 + nw)^k + nβ), ((1 + w)^k + βw^d)/((nw)^k + β(1 + w)^d) }
(3) s.t. n ∈ N, k ∈ {1, . . . , d}, w ∈ [0, 1], β ∈ [0, 1]."

The real supremum of `min(ratioOne, ratioTwo)` over all `n ∈ ℕ`, `k ∈ {1,…,d}`, `w ∈ [0,1]`,
`β ∈ [0,1]` at which (3) is defined.

**Formalization Note** The points where the second denominator `(nw)^k + β(1+w)^d` is `0` (exactly
`nw = 0` and `β = 0`) are excluded: (3) is undefined there. Under the convention `1/0 = +∞` they
would contribute `min = ratioOne = 1`, and the set already contains the value `1` (at
`n = 0, k = d, w = β = 1`), so the supremum is the same. `n` ranges over `ℕ` including `0`, which
only adds values `≤ 1`. The set is nonempty and bounded above by `2^d` (min ≤ ratioOne ≤
(1+w)^d), so `sSup` is the genuine supremum. -/
noncomputable def alphaBound (d : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ (n k : ℕ) (w β : ℝ), 1 ≤ k ∧ k ≤ d ∧ 0 ≤ w ∧ w ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 ∧
    0 < ((n : ℝ) * w) ^ k + β * (1 + w) ^ d ∧
    r = min (ratioOne d n k w β) (ratioTwo d n k w β)}

end CongestionApproxPNE


