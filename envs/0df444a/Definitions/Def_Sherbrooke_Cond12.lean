-- Prove2me | Definitions.Def_Sherbrooke_Cond12
-- name    : Sherbrooke_Cond12
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:22:19.767468+00:00
-- url     : https://prove2.me/theorems/0510bfbf-754c-4e1b-a653-3a54210f38e6
-- title:
--   Condition (12): the marginal conditions on $\Xi'$ for one item
-- statement:
--   Fix one item with unit cost $c\in\mathbb R$ and function $\Xi:\mathbb N\to\mathbb R$, and let $\Xi'$ be its convexified function (the lower boundary of the convex hull of $\Xi$). A stock level $\bar m\in\mathbb N$ satisfies **condition (12)** when
--
--   $$
--   c+\Xi'(\bar m+1)-\Xi'(\bar m)\ \ge\ 0,\qquad c+\Xi'(\bar m)-\Xi'(\bar m-1)\ <\ 0,
--   $$
--
--   with the convention $\Xi'(-1)=\infty$, so that the second inequality holds automatically at $\bar m=0$.
--
--   The first inequality says that one more unit does not pay for itself; the second says that the last unit did. These are the marginal-analysis stopping conditions of the METRIC procedure, and the Appendix Theorem says they determine the optimal stock levels.
--
--   **Formalization Note** The convention $\Xi'(-1)=\infty$ is encoded as the disjunct "$\bar m=0$ or $c+\Xi'(\bar m)-\Xi'(\bar m-1)<0$", so the natural-number predecessor $\bar m-1$ is only used when $\bar m\ge1$. The page prints $\Xi'(\bar m_i-1)$ without the item index in the second line; it is read as $\Xi_i'$, the function of the same item.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, Theorem, eq. (12), p. 140, with the convention "Define Ξ_i′(−1) = ∞" from the proof, p. 140

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull

namespace Sherbrooke

/-- **Condition (12) for one item.** Sherbrooke, *METRIC*, Operations Research 16 (1968),
Appendix, Theorem, eq. (12), p. 140: the stock level `m̄_i` satisfies
`c_i + Ξ_i′(m̄_i + 1) − Ξ_i′(m̄_i) ≥ 0` and `c_i + Ξ_i′(m̄_i) − Ξ_i′(m̄_i − 1) < 0`,
with the convention "Define Ξ_i′(−1) = ∞" (proof of the Theorem, p. 140).

`Cond12 c Ξ m` holds when `0 ≤ c + Ξ′(m + 1) − Ξ′(m)` and either `m = 0` or
`c + Ξ′(m) − Ξ′(m − 1) < 0`, where `Ξ′ = lowerHull Ξ`.

**Formalization Note.** The disjunct `m = 0` encodes `Ξ_i′(−1) = ∞`: at `m = 0` the second line
reads `c + Ξ′(0) − ∞ = −∞ < 0`, which always holds. Under the guard `m ≠ 0` the natural-number
subtraction `m - 1` is the honest predecessor. The page prints `Ξ′(m̄_i − 1)` without the item
index in the second line; it is read as `Ξ_i′`, the function of the same item. -/
def Cond12 (c : ℝ) (Ξ : ℕ → ℝ) (m : ℕ) : Prop :=
  0 ≤ c + lowerHull Ξ (m + 1) - lowerHull Ξ m ∧
    (m = 0 ∨ c + lowerHull Ξ m - lowerHull Ξ (m - 1) < 0)

end Sherbrooke


