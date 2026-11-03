-- Prove2me | Definitions.Def_RiskAverseConsistency_optimalValue
-- name    : RiskAverseConsistency_optimalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:27.907198+00:00
-- url     : https://prove2.me/theorems/cc63d81c-d9bc-457a-9189-ed2108742175
-- title:
--   Optimal value $\inf_{z\in S}g(z)$ in $[-\infty,\infty]$
-- statement:
--   For a set $S$ and $g:S\to[-\infty,\infty]$, the **optimal value** is
--
--   $$
--   \inf_{z\in S}g(z)\in[-\infty,\infty].
--   $$
--
--   It is the paper's $\mathfrak m_k^*$, $\mathfrak m^*$ in (5) and $m^*$, $\hat m_N^*$ for problems (8) and (10).
--
--   **Formalization Note** The infimum is taken in `EReal`, so it equals $+\infty$ on the empty set and $-\infty$ when unbounded below; no junk value occurs.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.6, (5); p.9

import Mathlib

namespace RiskAverseConsistency

/-- The **optimal value** `inf_{z ∈ S} g(z)` of an extended-real-valued function over a set, in
`EReal = [−∞, ∞]`.

Milz, Surowiec, arXiv:2207.14756v2, (5), p.6 (`𝔪*ₖ`, `𝔪*`), and p.9 (`m*`, `m̂*_N`, the optimal
values of (8) and (10)).

Formalization Note: the infimum is taken in `EReal`, so it is `+∞` on the empty set and `−∞` when
unbounded below; no junk value arises. -/
noncomputable def optimalValue {V : Type*} (S : Set V) (g : V → EReal) : EReal :=
  ⨅ z ∈ S, g z

end RiskAverseConsistency


