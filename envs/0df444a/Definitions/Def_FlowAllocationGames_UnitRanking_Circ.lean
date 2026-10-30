-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_Circ
-- name    : FlowAllocationGames_UnitRanking_Circ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:12:55.60103+00:00
-- url     : https://prove2.me/theorems/7dcee29a-7046-4645-bf57-4e530f4ea4b6
-- title:
--   Integral flow on the circulation network $G'$
-- statement:
--   The **circulation network** $G'$ adds to $G$ an auxiliary node $s$, an edge $(v, s)$ of capacity $\infty$ for every node $v$, and an edge $(s, v)$ of capacity $b_v$ for every node $v$. An integral flow on $G'$ is given by its values on the edges of $G$, on the edges $(v, s)$ and on the edges $(s, v)$.
--
--   Feasible flows of the game embed into $G'$ (Proposition 5), and the proof of Theorem 9 starts from an optimal circulation of $G'$.
--
--   **Formalization Note** The paper adds $(s, v)$ only when $b_v > 0$; here it is present for every $v$, with capacity $b_v$, so for $b_v = 0$ it carries no flow.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §3.1, p. 17

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Integral flow on the circulation network `G′`.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §3.1, p. 17:
"We add to G an auxiliary node s. For every v ∈ V, we add an auxiliary edge (v, s) with capacity
c(v,s) = ∞. For every v ∈ V with bv > 0 we add an auxiliary edge (s, v) with c(s,v) = bv".

A flow on `G′` records the flow `flow e` on every edge `e` of `G`, the flow `toS v` on the
auxiliary edge `(v, s)`, and the flow `fromS v` on the auxiliary edge `(s, v)`.

**Formalization Note.** The edge `(s, v)` is present for every `v`, with capacity `b v`; for
`b v = 0` it has capacity `0`, which adds no flow. Flows are integral (Reading 4 of the
mission). -/
structure Circ (n m : ℕ) where
  /-- Flow on each edge of `G`. -/
  flow : Fin m → ℕ
  /-- Flow on the auxiliary edge `(v, s)`. -/
  toS : Fin n → ℕ
  /-- Flow on the auxiliary edge `(s, v)`. -/
  fromS : Fin n → ℕ

end FlowAllocationGames.UnitRanking


