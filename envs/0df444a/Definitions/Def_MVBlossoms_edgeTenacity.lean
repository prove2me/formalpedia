-- Prove2me | Definitions.Def_MVBlossoms_edgeTenacity
-- name    : MVBlossoms_edgeTenacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:14.969889+00:00
-- url     : https://prove2.me/theorems/60eccfcd-c568-41dc-86d7-e914a735878f
-- title:
--   Tenacity of an edge
-- statement:
--   For an edge $(u,v)$ of $G$,
--
--   $$
--   \mathrm{tenacity}(u,v)=\begin{cases}\mathrm{even\ level}(u)+\mathrm{even\ level}(v)+1 & (u,v)\notin M,\\ \mathrm{odd\ level}(u)+\mathrm{odd\ level}(v)+1 & (u,v)\in M,\end{cases}
--   $$
--
--   with $\infty+x=\infty$. It is the length of the shortest closed alternating structure through the edge and decides which bridges are processed at which stage.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 8, p.2018

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel

namespace MVBlossoms

/-- **Tenacity of an edge.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 8, p.2018: "If (u, v) is an unmatched
edge, then tenacity(u,v) = even level(u) + even level(v) + 1, and if it is matched,
tenacity(u,v) = odd level(u) + odd level(v) + 1."

**Formalization Note.** "Matched" means `s(u, v) ∈ M.edgeSet`. The value is in `ℕ∞` (it is `⊤`
when a summand is). The function is symmetric in `u, v` and is only used on edges of `G`. -/
noncomputable def edgeTenacity {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (u v : V) : ℕ∞ := by
  classical
  exact if s(u, v) ∈ M.edgeSet then oddLevel M u + oddLevel M v + 1
    else evenLevel M u + evenLevel M v + 1

end MVBlossoms


