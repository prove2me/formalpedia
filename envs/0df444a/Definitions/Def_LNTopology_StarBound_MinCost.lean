-- Prove2me | Definitions.Def_LNTopology_StarBound_MinCost
-- name    : LNTopology_StarBound_MinCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:23.098691+00:00
-- url     : https://prove2.me/theorems/da2507ee-75a6-45e9-9523-d4274f8ab0fd
-- title:
--   §3.3 — minimal cost $c_{\min}(\mathcal F)$ of a Lightning Network supporting a flow
-- statement:
--   Let $V$ be a finite set of nodes, $c$ a channel cost function and $\mathcal F=(f_i)_{i\in V}$ a payment flow. The **minimal cost** of supporting $\mathcal F$ is
--   $$c_{\min}(\mathcal F)=\inf\{\,c(G)\;:\;G \text{ a Lightning Network on } V \text{ that supports } \mathcal F\,\}.$$
--
--   This is the benchmark against which the cost of any concrete topology, in particular the star, is measured.
--
--   **Formalization Note.** The paper writes $\min$. Since $c$ is not assumed continuous, the minimum need not be attained, and the infimum (`sInf`) is taken instead. When $\sum_i f_i=0$ the set is nonempty (a star supports $\mathcal F$) and bounded below by $0$, so the value is the genuine infimum. When $\sum_i f_i\neq 0$ no network supports $\mathcal F$ and the value is Lean's junk value $0$; every theorem using $c_{\min}$ therefore assumes $\sum_i f_i=0$. Competing networks live on the same node set $V$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 8 (PDF 9), §3.3, definition of c_min(F)

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model

namespace LNTopology.StarBound

/-- The minimal cost of supporting the flow `f` (SSRN 4439190, §3.3, p. 8):
`c_min(F) = inf { c(G) | G a Lightning Network on V supporting F }`. The paper writes `min`;
since `c` is not assumed continuous the minimum need not be attained, so the infimum is taken.
When `∑ i, f i = 0` the set is nonempty (a LNTopology.Local.star supports `f`) and bounded below by `0`, so
`sInf` is the genuine infimum; when `∑ i, f i ≠ 0` the set is empty and the value is junk. -/
noncomputable def cmin {V : Type*} [Fintype V] (c : ℝ → ℝ) (f : V → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ Λ : V → V → ℝ, IsLN Λ ∧ Supports Λ f ∧ cost c Λ = x}

end LNTopology.StarBound


