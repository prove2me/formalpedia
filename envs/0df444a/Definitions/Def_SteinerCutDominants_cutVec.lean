-- Prove2me | Definitions.Def_SteinerCutDominants_cutVec
-- name    : SteinerCutDominants_cutVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:18.530786+00:00
-- url     : https://prove2.me/theorems/e87e0784-a012-427b-a0e0-aa012e949111
-- title:
--   The incidence vector $\chi(\delta(S))$ of a cut
-- statement:
--   Let $G$ be a graph and $S\subseteq V(G)$. The **cut** $\delta(S)$ is the set of all edges with one end node in $S$ and the other in $V\setminus S$, and its **incidence vector** $\chi(\delta(S))\in\{0,1\}^{E(G)}$ is given by
--   $$
--   \chi(\delta(S))_e=\begin{cases}1 & e\in\delta(S),\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   The paper identifies a cut with its incidence vector whenever cuts appear in a linear algebra context. Every polyhedral object of the mission is built from these vectors.
--
--   **Formalization Note** The vector is indexed by the edge type `G.edgeSet`, with real values. $S$ and its complement give the same vector.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §1, p.1

import Mathlib

namespace SteinerCutDominants

open Classical in
/-- The incidence vector `χ(δ(S)) ∈ {0,1}^{E(G)}` of the cut `δ(S)`, the set of edges with one end
in `S` and the other in `V \ S` (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2,
§1, p.1).

**Formalization Note** The cut is kept as a vector indexed by `G.edgeSet`, and `S` as a `Finset`.
The paper writes `δ(S)` for this vector too (p.7). `S` and its complement give the same vector. -/
noncomputable def cutVec {V : Type} (G : SimpleGraph V) (S : Finset V) : G.edgeSet → ℝ :=
  fun e => if ∃ u v, (e : Sym2 V) = s(u, v) ∧ u ∈ S ∧ v ∉ S then 1 else 0

end SteinerCutDominants


