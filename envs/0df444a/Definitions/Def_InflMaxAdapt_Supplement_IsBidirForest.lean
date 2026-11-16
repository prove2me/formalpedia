-- Prove2me | Definitions.Def_InflMaxAdapt_Supplement_IsBidirForest
-- name    : InflMaxAdapt_Supplement_IsBidirForest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:43:11.940199+00:00
-- url     : https://prove2.me/theorems/2b6499dc-90bb-41a6-a067-c98738fe9ef1
-- title:
--   Bi-directed forest instance
-- statement:
--   Let $(V, \mathbf p)$ be an instance of influence maximization: a finite vertex set $V$ and arc probabilities $\mathbf p \in [0,1]^{V^2}$. Its **support graph** is the undirected simple graph on $V$ with an edge $\{u, v\}$ for each pair of distinct vertices $u \ne v$ such that
--   $$
--   p_{u,v} > 0 \quad\text{or}\quad p_{v,u} > 0 .
--   $$
--   The instance is a **bi-directed forest** if its support graph is a forest, i.e. contains no cycle.
--
--   The two opposite arcs $(u,v)$ and $(v,u)$ of an edge remain independent and may have different probabilities, one of them possibly $0$; so every orientation of a forest (in- or out-arborescences) and every undirected forest is a bi-directed forest. This is the hypothesis of Theorem 3.
--
--   **Formalization Note** The support graph is Mathlib's `SimpleGraph.fromRel` of the relation $0 < p_{u,v} \lor 0 < p_{v,u}$, which drops loops $(v,v)$ (they never change a cascade) and symmetrises; acyclicity is `SimpleGraph.IsAcyclic`.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 4, printed p.11 (PDF p.12), definition of a bi-directed forest; also Section 1.2, printed p.3 (PDF p.4)

import Mathlib

namespace InflMaxAdapt.Supplement

/-- The **support graph** of an instance `(V, p)` and the **bi-directed forest** predicate
(Section 4, printed p.11 = PDF p.12, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence
Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256
67dfe75c…abe5d5)): "An instance `(V, p)` is a bi-directed forest if the undirected graph on `V`
with an edge `{u, v}` for each pair of distinct vertices with `p_{u,v} > 0` or `p_{v,u} > 0` is a
forest." The two opposite arcs of an edge stay independent and may have different probabilities.

**Formalization Note** `SimpleGraph.fromRel r` has `u ~ v ↔ u ≠ v ∧ (r u v ∨ r v u)`, so loops
`(v, v)` (which never change a cascade) are ignored and the relation is symmetrised; a forest is a
Mathlib `SimpleGraph.IsAcyclic` graph. Positivity is strict (`0 < p`), as on the page. -/
def IsBidirForest {V : Type} (p : V → V → ℝ) : Prop :=
  (SimpleGraph.fromRel fun u v => 0 < p u v ∨ 0 < p v u).IsAcyclic

end InflMaxAdapt.Supplement


