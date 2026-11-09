-- Prove2me | Definitions.Def_InflMaxAdapt_IsUndirected
-- name    : InflMaxAdapt_IsUndirected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:32:40.882215+00:00
-- url     : https://prove2.me/theorems/ff42069c-f378-450a-a012-d7f13255c019
-- title:
--   Undirected instance
-- statement:
--   An instance $(V, \mathbf p)$ is **undirected** if
--   $$
--   p_{u,v} = p_{v,u} \qquad \text{for every } u, v \in V .
--   $$
--   The two arcs $(u,v)$ and $(v,u)$ of a pair are still live independently of each other.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib

namespace InflMaxAdapt

/-- An instance `(V, p)` is undirected if `p_{u,v} = p_{v,u}` for every `u, v ∈ V`
(Section 2, printed p.5 = PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)). The arcs `(u, v)` and `(v, u)` remain independent. -/
def IsUndirected {V : Type} (p : V → V → ℝ) : Prop :=
  ∀ u v, p u v = p v u

end InflMaxAdapt


