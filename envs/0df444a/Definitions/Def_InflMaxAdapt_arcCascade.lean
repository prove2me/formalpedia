-- Prove2me | Definitions.Def_InflMaxAdapt_arcCascade
-- name    : InflMaxAdapt_arcCascade
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:32:45.142211+00:00
-- url     : https://prove2.me/theorems/d04c67fb-f21f-46c8-be7d-f4c700e38bc0
-- title:
--   Cascade $C(S)$ of a seed set
-- statement:
--   For a set $A$ of live arcs and a seed set $S \subseteq V$, the **cascade** $C(S)$ is the set of vertices reachable from at least one vertex of $S$ along directed paths of live arcs. Paths of length zero count, so $S \subseteq C(S)$. A vertex of $C(S)$ is said to be **activated** by $S$, and $\sigma(S) = |C(S)|$ is the **influence** of $S$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib

namespace InflMaxAdapt

/-- The cascade `C(S)` (Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): the set of vertices
reachable from at least one vertex of `S ⊆ V` along directed paths of live arcs of `A` (paths of
length `0` included, so `S ⊆ C(S)`). -/
noncomputable def arcCascade {V : Type} [Fintype V] (A : Finset (V × V)) (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => ∃ s ∈ S, Relation.ReflTransGen (fun x y => (x, y) ∈ A) s w

end InflMaxAdapt


