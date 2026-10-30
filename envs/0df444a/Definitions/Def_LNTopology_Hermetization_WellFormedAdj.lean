-- Prove2me | Definitions.Def_LNTopology_Hermetization_WellFormedAdj
-- name    : LNTopology_Hermetization_WellFormedAdj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:36.865204+00:00
-- url     : https://prove2.me/theorems/a610998e-0296-4f68-905c-ff9a1c5e4304
-- title:
--   Adjacency lists of a simple graph
-- statement:
--   A family of lists $(\mathrm{adj}(v))_{v\in\{0,\dots,n-1\}}$ is a **well-formed adjacency-list representation** of a simple graph when, for all vertices $v,w$:
--
--   1. $w$ is listed at $v$ if and only if $v$ is listed at $w$;
--   2. $v$ is not listed at $v$ (no loops);
--   3. no vertex is listed twice at $v$.
--
--   Then $\sum_v|\mathrm{adj}(v)|=2|E|$. Lemma B.3's running time $O(V+E)$ refers to this input format; with an adjacency matrix it is unattainable.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.3, p. 12 (PDF p. 13)

import Mathlib

namespace LNTopology.Hermetization

/-- **Adjacency lists of a simple graph.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.3, p. 12 ("given a graph G … The running time of the algorithm is O(V + E)").

`adj v` lists the neighbours of `v`. The lists are symmetric (`w` is listed at `v` iff `v` is
listed at `w`), loopless and duplicate-free, i.e. they are the adjacency lists of a simple graph
on `Fin n`, and `Σ_v (adj v).length = 2|E|`.

**Formalization Note.** Reading R5: O(V + E) presupposes the adjacency-list representation; with
an adjacency matrix it is unattainable. -/
def WellFormedAdj {n : ℕ} (adj : Fin n → List (Fin n)) : Prop :=
  ∀ v w : Fin n, (w ∈ adj v ↔ v ∈ adj w) ∧ v ∉ adj v ∧ (adj v).Nodup

end LNTopology.Hermetization


