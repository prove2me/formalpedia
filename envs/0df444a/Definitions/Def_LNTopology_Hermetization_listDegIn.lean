-- Prove2me | Definitions.Def_LNTopology_Hermetization_listDegIn
-- name    : LNTopology_Hermetization_listDegIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:53.813529+00:00
-- url     : https://prove2.me/theorems/11ac24e6-08a4-4eae-8482-e4dbf4a3f1ba
-- title:
--   Degree in an induced subgraph, from adjacency lists
-- statement:
--   For adjacency lists $\mathrm{adj}$, a vertex set $W$ and a vertex $v$, $d_W(v)$ is the number of entries of $\mathrm{adj}(v)$ that lie in $W$. For well-formed lists and $v\in W$ it is the degree of $v$ in the subgraph induced on $W$.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.3, p. 12 (PDF p. 13)

import Mathlib

namespace LNTopology.Hermetization

/-- **Degree in an induced subgraph, from adjacency lists.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.3, p. 12 ("finds a subgraph H with δ(H) ≥ …").

`listDegIn adj W v` is the number of entries of `adj v` that lie in `W`; for well-formed lists
(`WellFormedAdj`) and `v ∈ W` it is the degree of `v` in the subgraph induced on `W`. -/
def listDegIn {n : ℕ} (adj : Fin n → List (Fin n)) (W : Finset (Fin n)) (v : Fin n) : ℕ :=
  ((adj v).filter fun w => decide (w ∈ W)).length

end LNTopology.Hermetization


