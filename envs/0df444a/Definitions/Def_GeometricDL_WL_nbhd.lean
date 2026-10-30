-- Prove2me | Definitions.Def_GeometricDL_WL_nbhd
-- name    : GeometricDL_WL_nbhd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:50.974349+00:00
-- url     : https://prove2.me/theorems/62b1bd41-fcb9-49ee-b29b-f02222679b37
-- title:
--   Neighbourhood $N_u=\{v:(u,v)\in E\text{ or }(v,u)\in E\}$ of a node, eq. (11)
-- statement:
--   Let $G=(V,E)$ be a graph with a finite set of nodes $V$ and edges $E\subseteq V\times V$. The **(undirected, 1-hop) neighbourhood** of a node $u\in V$ is
--
--   $$N_u=\{v\in V:\ (u,v)\in E\ \text{or}\ (v,u)\in E\}.$$
--
--   Every GNN layer of the mission aggregates over $N_u$, and so does each round of the Weisfeiler–Lehman test; $|N_u|$ is the degree of $u$.
--
--   **Formalization Note** $E$ is an arbitrary relation on a finite type $V$: edges may be directed and self-loops are allowed, so $u\in N_u$ exactly when $(u,u)\in E$ (the paper notes that "often, the node $u$ itself is included in its own neighbourhood"). The neighbourhood is symmetrised as in (11).
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §4.1, eq. (11), printed p. 34 (PDF p. 38); graph G = (V, E), E ⊆ V×V, printed p. 31 (PDF p. 35)

import Mathlib

namespace GeometricDL.WL

/-- **The (undirected) neighbourhood `N_u` of a node, eq. (11).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §4.1,
eq. (11), printed p. 34 (PDF p. 38): "A (undirected) neighbourhood of node u, sometimes also
called 1-hop, is defined as N_u = {v : (u, v) ∈ E or (v, u) ∈ E}" (§4.1, p. 31, PDF 35: "A graph
G = (V, E) is a collection of nodes V and edges E ⊆ V×V between pairs of nodes.")

For a finite node type `V` and an edge relation `E : V → V → Prop` (the paper's `E ⊆ V × V`),
`nbhd E u` is the finite set of nodes `v` with `E u v ∨ E v u`.

**Formalization Note.** `E` is an arbitrary relation: edges may be directed and loops `E u u`
are allowed, so `u ∈ nbhd E u` exactly when `u` has a self-loop (side note p. 34: "Often, the node
u itself is included in its own neighbourhood"). The neighbourhood is symmetrised as in (11). -/
def nbhd {V : Type*} [Fintype V] (E : V → V → Prop) [DecidableRel E] (u : V) : Finset V :=
  Finset.univ.filter (fun v => E u v ∨ E v u)

end GeometricDL.WL


