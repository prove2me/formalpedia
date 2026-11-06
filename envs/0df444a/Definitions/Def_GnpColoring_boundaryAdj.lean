-- Prove2me | Definitions.Def_GnpColoring_boundaryAdj
-- name    : GnpColoring_boundaryAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:38.37838+00:00
-- url     : https://prove2.me/theorems/9e2d43d3-451c-45b6-947e-0afd55031635
-- title:
--   The adjacency matrix $A_\partial$ of $G_\partial$
-- statement:
--   $A_\partial$ is the adjacency matrix, indexed by all of $V$, of the graph $G_\partial$ with edge set $\{\{u,v\}\in E(G): u\in S\text{ or }v\in S\}$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Corollary 3.26, p.33

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The adjacency matrix `A_∂` of `G_∂`**, the graph on `V` with
`E(G_∂) = {{u, v} ∈ E(G) : u ∈ S or v ∈ S}`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Corollary 3.26, p.33. -/
noncomputable def boundaryAdj {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun u v => if G.Adj u v ∧ (u ∈ S ∨ v ∈ S) then 1 else 0

end GnpColoring


