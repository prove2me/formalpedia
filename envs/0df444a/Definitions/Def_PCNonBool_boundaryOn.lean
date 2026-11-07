-- Prove2me | Definitions.Def_PCNonBool_boundaryOn
-- name    : PCNonBool_boundaryOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:46.026606+00:00
-- url     : https://prove2.me/theorems/15c4c1b9-6730-4cc8-9a03-e37034c0b3c9
-- title:
--   Boundary $\partial W$ of a pigeon set inside a hole set
-- statement:
--   In a bipartite graph $G=(U\sqcup V,E)$, the **boundary** of a set $W\subseteq U$ is the set of vertices of $V$ adjacent to exactly one vertex of $W$:
--   $$\partial_G W=\{\,v\in V : |\{u\in W:(u,v)\in E\}|=1\,\}.$$
--   Here the holes are restricted to a set $V_a$: $\partial W$ is taken among the holes of $V_a$. For $V_a=V$ this is $\partial_G W$; for $W\subseteq U_a$ it is the boundary of $W$ in the induced subgraph $G[U_a\sqcup V_a]$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2 (Boundary expansion), p.10 (PDF p.13)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph

namespace PCNonBool

/-- The boundary of a set `W` of pigeons inside the hole set `Va`: the holes of `Va` adjacent to
exactly one vertex of `W` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2, p.10 (PDF p.13): "the boundary of a set W ⊆ U is the
set of vertices in V that are adjacent to exactly one vertex in W"). With `Va = univ` this is
`∂_G W`; with `Va = V_ℓ` and `W ⊆ U_ℓ` it is the boundary in the induced subgraph
`G[U_ℓ ⊔ V_ℓ]`. -/
def boundaryOn {U V : Type*} (G : BipGraph U V) (Va : Finset V) (W : Finset U) : Finset V :=
  Va.filter (fun v => (W.filter (fun u => G.Adj u v)).card = 1)

end PCNonBool


