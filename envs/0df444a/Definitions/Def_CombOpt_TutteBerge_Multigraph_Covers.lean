-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Covers
-- name    : CombOpt_TutteBerge_Multigraph_Covers
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:03.34098+00:00
-- url     : https://prove2.me/theorems/e5669bbf-dcc2-4b26-93a7-b541b6044cee
-- title:
--   A set of edges covers a node
-- statement:
--   Let $M\subseteq E$. The set $M$ **covers** the node $v$ if some edge of $M$ is incident with $v$, that is, if $v$ is an end of some $e\in M$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph

namespace CombOpt.TutteBerge

/-- **A set of edges covers a node.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "we say that M *covers* a node v (or that v is *M-covered*) if
some edge of M is incident with v."

An edge is incident with each of its ends (p. 9), so `e` is incident with `v` iff
`v ∈ G.ends e`. -/
def Multigraph.Covers {V E : Type*} (G : Multigraph V E) (M : Set E) (v : V) : Prop :=
  ∃ e ∈ M, v ∈ G.ends e

end CombOpt.TutteBerge


