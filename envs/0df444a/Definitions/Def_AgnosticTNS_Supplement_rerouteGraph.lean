-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_rerouteGraph
-- name    : AgnosticTNS_Supplement_rerouteGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:33:55.011917+00:00
-- url     : https://prove2.me/theorems/f1ed109e-bbde-4e3f-a9a8-0058abac46a5
-- title:
--   Rerouted graph $G'=([n],(E\setminus\{\{x,y\}\})\cup\{\{x,z\},\{y,z\}\})$
-- statement:
--   For a graph $G=([n],E)$, an edge $\{x,y\}\in E$ and a vertex $z\notin\{x,y\}$, the **rerouted graph** is $G'=([n],E')$ with
--   $$
--   E' := (E\setminus\{\{x,y\}\})\cup\{\{x,z\},\{y,z\}\}.
--   $$
--   The edge $\{x,y\}$ is removed and its virtual index is routed through $z$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.8, Eq. (6.7), p.49

import Mathlib

namespace AgnosticTNS.Supplement

/-- **The rerouted graph** `G′ = ([n], E′)`, `E′ := (E ∖ {{x, y}}) ∪ {{x, z}, {y, z}}`, Eq. (6.7),
Theorem 6.8, p.49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).

**Formalization Note** `SimpleGraph.fromEdgeSet` (diagonal pairs are discarded; for `z ∉ {x, y}`
and `x ≠ y` there are none). -/
def rerouteGraph {n : ℕ} (G : SimpleGraph (Fin n)) (x y z : Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet ((G.edgeSet \ {s(x, y)}) ∪ {s(x, z), s(y, z)})

end AgnosticTNS.Supplement


