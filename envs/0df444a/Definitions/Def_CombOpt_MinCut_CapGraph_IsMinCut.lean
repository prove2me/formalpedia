-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph_IsMinCut
-- name    : CombOpt_MinCut_CapGraph_IsMinCut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:55.036285+00:00
-- url     : https://prove2.me/theorems/68691047-d6b4-45bd-89e2-326fed840230
-- title:
--   $\delta(S)$ is a minimum $(v,w)$-cut
-- statement:
--   For a finite capacitated graph $G$, a node set $S$ and nodes $v,w$, $\delta(S)$ is a **minimum $(v,w)$-cut** if
--
--   1. $S$ separates $v$ from $w$ (exactly one of $v,w$ lies in $S$), and
--   2. $u(\delta(S))\le u(\delta(T))$ for every $T\subseteq V$ separating $v$ from $w$.
--
--   Theorem 3.36 asserts that the star of the last node of a legal ordering is such a cut.
--
--   **Formalization Note** The book's cut is the edge set $\delta(S)$; the predicate is stated for the node set $S$ presenting it. Its capacity depends only on the edge set.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.5, pp. 72–73 (PDF pp. 81–82)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_uSum
import Definitions.Def_CombOpt_MinCut_CapGraph_delta
import Definitions.Def_CombOpt_MinCut_Separates

namespace CombOpt.MinCut

/-- **`δ(S)` is a minimum `(v, w)`-cut.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.5,
pp. 72–73 (PDF pp. 81–82): δ(S) is a (v, w)-cut "if exactly one of v, w is in S", and a minimum
(v, w)-cut is one of least capacity `u(δ(S))`.

`G.IsMinCut S v w` says that `S` separates `v` from `w` and that `u(δ(S)) ≤ u(δ(T))` for every
`T ⊆ V` separating `v` from `w`.

**Formalization Note.** The book's cut is the edge set `δ(S)`; the predicate is stated for the
node set `S` defining it. This changes nothing: whether an edge set `δ(T)` is a (v, w)-cut is a
property of the set `T` chosen to present it, and its capacity depends only on the edge set. -/
def CapGraph.IsMinCut {V E : Type*} [Fintype E] (G : CapGraph V E) (S : Finset V) (v w : V) :
    Prop :=
  Separates S v w ∧ ∀ T : Finset V, Separates T v w → G.uSum (G.delta S) ≤ G.uSum (G.delta T)

end CombOpt.MinCut


