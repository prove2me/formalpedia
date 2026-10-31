-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_gamma
-- name    : CombOpt_HeldKarp_Graph_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:39.775559+00:00
-- url     : https://prove2.me/theorems/02ada746-cdbf-4bef-9e56-b31c4d8c131a
-- title:
--   The edge set $\gamma(S)$ inside a node set
-- statement:
--   For $S\subseteq V$, $\gamma(S)$ is the set of edges both of whose ends lie in $S$ (loops at nodes of $S$ included).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph

namespace CombOpt.HeldKarp

open Classical in
/-- **The edge set γ(S) inside a node set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12
(PDF p. 21): "γ(A) the set {e ∈ E : both ends of e are in A}".

`G.gamma S` is the set of edges both of whose ends lie in `S`.

**Formalization Note.** A loop at a node of `S` is in `γ(S)`. -/
noncomputable def Graph.gamma {V E : Type*} [Fintype E] (G : Graph V E) (S : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => ∀ a ∈ G.ends e, a ∈ S)

end CombOpt.HeldKarp


