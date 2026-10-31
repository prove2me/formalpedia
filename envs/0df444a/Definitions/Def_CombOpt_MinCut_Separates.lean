-- Prove2me | Definitions.Def_CombOpt_MinCut_Separates
-- name    : CombOpt_MinCut_Separates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:19.038006+00:00
-- url     : https://prove2.me/theorems/73efa7d5-85e9-4181-bea1-119275567618
-- title:
--   A node set $S$ separates $v$ from $w$
-- statement:
--   Nodes $v,w$ are **separated** by a cut $\delta(S)$, or $\delta(S)$ is a **$(v,w)$-cut**, if exactly one of $v,w$ belongs to $S$.
--
--   The relation is symmetric in $v$ and $w$, and no set separates a node from itself.
--
--   **Formalization Note** The predicate is stated for the node set $S$ (`Xor (v ∈ S) (w ∈ S)`).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.5, p. 72 (PDF p. 81)

import Mathlib

namespace CombOpt.MinCut

/-- **A node set separating two nodes.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.5, p. 72
(PDF p. 81): "We say that nodes v, w of G are separated by a cut δ(S), or that δ(S) is a
(v, w)-cut, if exactly one of v, w is in S."

`Separates S v w` says that exactly one of `v`, `w` lies in `S`. It is symmetric in `v`, `w` and
false when `v = w`. -/
def Separates {V : Type*} (S : Finset V) (v w : V) : Prop :=
  Xor (v ∈ S) (w ∈ S)

end CombOpt.MinCut


