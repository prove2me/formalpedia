-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_IsDipath
-- name    : CombOpt_MatroidIntersection_IsDipath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:34.965285+00:00
-- url     : https://prove2.me/theorems/4a69193c-bc17-4fdb-9fe4-056dc809226a
-- title:
--   Dipath given by its node sequence
-- statement:
--   In a digraph, a **dipath** (directed path) from $u$ to $v$ is a path $v_0,a_1,v_1,\dots,a_k,v_k$ with $v_0=u$, $v_k=v$, in which every arc $a_i$ is forward, i.e. has tail $v_{i-1}$ and head $v_i$. Nodes may repeat.
--
--   **Formalization Note** For a digraph given by an arc relation (no parallel arcs), a dipath is recorded by its node sequence: a nonempty list $[v_0,\dots,v_k]$ starting at $u$, ending at $v$, with $v_{i-1}v_i$ an arc for $1\le i\le k$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 19 (PDF p. 28)

import Mathlib

namespace CombOpt.MatroidIntersection

/-- **A `(u, v)`-dipath, given by its node sequence.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2,
p. 19 (PDF p. 28): "An arc e_i of a path P : v₀, e₁, v₁, …, e_k, v_k is *forward* if
t(e_i) = v_{i−1} and h(e_i) = v_i, and is reverse otherwise. A path in which every arc is forward
is a *directed path* or *dipath*." A dipath from v₀ to v_k is a (v₀, v_k)-dipath.

For a digraph given by its arc relation `arc` (with at most one arc from any node to any other),
`IsDipath arc P u v` says that the list `P = [v₀, v₁, …, v_k]` is nonempty, starts at `u`, ends at
`v`, and `v_{i−1} v_i` is an arc for every `1 ≤ i ≤ k`.

**Formalization Note.** A dipath is recorded by its node sequence, which determines its arcs
when there are no parallel arcs (the case of the auxiliary digraph of §8.3). Nodes may repeat,
as in the book's paths (p. 10). -/
def IsDipath {V : Type*} (arc : V → V → Prop) (P : List V) (u v : V) : Prop :=
  P.head? = some u ∧ P.getLast? = some v ∧ P.IsChain arc

end CombOpt.MatroidIntersection


