-- Prove2me | Definitions.Def_FastReachability
-- name    : FastReachability
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-11T17:33:33.605007+00:00
-- url     : https://prove2.me/theorems/852ba404-d4ce-4547-ad13-5e83ef35289d
-- title:
--   Computable reachability for finite graphs (neighbour closure)
-- statement:
--   Mathlib decides reachability in a finite simple graph through `SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty`, which asks whether some walk of length less than $|V|$ joins the two vertices. That is a correct decision procedure but an impractical one: the number of walks grows exponentially, and in practice it becomes unusable past roughly ten vertices.
--
--   This file supplies the standard alternative, neighbour closure. For a finite simple graph $G$ on a vertex type $V$ with decidable adjacency, define one *round* of closure on a finite set $s \subseteq V$ by
--
--   $$\operatorname{step}(s) \;=\; s \;\cup\; \{\, v \in V \;:\; \exists\, u \in s,\ u \sim_G v \,\}.$$
--
--   Each round either enlarges $s$ or leaves it unchanged, so after $|V|$ rounds the process has certainly stabilised. The reachable set from a vertex $u$ is therefore defined as
--
--   $$\operatorname{reachSet}(u) \;=\; \operatorname{step}^{\,|V|}\bigl(\{u\}\bigr).$$
--
--   This is the usual breadth-first characterisation of a connected component, expressed so that it evaluates: `step` is a `Finset` operation built from `filter` and `union`, and iterating it a fixed number of times gives a closed-form `Finset` rather than a search over walks.
--
--   The accompanying theorem `FastReach.mem_reachSet_iff` states that this really does compute reachability, $v \in \operatorname{reachSet}(u) \iff G.\mathrm{Reachable}\ u\ v$, which is what makes the construction usable as a drop-in replacement for Mathlib's decision procedure.
--
--   **Formalization Note** Imports are deliberately narrow — only `Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite` — so that downstream files stay cheap to compile. `step` takes the graph explicitly and requires `[DecidableRel G.Adj]`; `reachSet` additionally uses `Fintype.card V` as the iteration count. No finiteness assumption beyond `[Fintype V] [DecidableEq V]` is needed.
-- source:
--   Standard neighbour-closure (breadth-first) characterisation of connected components; see e.g. G. R. Grimmett, Percolation, 2nd ed., Springer 1999, or any algorithms text. Motivated by Mathlib SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty (Mathlib/Combinatorics/SimpleGraph/Connectivity/Finite.lean), which decides reachability by enumerating all walks of length < |V| and is infeasible beyond ~10 vertices. Contributed as infrastructure for the mission The Bunkbed Conjecture is False.

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Computable reachability for finite graphs

Mathlib decides `SimpleGraph.Reachable` via `reachable_iff_exists_finsetWalkLength_nonempty`,
which enumerates every walk of length `< |V|`; that is infeasible past roughly ten vertices.
This file provides the standard neighbour-closure alternative: iterate "add all neighbours of
the current set" `|V|` times starting from `{u}`.
-/

namespace FastReach

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One round of neighbour closure: add every vertex adjacent to something already in `s`. -/
def step (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Finset V :=
  s ∪ univ.filter (fun v => ∃ u ∈ s, G.Adj u v)

/-- The vertices reachable from `u`, obtained by iterating neighbour closure `|V|` times.
Since each round either grows the set or has reached a fixed point, `|V|` rounds suffice. -/
def reachSet (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  (step G)^[Fintype.card V] {u}

end FastReach


