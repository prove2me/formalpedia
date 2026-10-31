-- Prove2me | Definitions.Def_ContPatrol_Multigraph
-- name    : ContPatrol_Multigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:52.060988+00:00
-- url     : https://prove2.me/theorems/c8b8354c-da08-4b43-b720-78920a5c746f
-- title:
--   Finite multigraph: darts, degree, walks, connectivity
-- statement:
--   A **multigraph** $G$ has a set $V$ of vertices, a set $E$ of edges, and for every edge $e$ an initial vertex $\mathrm{src}(e)$ and a terminal vertex $\mathrm{tgt}(e)$. Loops ($\mathrm{src}(e)=\mathrm{tgt}(e)$) and parallel edges are allowed.
--
--   1. A **dart** is an edge with a direction: $(e,\mathrm{true})$ runs from $\mathrm{src}(e)$ to $\mathrm{tgt}(e)$ and $(e,\mathrm{false})$ the other way. Its **tail** is the vertex it leaves, its **head** the vertex it reaches, and its **reverse** is the same edge in the other direction.
--   2. The **degree** $\deg v$ is the number of edge ends at $v$; a loop counts twice.
--   3. A **walk** from $u$ to $w$ is a list of darts, each starting where the previous one ends; $G$ is **connected** if every two vertices are joined by a walk.
--   4. A **closed dart walk** is a nonempty cyclic list of darts in which each dart starts where the previous one ends, including the wrap-around from the last dart to the first.
--
--   This is the combinatorial skeleton of the networks on which the continuous patrolling game is played; tours, circuits and Eulerian tours are all closed dart walks.
--
--   **Formalization Note** The orientation $\mathrm{src}\to\mathrm{tgt}$ is only a coordinate convention: it fixes the end from which positions along the edge are measured.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, pp.4–5

import Mathlib

namespace ContPatrol

/-- **The underlying finite multigraph of a network.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.4:
"To define Q, we begin with a graph G with edges and vertices".

The vertices are the type `V`, the edges the type `E`; edge `e` runs from `src e` to `tgt e`.

**Formalization Note.** Loops (`src e = tgt e`) and parallel edges are allowed, as the paper
uses both (the three-arc network, p.13; "For loops, an arc may be repeated consecutively",
p.12). The orientation `src → tgt` is only a coordinate convention: it fixes from which end the
position along the edge is measured (§3, p.4: an edge is identified with an open interval).
A *dart* is an edge with a direction, `(e, true)` running `src e → tgt e` and `(e, false)`
running `tgt e → src e`. The *degree* of a vertex counts a loop twice, matching the paper's
degree of a point (the number of components of a punctured neighbourhood, p.5). -/
structure Multigraph (V E : Type) where
  /-- The initial vertex of each edge (the end at offset 0). -/
  src : E → V
  /-- The terminal vertex of each edge. -/
  tgt : E → V

namespace Multigraph

variable {V E : Type}

/-- The vertex a dart leaves from. -/
def tail (G : Multigraph V E) (d : E × Bool) : V := if d.2 then G.src d.1 else G.tgt d.1

/-- The vertex a dart arrives at. -/
def head (G : Multigraph V E) (d : E × Bool) : V := if d.2 then G.tgt d.1 else G.src d.1

/-- The reverse dart: the same edge traversed in the opposite direction. -/
def rev (d : E × Bool) : E × Bool := (d.1, !d.2)

/-- The degree of a vertex: the number of edge ends at it (a loop counts twice). -/
def deg [Fintype E] [DecidableEq V] (G : Multigraph V E) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => G.src e = v)).card +
    (Finset.univ.filter (fun e => G.tgt e = v)).card

/-- `G.IsWalk u w ds`: the list of darts `ds` is a walk from `u` to `w` (each dart starts where
the previous one ends; the empty list is the walk from `u` to `u`). -/
def IsWalk (G : Multigraph V E) : V → V → List (E × Bool) → Prop
  | u, w, [] => u = w
  | u, w, d :: ds => G.tail d = u ∧ IsWalk G (G.head d) w ds

/-- The multigraph is connected: any two vertices are joined by a walk. -/
def Connected (G : Multigraph V E) : Prop := ∀ u w : V, ∃ ds, G.IsWalk u w ds

/-- `G.IsClosedDartWalk w`: `w` is a nonempty cyclic sequence of darts in which each dart starts
where the previous one ends, including the wrap-around from the last dart to the first. -/
def IsClosedDartWalk (G : Multigraph V E) (w : List (E × Bool)) : Prop :=
  w ≠ [] ∧ ∀ (i : ℕ) (hi : i < w.length),
    G.head w[i] = G.tail (w[(i + 1) % w.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))

end Multigraph

end ContPatrol


