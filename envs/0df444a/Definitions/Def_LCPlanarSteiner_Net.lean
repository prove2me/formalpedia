-- Prove2me | Definitions.Def_LCPlanarSteiner_Net
-- name    : LCPlanarSteiner_Net
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:22.584062+00:00
-- url     : https://prove2.me/theorems/715a9496-3d01-463a-a693-27573c98da0d
-- title:
--   A directed graph with rational arc costs and lengths
-- statement:
--   A **graph** $G = (V, E)$ has vertices $V = \{0, \dots, n-1\}$ and a finite list $E$ of arcs; the arc with index $e$ has a tail, a head, a cost $c_e$ and a length $\ell_e$, all read from the list. Parallel and antiparallel arcs, loops and zero costs or lengths are allowed, and parallel arcs are distinct arcs because an arc is named by its position.
--
--   $G$ is **well-formed** when every endpoint is a vertex and every cost and length is nonnegative:
--   $$
--   \mathrm{tail}(e), \mathrm{head}(e) < n,\qquad c_e \ge 0,\qquad \ell_e \ge 0 \qquad (e \in E).
--   $$
--   The set of all arc indices is $E = \{0, \dots, m-1\}$.
--
--   This is the input graph of the paper: nonnegative rational edge costs and lengths, encoded in binary.
--
--   **Formalization Note** The accessors return $0$ for an index outside the list; walks check that every index is in range. Well-formedness is a hypothesis of the guarantees, not part of the type, so every algorithm is a function on all inputs.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2; §3, p.4 (cycles, parallel and antiparallel edges, zero costs or lengths allowed)

import Mathlib

namespace LCPlanarSteiner

/-- **A directed graph with nonnegative rational edge costs and lengths.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2: "Let G = (V, E) have
nonnegative rational edge costs c_e and lengths ℓ_e, encoded in binary"; §3, p.4: "We allow cycles,
parallel and antiparallel edges, and zero costs or lengths."

`G.n` is the number of vertices (the vertices are `0, …, n − 1`) and `G.arcs` is the list of arcs,
each a tuple `(tail, head, cost, length)`. An arc is named by its position in the list, so parallel
arcs are distinct arcs.

**Formalization Note.** The accessors `tl`, `hd`, `cst`, `lng` read the arc with a given index and
return `0` for an index outside the list; every statement of the mission only uses arcs whose index
is in range (walks check it), and costs are summed over sets of arc indices. `WF` (well-formed) says
that every endpoint is a vertex and every cost and length is `≥ 0`; it is a hypothesis of the
guarantees, never built into the type, so a machine is defined on every input. -/
structure Net where
  /-- number of vertices -/
  n : ℕ
  /-- arcs `(tail, head, cost, length)`, indexed by position -/
  arcs : List (ℕ × ℕ × ℚ × ℚ)

/-- Tail of the arc with index `e`. -/
def Net.tl (G : Net) (e : ℕ) : ℕ := (G.arcs.getD e (0, 0, 0, 0)).1

/-- Head of the arc with index `e`. -/
def Net.hd (G : Net) (e : ℕ) : ℕ := (G.arcs.getD e (0, 0, 0, 0)).2.1

/-- Cost `c_e` of the arc with index `e`. -/
def Net.cst (G : Net) (e : ℕ) : ℚ := (G.arcs.getD e (0, 0, 0, 0)).2.2.1

/-- Length `ℓ_e` of the arc with index `e`. -/
def Net.lng (G : Net) (e : ℕ) : ℚ := (G.arcs.getD e (0, 0, 0, 0)).2.2.2

/-- Well-formed: endpoints are vertices, costs and lengths are nonnegative. -/
def Net.WF (G : Net) : Prop :=
  ∀ a ∈ G.arcs, a.1 < G.n ∧ a.2.1 < G.n ∧ 0 ≤ a.2.2.1 ∧ 0 ≤ a.2.2.2

/-- The set of all arc indices `{0, …, m − 1}`, i.e. the whole graph `E`. -/
def Net.allArcs (G : Net) : Finset ℕ := Finset.range G.arcs.length

end LCPlanarSteiner


