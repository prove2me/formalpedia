-- Prove2me | Definitions.Def_ContPatrol_Multigraph_IsDoubleTour
-- name    : ContPatrol_Multigraph_IsDoubleTour
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:41.285478+00:00
-- url     : https://prove2.me/theorems/134b04ad-4139-43c9-bdb5-904f12415223
-- title:
--   The double tours $S_2$ of Theorem 3
-- statement:
--   A **double tour** $S_2$ is a closed dart walk such that
--
--   1. every edge is traversed exactly twice, and
--   2. no edge is traversed consecutively in opposite directions, except at a leaf node: whenever a dart is immediately followed (cyclically) by its own reverse, the vertex between them has degree $1$.
--
--   Theorem 3 asserts that every network has such a tour; the Patroller's optimal strategy in Theorem 6 is built from it.
--
--   **Formalization Note** Vertices of degree $2$ are regular points of $Q$, so no reversal is allowed there. A loop may be repeated consecutively in the same direction (the paper's "For loops, an arc may be repeated consecutively").
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Theorem 3, p.11

import Mathlib
import Definitions.Def_ContPatrol_Multigraph

namespace ContPatrol

namespace Multigraph

variable {V E : Type}

/-- **The double tours S₂ of Theorem 3.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Theorem 3,
p.11: "a tour S2 which covers every arc twice and for which no arc is traversed consecutively in
opposite directions, except for leaf arcs."

`G.IsDoubleTour w`: `w` is a closed dart walk in which
1. every edge occurs in exactly two positions, and
2. (cyclically, including the wrap-around) a dart is followed by its own reverse only when the
   vertex in between has degree 1.

**Formalization Note.** A reversal "on a leaf arc" is a turn-around at its leaf node, the only
place where the walk can reverse inside a leaf arc. Vertices of degree 2 are regular points, so no
reversal is allowed there. For a loop, the reverse dart is the same loop traversed in the other
direction; repeating a loop in the same direction is allowed (p.12: "For loops, an arc may be
repeated consecutively"). Covering every edge twice covers every arc of Q twice. -/
def IsDoubleTour [Fintype E] [DecidableEq V] [DecidableEq E] (G : Multigraph V E)
    (w : List (E × Bool)) : Prop :=
  G.IsClosedDartWalk w ∧ (∀ e : E, w.countP (fun d => d.1 = e) = 2) ∧
    ∀ (i : ℕ) (hi : i < w.length),
      w[(i + 1) % w.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) = rev w[i] →
        G.deg (G.head w[i]) = 1

end Multigraph

end ContPatrol


