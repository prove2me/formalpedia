-- Prove2me | Definitions.Def_FASTournament_M5
-- name    : FASTournament_M5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:23.575079+00:00
-- url     : https://prove2.me/theorems/70550ce9-bd8c-4483-9bd4-4f6064c196d9
-- title:
--   Möbius ladder $M_5$
-- statement:
--   The Möbius ladder $M_5$ of Figure 1 is the digraph on the vertices $u_1,\dots,u_6$ with arcs
--   $u_1u_2,\ u_2u_3,\ u_3u_1,\ u_3u_4,\ u_4u_2,\ u_4u_5,\ u_5u_3,\ u_3u_6,\ u_6u_5,\ u_2u_6,\ u_5u_1$ (11 arcs).
--
--   It is one of the four forbidden structures in the definition of Möbius-free tournaments.
--
--   **Formalization Note** Vertex $u_i$ is the element $i-1$ of `Fin`; the arc list is written with the 1-based labels of the figure.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 1, p.3

import Mathlib

namespace FASTournament

/-- **The Möbius ladder M₅** (Figure 1, p.3).
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 1 ("Forbidden Structures"), p.3.

Vertices `u1, …, u6`; arcs u1u2, u2u3, u3u1, u3u4, u4u2, u4u5, u5u3, u3u6, u6u5, u2u6, u5u1.

**Formalization Note.** Vertex `uᵢ` is `Fin` index `i - 1`; the arc list is written with the
1-based labels of the figure. -/
def M5 : Digraph (Fin 6) where
  Adj a b := (a.val + 1, b.val + 1) ∈ ([(1, 2), (2, 3), (3, 1), (3, 4), (4, 2), (4, 5), (5, 3), (3, 6), (6, 5), (2, 6), (5, 1)] : List (ℕ × ℕ))

end FASTournament


