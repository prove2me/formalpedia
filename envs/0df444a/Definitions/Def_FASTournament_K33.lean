-- Prove2me | Definitions.Def_FASTournament_K33
-- name    : FASTournament_K33
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:24.469152+00:00
-- url     : https://prove2.me/theorems/9e26dad6-ab12-4194-a1b6-23e3ff9f0f00
-- title:
--   Möbius ladder $K_{3,3}$
-- statement:
--   The Möbius ladder $K_{3,3}$ of Figure 1 is the digraph on the vertices $u_1,\dots,u_6$ with arcs
--   $u_1u_2,\ u_2u_3,\ u_3u_4,\ u_4u_1,\ u_4u_5,\ u_5u_6,\ u_6u_3,\ u_6u_1,\ u_2u_5$ (9 arcs).
--
--   It is one of the four forbidden structures in the definition of Möbius-free tournaments.
--
--   **Formalization Note** Vertex $u_i$ is the element $i-1$ of `Fin`; the arc list is written with the 1-based labels of the figure.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 1, p.3

import Mathlib

namespace FASTournament

/-- **The Möbius ladder K₃,₃** (Figure 1, p.3).
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 1 ("Forbidden Structures"), p.3.

Vertices `u1, …, u6`; arcs u1u2, u2u3, u3u4, u4u1, u4u5, u5u6, u6u3, u6u1, u2u5.

**Formalization Note.** Vertex `uᵢ` is `Fin` index `i - 1`; the arc list is written with the
1-based labels of the figure. -/
def K33 : Digraph (Fin 6) where
  Adj a b := (a.val + 1, b.val + 1) ∈ ([(1, 2), (2, 3), (3, 4), (4, 1), (4, 5), (5, 6), (6, 3), (6, 1), (2, 5)] : List (ℕ × ℕ))

end FASTournament


