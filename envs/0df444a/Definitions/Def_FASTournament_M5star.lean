-- Prove2me | Definitions.Def_FASTournament_M5star
-- name    : FASTournament_M5star
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:32.017556+00:00
-- url     : https://prove2.me/theorems/46048bd3-b562-4314-bd8e-0d59f11e6bc3
-- title:
--   Möbius ladder $M_5^*$
-- statement:
--   The Möbius ladder $M_5^*$ of Figure 1 is the digraph on the vertices $u_1,\dots,u_6$ with arcs
--   $u_2u_1,\ u_3u_2,\ u_1u_3,\ u_4u_3,\ u_2u_4,\ u_5u_4,\ u_3u_5,\ u_6u_3,\ u_5u_6,\ u_6u_2,\ u_1u_5$ (11 arcs).
--
--   It is $M_5$ with every arc reversed.
--
--   It is one of the four forbidden structures in the definition of Möbius-free tournaments.
--
--   **Formalization Note** Vertex $u_i$ is the element $i-1$ of `Fin`; the arc list is written with the 1-based labels of the figure.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 1, p.3

import Mathlib

namespace FASTournament

/-- **The Möbius ladder M₅*** (Figure 1, p.3).
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 1 ("Forbidden Structures"), p.3.

Vertices `u1, …, u6`; arcs u2u1, u3u2, u1u3, u4u3, u2u4, u5u4, u3u5, u6u3, u5u6, u6u2, u1u5.
(Every arc of `M₅` reversed, as drawn.)

**Formalization Note.** Vertex `uᵢ` is `Fin` index `i - 1`; the arc list is written with the
1-based labels of the figure. -/
def M5star : Digraph (Fin 6) where
  Adj a b := (a.val + 1, b.val + 1) ∈ ([(2, 1), (3, 2), (1, 3), (4, 3), (2, 4), (5, 4), (3, 5), (6, 3), (5, 6), (6, 2), (1, 5)] : List (ℕ × ℕ))

end FASTournament


