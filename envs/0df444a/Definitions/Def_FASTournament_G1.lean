-- Prove2me | Definitions.Def_FASTournament_G1
-- name    : FASTournament_G1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:25.286886+00:00
-- url     : https://prove2.me/theorems/9302dba4-4105-4621-82d5-1a08a73781b9
-- title:
--   The tournament $G_1$
-- statement:
--   $G_1$ is the tournament on the vertex set $V_1=\{1,2,3,4,5,6\}$ with arc set
--   $$
--   E_1=\{12,23,34,45,51,13,35,52,24,41,16,26,63,64,65\},
--   $$
--   whose members are denoted $a,b,c,\dots,o$ in this order (so $a=12$, $b=23$, $c=34$, …). It is one of the two exceptional Möbius-free strong tournaments that are not in the class $\mathcal P$, and Lemma 4.1 shows by a computer-assisted proof that it is FAS Mengerian.
--
--   **Formalization Note** Vertex $i$ is the element $i-1$ of `Fin 6`.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 5; proof of Lemma 4.1, p.24

import Mathlib

namespace FASTournament

/-- **The tournament `G₁`** (Figure 5; arc list on p.24).
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Lemma 4.1, p.24: "the vertex set of G1 is V1 = {1, 2, 3, 4, 5, 6} and arc set is
E1 = {12, 23, 34, 45, 51, 13, 35, 52, 24, 41, 16, 26, 63, 64, 65}".

**Formalization Note.** Vertex `i` is `Fin` index `i - 1`; the arc list is written with the
1-based labels of p.24, in the order of `E1` (the letters `a, …, o` of Claim 1). -/
def G1 : Digraph (Fin 6) where
  Adj a b := (a.val + 1, b.val + 1) ∈
    ([(1, 2), (2, 3), (3, 4), (4, 5), (5, 1), (1, 3), (3, 5), (5, 2), (2, 4), (4, 1), (1, 6),
      (2, 6), (6, 3), (6, 4), (6, 5)] : List (ℕ × ℕ))

end FASTournament


