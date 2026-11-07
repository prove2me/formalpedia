-- Prove2me | Definitions.Def_Max3CutHard_Gadget
-- name    : Max3CutHard_Gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:04.673415+00:00
-- url     : https://prove2.me/theorems/96d9842f-120d-4438-a6ab-a4a453710fc6
-- title:
--   A gadget $I$ with primaries, globals and auxiliary vertices
-- statement:
--   Fix $k$. A **gadget** $I$ is a weighted graph on three **primary** vertices $p_1,p_2,p_3$, $k$ **global** vertices $g_0,\dots,g_{k-1}$ and some number of **auxiliary** vertices.
--
--   Gadgets replace the equations of a 3Lin($\mathbb Z_3$) instance in the reduction to Max-$k$-Cut.
--
--   **Formalization Note** The primaries $p_1,p_2,p_3$ are indexed $0,1,2$. The source fixes $k\ge3$; the theorems that need it assume it.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Gadgets, p.4

import Mathlib
import Definitions.Def_Max3CutHard_RGraph

namespace Max3CutHard

/-- **A gadget.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Gadgets, p.4: "Fix `k ≥ 3`. A gadget `I` is a weighted graph on
three primary vertices `p1, p2, p3`, `k` global vertices `g0, …, g(k−1)` and some auxiliary
vertices."

**Formalization Note.** The vertex type is `Fin 3 ⊕ Fin k ⊕ Fin aux`: primaries `p1, p2, p3` are
`Sum.inl 0, 1, 2` (0-based), global `g_i` is `Sum.inr (Sum.inl i)`, auxiliary vertices are
`Sum.inr (Sum.inr a)`. The bound `k ≥ 3` is a hypothesis of the theorems that need it. -/
structure Gadget (k : ℕ) where
  /-- number of auxiliary vertices -/
  aux : ℕ
  /-- the weighted edges -/
  edges : RGraph (Fin 3 ⊕ Fin k ⊕ Fin aux)

end Max3CutHard


