-- Prove2me | Definitions.Def_FASTournament_Isomorphic
-- name    : FASTournament_Isomorphic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:36.100657+00:00
-- url     : https://prove2.me/theorems/d7bf2e0d-421a-452c-85a8-03cd124bbe53
-- title:
--   Isomorphic digraphs
-- statement:
--   Digraphs $G$ and $H$ are **isomorphic** if there is a bijection $\varphi$ between their vertex sets such that $ab$ is an arc of $G$ if and only if $\varphi(a)\varphi(b)$ is an arc of $H$. Statements such as "$T\notin\{F_1,G_1\}$" are read up to isomorphism.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.8 and p.12

import Mathlib

namespace FASTournament

/-- **Isomorphic digraphs.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.8 and p.12 ("T ∉ {F1, G1}", "other than F1 and G1", read up to isomorphism).

A bijection of the vertex sets that preserves and reflects arcs. -/
def Isomorphic {V W : Type*} (G : Digraph V) (H : Digraph W) : Prop :=
  ∃ e : V ≃ W, ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)

end FASTournament


