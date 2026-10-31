-- Prove2me | Definitions.Def_FASTournament_Arc
-- name    : FASTournament_Arc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:24.111151+00:00
-- url     : https://prove2.me/theorems/0d6eaadd-b8c7-4f26-b220-7306f3a3fd4b
-- title:
--   Arc set $A$ of a digraph
-- statement:
--   For a digraph $G=(V,A)$, the **arc set** $A$ consists of the ordered pairs $(u,v)$ of vertices such that $uv$ is an arc of $G$. Arc weights $w(e)$ and the variables $x(e)$ of the linear systems below are indexed by $A$.
--
--   **Formalization Note** `Arc G` is the subtype of pairs `(u, v)` with `G.Adj u v`.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2

import Mathlib

namespace FASTournament

/-- **The arc set `A` of a digraph `G = (V, A)`.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2.

An arc is an ordered pair `(u, v)` of vertices with `u → v` in `G`; weights `w(e)` and LP
variables `x(e)` are functions on this type.

**Formalization Note.** `Arc G` is the subtype `{p : V × V // G.Adj p.1 p.2}`. -/
abbrev Arc {V : Type*} (G : Digraph V) : Type _ := {p : V × V // G.Adj p.1 p.2}

end FASTournament


