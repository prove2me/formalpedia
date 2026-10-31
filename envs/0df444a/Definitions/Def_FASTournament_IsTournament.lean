-- Prove2me | Definitions.Def_FASTournament_IsTournament
-- name    : FASTournament_IsTournament
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:20.249995+00:00
-- url     : https://prove2.me/theorems/f32ed58a-0972-4e28-ac1d-3f2610a88f92
-- title:
--   Tournament
-- statement:
--   A digraph $G=(V,A)$ is a **tournament** if there is precisely one arc between any two vertices: $G$ has no loops, and for any two distinct vertices $u,v$ exactly one of the arcs $uv$, $vu$ belongs to $A$.
--
--   Tournaments are the class of digraphs the whole paper characterizes.
--
--   **Formalization Note** Digraphs are Mathlib's `Digraph V`, which permits loops and pairs of opposite arcs; the predicate excludes both.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2

import Mathlib

namespace FASTournament

/-- **Tournament.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2: "A digraph G is called a tournament if there is precisely one arc between any two
vertices in G."

A digraph is a tournament if it has no loops and, for any two distinct vertices `u, v`, exactly
one of the arcs `u → v`, `v → u` is present.

**Formalization Note.** Digraphs are Mathlib's `Digraph V`, which allows loops and arcs in both
directions; both are excluded here. -/
def IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ ∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)

end FASTournament


