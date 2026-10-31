-- Prove2me | Definitions.Def_FASTournament_IsStrong
-- name    : FASTournament_IsStrong
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:51.118443+00:00
-- url     : https://prove2.me/theorems/8af81dec-cfb4-404d-ba76-eef304ed4f59
-- title:
--   Strong (strongly connected) digraph
-- statement:
--   A digraph $G$ is **strongly connected**, or **strong**, if each vertex is reachable from every other vertex by a directed path.
--
--   **Formalization Note** Reachability is the reflexive-transitive closure of the arc relation; a digraph with at most one vertex is strong.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5

import Mathlib

namespace FASTournament

/-- **Strong (strongly connected) digraph.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5: "is called strongly connected or strong if each vertex is reachable from every
other vertex."

**Formalization Note.** Reachability is the reflexive-transitive closure of the arc relation.
A digraph with at most one vertex is strong. -/
def IsStrong {V : Type*} (G : Digraph V) : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adj u v

end FASTournament


