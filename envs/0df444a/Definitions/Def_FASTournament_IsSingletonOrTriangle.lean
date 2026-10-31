-- Prove2me | Definitions.Def_FASTournament_IsSingletonOrTriangle
-- name    : FASTournament_IsSingletonOrTriangle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:52.886428+00:00
-- url     : https://prove2.me/theorems/bdf75b1f-c722-466c-bee5-b4b956b4f4af
-- title:
--   Singleton or triangle
-- statement:
--   A vertex set $U$ of a digraph $G$ induces **a singleton or a triangle** if $U$ consists of a single vertex, or $U=\{a,b,c\}$ with three distinct vertices and arcs $ab$, $bc$, $ca$ (a directed cycle of length three).
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5 and p.8

import Mathlib

namespace FASTournament

/-- **`G[U]` is a singleton or a triangle.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.8 ("G[Ui] is either a singleton or a triangle") and p.5 ("a triangle (a directed cycle
of length three)").

`U` is a single vertex, or `U = {a, b, c}` with three distinct vertices and arcs
`a → b → c → a`. -/
def IsSingletonOrTriangle {V : Type*} (G : Digraph V) (U : Set V) : Prop :=
  (∃ a, U = {a}) ∨
    ∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ U = {a, b, c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

end FASTournament


