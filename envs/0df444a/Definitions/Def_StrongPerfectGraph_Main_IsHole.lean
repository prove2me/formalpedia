-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsHole
-- name    : StrongPerfectGraph_Main_IsHole
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:05:26.034899+00:00
-- url     : https://prove2.me/theorems/6ee8835d-3c4b-4795-8a36-5ea7ed4800e7
-- title:
--   Hole (induced cycle)
-- statement:
--   Let $G$ be a finite simple graph. A **hole** is an induced cycle with at least four vertices. Its vertices are listed in cyclic order as $c=(v_0,\ldots,v_{k-1})$, without repetition, with $k\ge4$ and
--
--   $$v_i v_j\in E(G)\quad\Longleftrightarrow\quad j\equiv i+1\pmod k\ \text{or}\ i\equiv j+1\pmod k.$$
--
--   Its length is $k$. A hole of $\overline G$ represents an antihole of $G$. The adjacency equivalence excludes chords, which is essential to the definition of a Berge graph.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 51, §1, definition of a hole

import Mathlib

namespace StrongPerfectGraph.Main

/-- An induced cycle of length at least four, listed cyclically. -/
def IsHole {V : Type*} (G : SimpleGraph V) (c : List V) : Prop :=
  4 ≤ c.length ∧ c.Nodup ∧
    ∀ i j : Fin c.length,
      G.Adj (c.get i) (c.get j) ↔
        ((i.val + 1) % c.length = j.val ∨ (j.val + 1) % c.length = i.val)

end StrongPerfectGraph.Main


