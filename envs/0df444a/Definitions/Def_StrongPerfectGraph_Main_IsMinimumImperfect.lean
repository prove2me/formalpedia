-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsMinimumImperfect
-- name    : StrongPerfectGraph_Main_IsMinimumImperfect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:37:45.843986+00:00
-- url     : https://prove2.me/theorems/87da9949-8470-4a96-8895-fddd64c7d791
-- title:
--   Minimum imperfect graph
-- statement:
--   A **minimum imperfect graph** is a counterexample to Theorem 1.2 with as few vertices as possible. Thus $G$ is Berge and not perfect, while every Berge graph $H$ with fewer vertices is perfect:
--
--   $$G\text{ is Berge},\quad G\text{ is not perfect},\quad |V(H)|<|V(G)|\ \text{and}\ H\text{ Berge}\Longrightarrow H\text{ perfect}.$$
--
--   The comparison ranges over all finite simple graphs of smaller order, rather than only induced subgraphs of $G$. This global minimum is used in the paper’s reduction from the decomposition theorem to the main theorem.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 52, §1, paragraph following 1.2

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

namespace StrongPerfectGraph.Main

/-- A smallest-vertex Berge graph that is not perfect. -/
def IsMinimumImperfect {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  IsBerge G ∧ ¬ IsPerfect G ∧
    ∀ n : ℕ, n < Fintype.card V →
      ∀ H : SimpleGraph (Fin n), IsBerge H → IsPerfect H

end StrongPerfectGraph.Main


