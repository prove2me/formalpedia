-- Prove2me | Definitions.Def_UniqueOptScores_IsYes
-- name    : UniqueOptScores_IsYes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:20.742122+00:00
-- url     : https://prove2.me/theorems/546e3721-bdfc-4e35-88a4-555742cc9d0f
-- title:
--   YES supports
-- statement:
--   A support $S$ is **YES** (for the occupancy parameter $r$) if $S \subseteq X \cup Y$, $S \in P_r$ and $F(S)$ holds. In Section 6 all supports called YES are understood to belong to $P_r$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22 ("All supports called YES below are understood to belong to P_r")

import Mathlib
import Definitions.Def_UniqueOptScores_Fpred
import Definitions.Def_UniqueOptScores_InPr

namespace UniqueOptScores

/-- **YES supports.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "All supports called YES below are understood to belong to P_r."

A support `S` is YES when `S ⊆ X ∪ Y`, `S ∈ P_r` and `F(S)` holds. -/
def IsYes {α : Type*} [DecidableEq α] (r : ℕ) (X Y S : Finset α) : Prop :=
  S ⊆ X ∪ Y ∧ InPr r X Y S ∧ Fpred X Y S

end UniqueOptScores


