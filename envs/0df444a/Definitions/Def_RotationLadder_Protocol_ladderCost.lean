-- Prove2me | Definitions.Def_RotationLadder_Protocol_ladderCost
-- name    : RotationLadder_Protocol_ladderCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:32.97043+00:00
-- url     : https://prove2.me/theorems/eb950abf-35da-4e1b-a9aa-67eef1c1135d
-- title:
--   Copies of $|H\rangle$ used to reach a level
-- statement:
--   For a level $i\ge0$, the cost of a ladder run is the first time the walk is at level $i$:
--
--   $$\min\{t: L_t=i\},$$
--
--   with value $\infty$ if the walk never reaches $i$. Since each step of the walk consumes one copy of $|H\rangle$, this is the number of copies consumed to produce $|H_i\rangle$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3 and Fig. 3

import Mathlib
import Definitions.Def_RotationLadder_Protocol_ladderLevel

namespace RotationLadder.Protocol

/-- **The cost of one ladder run.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, p. 3 and Fig. 3: the number of copies of `|H⟩` consumed until `|H_i⟩` is held.

`ladderCost i u` is the least `t` with `ladderLevel u t = i`, and `⊤` if the walk never gets there.
-/
noncomputable def ladderCost (i : ℕ) (u : LadderTape) : ℕ∞ :=
  sInf ((fun t : ℕ => (t : ℕ∞)) '' {t : ℕ | ladderLevel u t = i})

end RotationLadder.Protocol


