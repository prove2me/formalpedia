-- Prove2me | Definitions.Def_RotationLadder_Protocol_ladderMeanCost
-- name    : RotationLadder_Protocol_ladderMeanCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:38.504079+00:00
-- url     : https://prove2.me/theorems/3d75e65d-6cf0-4553-aa59-a77f4ad87832
-- title:
--   Mean ladder cost of a level
-- statement:
--   The mean ladder cost of a level $i$ is the expected number of copies of $|H\rangle$ consumed to produce $|H_i\rangle$, as an element of $[0,\infty]$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 4

import Mathlib
import Definitions.Def_RotationLadder_Protocol_ladderLaw
import Definitions.Def_RotationLadder_Protocol_ladderCost
open scoped ENNReal

namespace RotationLadder.Protocol

/-- **The mean ladder cost of a level.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, p. 4: the offline cost is "the sum of the `|H⟩` states used for each ladder process".

`ladderMeanCost i` is the expected number of copies of `|H⟩` consumed to obtain `|H_i⟩`.

**Formalization Note.** Valued in `ℝ≥0∞`, so a run that never arrives makes the value `⊤`. -/
noncomputable def ladderMeanCost (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ u, ((ladderCost i u : ℕ∞) : ℝ≥0∞) ∂ladderLaw

end RotationLadder.Protocol


