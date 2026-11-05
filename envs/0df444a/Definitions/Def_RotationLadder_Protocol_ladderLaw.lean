-- Prove2me | Definitions.Def_RotationLadder_Protocol_ladderLaw
-- name    : RotationLadder_Protocol_ladderLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:57.391001+00:00
-- url     : https://prove2.me/theorems/594ebbaa-9d6b-4612-8b21-9af53d9731a9
-- title:
--   Law of the randomness of one ladder run
-- statement:
--   The sequence $u$ of a ladder run has independent coordinates, each uniform on $[0,1]$. This is the product of Lebesgue measures on $[0,1]^{\mathbb N}$, and it models independent measurements at the successive steps of Fig. 3.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3 and Fig. 3

import Mathlib
import Definitions.Def_RotationLadder_Protocol_LadderTape

namespace RotationLadder.Protocol

/-- **The law of the ladder's randomness.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, p. 3, Fig. 3: the measurements of the successive steps are independent.

`ladderLaw` is the product of Lebesgue measures on `[0, 1]`, one factor per step. -/
noncomputable def ladderLaw : MeasureTheory.Measure LadderTape :=
  MeasureTheory.Measure.infinitePi fun _ => MeasureTheory.volume

end RotationLadder.Protocol


