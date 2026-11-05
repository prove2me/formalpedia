-- Prove2me | Definitions.Def_RotationLadder_Protocol_coinLaw
-- name    : RotationLadder_Protocol_coinLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:37.702233+00:00
-- url     : https://prove2.me/theorems/dea1d244-df91-45e6-a2e2-90a2db40067e
-- title:
--   Law of the measured outcomes
-- statement:
--   The outcomes of a run are independent fair coins: this is the product of uniform measures on $\{0,1\}^{\mathbb N}$. Each use of Fig. 1 gives either outcome with probability $1/2$, whatever the input state.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2

import Mathlib
import Definitions.Def_RotationLadder_Protocol_Coins

namespace RotationLadder.Protocol

/-- **The law of the outcomes.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, p. 2: the two outcomes of Fig. 1 occur "each with probability 1/2".

`coinLaw` is the product of fair coins, one per step. -/
noncomputable def coinLaw : MeasureTheory.Measure Coins :=
  MeasureTheory.Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

end RotationLadder.Protocol


