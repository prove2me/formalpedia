-- Prove2me | Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
-- name    : HodgeComputerCycleQ2NumeratorCharacter
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-24T00:20:02.595019+00:00
-- url     : https://prove2.me/theorems/b14981ee-aaf9-4a05-8018-07130d8ed3eb
-- title:
--   Numerator characters for a character-$0$ denominator
-- statement:
--   When the denominator $S$ has sixth-root character $0$, each numerator component $W_j$ that contributes to the chart divergence in character $1$ must itself lie in a definite character class. Differentiation by the variable of index $j+1$ lowers weight by $\mathrm{sixthRootWeight}(j+1)$, and matching the character-$1$ inhomogeneous term forces
--
--   $$\mathrm{numeratorCharacter}(j) = 5 + \mathrm{sixthRootWeight}(j+1)\pmod{6}.$$
--
--   Explicitly the five characters are $(0,5,2,1,0)$.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_character_zero_linear_system, https://prove2.me/theorems/75f1477a-2df3-4a0d-bd43-85d9e80c9fd2. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerCycleQ2Character

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2

/-- Target character of `W j` when the denominator has character `0`:
`5 + sixthRootWeight (j.succ)`. -/
def HodgeComputer.CycleQ2.numeratorCharacter (j : Fin 5) : ZMod 6 :=
  5 + sixthRootWeight j.succ


