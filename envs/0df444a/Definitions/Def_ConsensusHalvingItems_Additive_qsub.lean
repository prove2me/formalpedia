-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_qsub
-- name    : ConsensusHalvingItems_Additive_qsub
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:23:34.94338+00:00
-- url     : https://prove2.me/theorems/417e5b90-0379-4cb9-b9b6-f498c6f3a78e
-- title:
--   Ticked rational subtraction
-- statement:
--   The ticked subtraction of two rationals $a, b$ charges $\operatorname{opCost}(a, b)$ ticks and returns the exact rational $a - b$. Every rational subtraction performed by the algorithm of the mission goes through this operation.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_opCost

namespace ConsensusHalvingItems.Additive

/-- **Ticked rational difference.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

`qsub a b` charges `opCost a b` and returns the exact difference `a - b` in `ℚ`.

**Formalization Note.** Every rational difference computed by the algorithm of the mission goes
through this helper (bit model, Reading 1). -/
def qsub (a b : ℚ) : StateM ℕ ℚ := do
  tick (opCost a b)
  pure (a - b)

end ConsensusHalvingItems.Additive


