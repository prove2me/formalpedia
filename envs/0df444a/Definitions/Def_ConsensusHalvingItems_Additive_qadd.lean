-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_qadd
-- name    : ConsensusHalvingItems_Additive_qadd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:23:05.947693+00:00
-- url     : https://prove2.me/theorems/7be4dedb-c405-45e1-8ccb-dbfeb67aca16
-- title:
--   Ticked rational addition
-- statement:
--   The ticked addition of two rationals $a, b$ charges $\operatorname{opCost}(a, b)$ ticks and returns the exact rational $a + b$. Every rational addition performed by the algorithm of the mission goes through this operation.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_opCost

namespace ConsensusHalvingItems.Additive

/-- **Ticked rational sum.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

`qadd a b` charges `opCost a b` and returns the exact sum `a + b` in `ℚ`.

**Formalization Note.** Every rational sum computed by the algorithm of the mission goes
through this helper (bit model, Reading 1). -/
def qadd (a b : ℚ) : StateM ℕ ℚ := do
  tick (opCost a b)
  pure (a + b)

end ConsensusHalvingItems.Additive


