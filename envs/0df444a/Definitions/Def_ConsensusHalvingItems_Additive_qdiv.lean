-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_qdiv
-- name    : ConsensusHalvingItems_Additive_qdiv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:48.372835+00:00
-- url     : https://prove2.me/theorems/118642c0-f241-4287-b22a-c34f95aeb50e
-- title:
--   Ticked rational division
-- statement:
--   The ticked division of two rationals $a, b$ charges $\operatorname{opCost}(a, b)$ ticks and returns the exact rational $a / b$. Every rational division performed by the algorithm of the mission goes through this operation. The algorithm of the mission divides only by nonzero numbers.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_opCost

namespace ConsensusHalvingItems.Additive

/-- **Ticked rational quotient.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

`qdiv a b` charges `opCost a b` and returns the exact quotient `a / b` in `ℚ`.

**Formalization Note.** Every rational quotient computed by the algorithm of the mission goes
through this helper (bit model, Reading 1).
The algorithm of the mission only divides by nonzero numbers; `a / 0 = 0` in Lean is never
used. -/
def qdiv (a b : ℚ) : StateM ℕ ℚ := do
  tick (opCost a b)
  pure (a / b)

end ConsensusHalvingItems.Additive


