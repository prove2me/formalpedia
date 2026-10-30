-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_qmul
-- name    : ConsensusHalvingItems_Additive_qmul
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:14.220277+00:00
-- url     : https://prove2.me/theorems/7b5bf47b-c4c0-40e9-ad86-3377a7829ba8
-- title:
--   Ticked rational multiplication
-- statement:
--   The ticked multiplication of two rationals $a, b$ charges $\operatorname{opCost}(a, b)$ ticks and returns the exact rational $a \cdot b$. Every rational multiplication performed by the algorithm of the mission goes through this operation.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_opCost

namespace ConsensusHalvingItems.Additive

/-- **Ticked rational product.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

`qmul a b` charges `opCost a b` and returns the exact product `a * b` in `ℚ`.

**Formalization Note.** Every rational product computed by the algorithm of the mission goes
through this helper (bit model, Reading 1). -/
def qmul (a b : ℚ) : StateM ℕ ℚ := do
  tick (opCost a b)
  pure (a * b)

end ConsensusHalvingItems.Additive


