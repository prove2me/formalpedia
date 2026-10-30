-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_qlt
-- name    : ConsensusHalvingItems_Additive_qlt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:25:27.033014+00:00
-- url     : https://prove2.me/theorems/8c840b2d-23e6-4c69-94f5-03485ee256a1
-- title:
--   Ticked rational comparison
-- statement:
--   The ticked comparison of two rationals $a, b$ charges $\operatorname{opCost}(a, b)$ ticks and returns the truth value of $a < b$. Every test of this kind on rational data made by the algorithm of the mission goes through this operation.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_opCost

namespace ConsensusHalvingItems.Additive

/-- **Ticked rational comparison \`a < b\`.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

`qlt a b` charges `opCost a b` and returns the truth value of `a < b` as a `Bool`.

**Formalization Note.** Every test on rational data made by the algorithm of the mission goes
through this helper (bit model, Reading 1). -/
def qlt (a b : ℚ) : StateM ℕ Bool := do
  tick (opCost a b)
  pure (decide (a < b))

end ConsensusHalvingItems.Additive


