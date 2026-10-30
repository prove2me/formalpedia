-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_opCost
-- name    : ConsensusHalvingItems_Additive_opCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:22:29.477598+00:00
-- url     : https://prove2.me/theorems/8f20df7b-916c-4fb4-adc2-ad4cd2a6cc35
-- title:
--   Cost of one arithmetic operation on rationals
-- statement:
--   The cost charged for one arithmetic operation or comparison on rationals $a, b$ is
--
--   $$
--   \operatorname{opCost}(a, b) = \bigl(\operatorname{bitSize}(a) + \operatorname{bitSize}(b) + 1\bigr)^2 .
--   $$
--
--   Up to a constant factor this bounds the bit complexity of schoolbook addition, subtraction, multiplication and division (including reduction of the result to lowest terms) and of comparison. Because the cost grows with the sizes of the numbers, a computation whose numbers grow exponentially is charged exponentially.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_bitSize

namespace ConsensusHalvingItems.Additive

/-- **Cost of one arithmetic operation on two rationals.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

`opCost a b = (bitSize a + bitSize b + 1)²`. Up to a constant factor this bounds the bit
complexity of schoolbook addition, subtraction, multiplication and division of `a` and `b`,
including the gcd reduction of the result, and of comparing them.

**Formalization Note.** Reading 1 of the mission (bit model): the cost of an operation grows with
the size of the numbers, so a run whose numbers grow exponentially is charged exponentially. -/
def opCost (a b : ℚ) : ℕ := (bitSize a + bitSize b + 1) ^ 2

end ConsensusHalvingItems.Additive


