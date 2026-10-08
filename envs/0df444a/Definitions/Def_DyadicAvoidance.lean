-- Prove2me | Definitions.Def_DyadicAvoidance
-- name    : DyadicAvoidance
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.701246+00:00
-- url     : https://prove2.me/theorems/d8a0d3b6-ce34-4021-abce-94c89cc97aa0
-- statement:
--   For each natural number n, dyadicPoint(n) is defined to be the real number (1/2)ⁿ = 2⁻ⁿ. The indexing starts at n = 0, giving the sequence 1, 1/2, 1/4, 1/8, and so on: each successive term is half the preceding term.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DyadicAvoidance.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DyadicAvoidance.lean; bytes 16..133
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace Problem310

def dyadicPoint (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n



end Problem310
end
end OAI


