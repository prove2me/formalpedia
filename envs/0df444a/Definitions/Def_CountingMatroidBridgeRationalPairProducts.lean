-- Prove2me | Definitions.Def_CountingMatroidBridgeRationalPairProducts
-- name    : CountingMatroidBridgeRationalPairProducts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T22:08:31.656412+00:00
-- url     : https://prove2.me/theorems/77256b72-1808-4e61-b376-4052d5c048a1
-- title:
--   Finite products of unreduced rational pairs
-- statement:
--   Finite lists of nonnegative rationals can be multiplied using unreduced natural numerator and positive-denominator pairs. The product operation is componentwise multiplication of these pairs.
-- source:
--   Lean 4.33.1 continuation of the accepted rational-pair arithmetic bridge.

import Definitions.Def_CountingMatroidBridgeRationalPairSums

set_option autoImplicit false

namespace CountingMatroid.Bridge.RationalPair

/-- Exact left-associated multiplication of a finite list of rational pairs. -/
def productPairs : List Pair → Pair
  | [] => (1, 1)
  | x :: xs => mul x (productPairs xs)

end CountingMatroid.Bridge.RationalPair


