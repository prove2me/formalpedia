-- Prove2me | Definitions.Def_CountingMatroidBridgeRationalPairSums
-- name    : CountingMatroidBridgeRationalPairSums
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T22:00:37.214915+00:00
-- url     : https://prove2.me/theorems/501c7eed-94d4-4e32-a51a-6d9a86a6fdde
-- title:
--   Finite sums of unreduced rational pairs
-- statement:
--   A finite list of nonnegative rationals is summed using unreduced natural numerator and positive-denominator pairs. The representation records the total binary width of the two components and the exact cross-product sum operation.
-- source:
--   Lean 4.33.1 continuation of the accepted nonnegative rational-pair arithmetic bridge.

import Definitions.Def_CountingMatroidBridgeNonnegativeRationalPair

set_option autoImplicit false

namespace CountingMatroid.Bridge.RationalPair

/-- Total numerator/denominator bit width of an unreduced rational pair. -/
def pairSize (x : Pair) : ℕ := Nat.size x.1 + Nat.size x.2

/-- Exact left-associated addition of a finite list of rational pairs. -/
def sumPairs : List Pair → Pair
  | [] => (0, 1)
  | x :: xs => add x (sumPairs xs)

end CountingMatroid.Bridge.RationalPair


