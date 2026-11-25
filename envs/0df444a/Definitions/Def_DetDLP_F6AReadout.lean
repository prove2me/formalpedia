-- Prove2me | Definitions.Def_DetDLP_F6AReadout
-- name    : DetDLP_F6AReadout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T03:06:18.404437+00:00
-- url     : https://prove2.me/theorems/3acece50-3704-410d-9700-1ab2586cc6c2
-- title:
--   Packed digit readout with a unary output length
-- statement:
--   For each position below the length of the fourth word, extract the corresponding radix digit of the packed integer, reduce it modulo the given modulus, and encode the list in increasing index order. The first three words encode the integer, radix and modulus in binary.
-- source:
--   Solutions/M14A_small_kernel.lean, packed coefficient output of theorem solution.

import Mathlib
import Definitions.Def_DetDLP_Machine
import Definitions.Def_ToTuring_Lib_Nat1

namespace DetDLP.F6AReadout
open Groundwork.PolyT OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev Input := List Bool × List Bool × List Bool × List Bool

/-- The fourth word gives the digit count in unary; its bit values are ignored. -/
def readout (x : Input) : List Bool :=
  encodeNatListBin ((List.range x.2.2.2.length).map fun i =>
    bval x.1 / (bval x.2.1)^i % bval x.2.1 % bval x.2.2.1)

end DetDLP.F6AReadout


