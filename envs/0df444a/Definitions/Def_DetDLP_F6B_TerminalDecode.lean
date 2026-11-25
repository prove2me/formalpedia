-- Prove2me | Definitions.Def_DetDLP_F6B_TerminalDecode
-- name    : DetDLP_F6B_TerminalDecode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:42:33.403719+00:00
-- url     : https://prove2.me/theorems/a41694a6-f045-411c-b458-e5e6dfb4fc38
-- title:
--   Terminal BTN metadata decoder
-- statement:
--   Read the seven fields needed by the small contraction kernel from the nested terminal BTN encoding. The result preserves the descriptor verbatim and stores the six natural numbers in little-endian binary. The endpoint code includes a leading radix-one sentinel, so zero endpoint digits do not lose the edge-list length.
-- source:
--   Definitions/Def_DetDLP_TerminalBTN.lean, encodeTerminalBTNInstance; Solutions/M14A_small_kernel.lean, pairs and code.

import Definitions.Def_DetDLP_TerminalBTN
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_DetDLP_M13B_EndpointPoly

set_option autoImplicit false
namespace DetDLP.F6B
open OAI.Algorithms.SubexponentialSAT
open DetDLP_W1_Queries

/-- Read the zero-indexed field of a framed word list. -/
def fieldAt : ℕ → List Bool → List Bool
  | 0, x => first x
  | n+1, x => fieldAt n (more x)

/-- Return seven framed words: the unchanged descriptor and the little-endian
    bit strings for the edge count, vertex count, precision, arity, radix,
    and endpoint code (including its leading radix sentinel). -/
def decode (x : List Bool) : List Bool :=
  let g := fieldAt 1 x
  let v := Groundwork.PolyT.bval (fieldAt 0 g)
  let e := Groundwork.PolyT.bval (fieldAt 1 g)
  let p := Groundwork.PolyT.bval (fieldAt 6 x)
  let a := Groundwork.PolyT.bval (fieldAt 7 x)
  let r := v + 3
  let c := M13BEndpoint.pack r (w5_M6Sort.decode (fieldAt 3 g))
  Encoding.encodeList id [fieldAt 0 x,e.bits,v.bits,p.bits,a.bits,r.bits,c.bits]

end DetDLP.F6B


