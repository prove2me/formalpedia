-- Prove2me | Definitions.Def_BitDFT_PackedScale
-- name    : BitDFT_PackedScale
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T21:54:37.650553+00:00
-- url     : https://prove2.me/theorems/1678e9bb-d494-4d56-aa15-75ccb9083aec
-- title:
--   Little-endian packing for exact block scaling
-- statement:
--   For a base B, pack a finite list of nonnegative coefficients as a little-endian positional numeral. This representation supports exact coefficientwise multiplication by a common natural factor whenever the scaled coefficients remain below B.
-- source:
--   Arithmetic representation used by the output rescaling machine. Coefficients are grouped into blocks whose total encoded width does not exceed nq, so arbitrary nonmonotone multiplier bounds are applied only at size nq.

import Definitions.Def_IntMul_MultitapeModel

set_option autoImplicit false
namespace BitDFT.PackedScale

/-- Little-endian base-B packing of a list of nonnegative coefficients. -/
def packBase (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: xs => a + B * packBase B xs

end BitDFT.PackedScale


