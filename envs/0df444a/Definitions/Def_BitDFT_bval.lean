-- Prove2me | Definitions.Def_BitDFT_bval
-- name    : BitDFT_bval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T01:36:50.175636+00:00
-- url     : https://prove2.me/theorems/f4c7de7c-b6ea-4dbc-8027-2800e75aa52f
-- title:
--   Value of a bit list read least significant first
-- statement:
--   The number represented by a finite list of bits when the first entry is the least significant one: $\operatorname{bval}[b_0,b_1,\dots,b_{m-1}] = \sum_i b_i 2^i$. This is the order in which a Turing machine that walks leftwards over a tape meets the bits of a stored integer, and it is the companion of the platform's `IntMul.val`, which reads a bit list most significant first. Together the two let a machine-level argument speak about blocks of an encoded integer instead of about tape cells.
-- source:
--   Internal: bit-list value used by the machine constructions for the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98).

import Mathlib
namespace BitDFT

/-- Value of a list of bits read least significant bit first: `bval [b0, b1, …] = Σ bᵢ 2ⁱ`. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * bval l

theorem bval_cons (b : Bool) (l : List Bool) : bval (b :: l) = b.toNat + 2 * bval l := rfl

theorem bval_nil : bval [] = 0 := rfl

end BitDFT


