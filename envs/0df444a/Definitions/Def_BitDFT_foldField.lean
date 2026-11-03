-- Prove2me | Definitions.Def_BitDFT_foldField
-- name    : BitDFT_foldField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T04:34:11.854185+00:00
-- url     : https://prove2.me/theorems/2c91830b-4395-41b7-a1bb-b92bd746458d
-- title:
--   The digit fold of the unpacking machine
-- statement:
--   The unpacking machine computes one balanced base-$2^\beta$ digit at a time. It walks the $\beta$ input bits of a field from the least significant end, keeping two bits in its state.
--
--   The first is the *two's-complement carry* for the sign of $W$: while it is set, each scanned bit of the stored magnitude is flipped, and it clears at the first stored $1$. The second is the carry of the addition that folds the incoming digit carry into the field's value.
--
--   `foldStep` is the rule for one scanned bit, returning the two carries after it and the sum bit it contributes; `foldField` is the iteration of that rule over a whole field, returning the pushed bits least significant first, the two's-complement carry after the field, the carry out of the digit, and the field's top bit — which is the digit's sign in the balanced representation. `addBits` is the same iteration with the two's-complement carry switched off, that is, plain carry-propagating addition of one bit.
--
--   The content is the bit-level interface between the machine and the arithmetic: the main theorem about it says that the pushed bits are the bits of the field's value plus the incoming carry, so the field's digit is obtained from its value by a single carry-propagating addition, and the carry out is what the next field has to absorb.
-- source:
--   Internal: the digit loop of the machine component of the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98); balanced digit extraction as in Harvey--van der Hoeven, arXiv:2503.22848, Section 2.

import Mathlib
import Definitions.Def_BitDFT_bval

set_option autoImplicit false
noncomputable section
namespace BitDFT

/-!
# The digit fold of the unpacking machine

The unpacking machine computes one balanced base-`2^β` digit at a time by walking a field of `β`
input bits from its least significant end, carrying two bits in its state.  `foldStep` is that
one-bit rule and `foldField` is its iteration over a whole field: the pushed bits (least
significant first), the two's-complement carry after the field, the carry out of the digit, and the
field's top bit, which is the digit's sign in the balanced representation.
-/

/-- One digit step: given the two's-complement carry `g`, the digit carry `κ` and the scanned bit
`b`, the folded bit `x = b ≠ g`, the new two's-complement carry `g ∧ ¬b`, the folded bit `x ≠ κ`
and the new digit carry `x ∧ κ`. -/
def foldStep (g κ b : Bool) : Bool × Bool × Bool :=
  let x := b != g
  (g && !b, x != κ, x && κ)

/-- Fold a whole field, least significant bit first. -/
def foldField (g κ : Bool) (l : List Bool) : List Bool × Bool × Bool × Bool :=
  match l with
  | [] => ([], g, κ, κ)
  | b :: t =>
    let s := foldStep g κ b
    let r := foldField s.1 s.2.2 t
    (s.2.1 :: r.1, r.2.1, r.2.2.1, if t = [] then s.2.1 else r.2.2.2)

/-- Carry-propagating addition of one bit to a bit list, least significant first: the bits of the
sum and the carry out.  This is `foldField` with the two's-complement carry switched off. -/
def addBits : Bool → List Bool → List Bool × Bool
  | κ, [] => ([], κ)
  | κ, b :: t =>
    let r := addBits (b && κ) t
    ((b != κ) :: r.1, r.2)

end BitDFT


