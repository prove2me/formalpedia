-- Prove2me | Definitions.Def_PascalMinusOne_Kummer
-- name    : PascalMinusOne_Kummer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:17:04.511604+00:00
-- url     : https://prove2.me/theorems/06f694f4-7f4e-54c0-8c35-7b3409ce8fb5
-- title:
--   Kummer
-- statement:
--   Definitions and structural lemmas for Kummer, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Kummer.lean

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit true
namespace PascalMinusOne
def CarryAt (p n k i : ℕ) : Prop :=
  p ^ i ≤ k % p ^ i + (n - k) % p ^ i
instance carryAtDecidable (p n k i : ℕ) : Decidable (CarryAt p n k i) := by
  unfold CarryAt
  infer_instance
def carryCount (p n k b : ℕ) : ℕ :=
  ((Finset.Ico 1 b).filter fun i ↦ CarryAt p n k i).card
def DigitwiseLE (p k n : ℕ) : Prop :=
  ∀ i, digitAt p k i ≤ digitAt p n i
end PascalMinusOne


