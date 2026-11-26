-- Prove2me | Definitions.Def_PascalExtremes_Kummer
-- name    : PascalExtremes_Kummer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:54:34.503881+00:00
-- url     : https://prove2.me/theorems/4c5ecf05-cbe4-4b68-a5a2-37cb7b2b9e19
-- title:
--   Kummer
-- statement:
--   Definitions and structural lemmas for Kummer, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Kummer.lean

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Digits
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremes
def CarryAt (p n k i : ℕ) : Prop :=
  p ^ i ≤ k % p ^ i + (n - k) % p ^ i
instance carryAtDecidable (p n k i : ℕ) : Decidable (CarryAt p n k i) := by
  unfold CarryAt
  infer_instance
def carryCount (p n k b : ℕ) : ℕ :=
  ((Finset.Ico 1 b).filter fun i ↦ CarryAt p n k i).card
end PascalExtremes


