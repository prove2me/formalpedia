-- Prove2me | Definitions.Def_PascalExtremes_Digits
-- name    : PascalExtremes_Digits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:53:27.422705+00:00
-- url     : https://prove2.me/theorems/a85ac40d-dbbb-567a-95fe-738574ebd5da
-- title:
--   Digits
-- statement:
--   Definitions and structural lemmas for Digits, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Digits.lean

module
public import Mathlib.Data.Nat.Digits.Lemmas
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremes
def digitAt (p N i : ℕ) : ℕ :=
  N / p ^ i % p
end PascalExtremes


