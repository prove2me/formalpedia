-- Prove2me | Definitions.Def_PascalExtremes_Powers
-- name    : PascalExtremes_Powers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:55:06.606352+00:00
-- url     : https://prove2.me/theorems/bd40d271-7c92-46ce-9e64-b938a231abd9
-- title:
--   Powers
-- statement:
--   Definitions and structural lemmas for Powers, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremes
def rP (p m : ℕ) : ℕ :=
  Nat.log p m + 1
end PascalExtremes


