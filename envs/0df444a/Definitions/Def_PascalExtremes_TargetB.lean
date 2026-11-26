-- Prove2me | Definitions.Def_PascalExtremes_TargetB
-- name    : PascalExtremes_TargetB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:59:38.215798+00:00
-- url     : https://prove2.me/theorems/ba04adc3-0dc8-5472-83f1-2aee0283c032
-- title:
--   Target B
-- statement:
--   Definitions and structural lemmas for Target B, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremes
def q0 (p a : ℕ) : ℕ :=
  p ^ (2 * a) - p ^ a + 1
end PascalExtremes


