-- Prove2me | Definitions.Def_PascalExtremes_Examples
-- name    : PascalExtremes_Examples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:09:37.392236+00:00
-- url     : https://prove2.me/theorems/1ada1f2d-eae0-4b50-8a1a-b54ff1734f2b
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Examples.lean

module
public import Definitions.Def_PascalExtremes_TargetBMinimality
public import Mathlib.Tactic
public import Theorems.Thm_PascalExtremes_targetB

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremes
example : rP 2 5 = 3 := by
  norm_num [rP]
example : q0 2 2 = 13 := by
  norm_num [q0]
example : T 2 5 = 65 := by
  have h := targetB (p := 2) (a := 2) Nat.prime_two (by omega)
  norm_num at h ⊢
  exact h
end PascalExtremes


