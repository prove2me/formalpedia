-- Prove2me | Definitions.Def_PascalExtremes_TargetAAttainment
-- name    : PascalExtremes_TargetAAttainment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:58:12.96669+00:00
-- url     : https://prove2.me/theorems/1542de09-28da-54a8-b69e-9b114dcada9c
-- title:
--   Target AAttainment
-- statement:
--   Definitions and structural lemmas for Target AAttainment, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetAAttainment.lean

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremes
def extremalRows (p m : ℕ) : Set ℕ :=
  {N | AdmissibleRow m N ∧
    padicValNat p (G N m) = rP p m}
noncomputable def T (p m : ℕ) : ℕ :=
  sInf (extremalRows p m)
end PascalExtremes


