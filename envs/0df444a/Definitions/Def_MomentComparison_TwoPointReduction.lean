-- Prove2me | Definitions.Def_MomentComparison_TwoPointReduction
-- name    : MomentComparison_TwoPointReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:14:38.746563+00:00
-- url     : https://prove2.me/theorems/4a137bb9-c11b-4aaa-8301-fe3c471eeefa
-- title:
--   Two Point Reduction
-- statement:
--   Definitions and structural lemmas for Two Point Reduction, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPointReduction.lean

module
public import Definitions.Def_MomentComparison_TwoPoint
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace MomentComparison
noncomputable def twoPointMoment (s : ℝ) (a b : ℂ) : ℝ :=
  (‖a + b‖ ^ s + ‖a - b‖ ^ s) / 2
end MomentComparison


