-- Prove2me | Definitions.Def_MomentComparison_Lens
-- name    : MomentComparison_Lens
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:10:47.981235+00:00
-- url     : https://prove2.me/theorems/1110b176-82d8-4b08-932c-390221cb4aa7
-- title:
--   Lens
-- statement:
--   Definitions and structural lemmas for Lens, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Lens.lean

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace MomentComparison
@[expose] def inLens (p : ℝ) (w : ℂ) : Prop :=
  ‖w - (((p - 2) / (2 * (p - 1)) : ℝ) : ℂ)‖ ≤ p / (2 * (p - 1)) ∧
  ‖w + (((p - 2) / (2 * (p - 1)) : ℝ) : ℂ)‖ ≤ p / (2 * (p - 1))
end MomentComparison


