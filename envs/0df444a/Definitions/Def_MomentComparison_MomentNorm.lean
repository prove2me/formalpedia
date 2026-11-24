-- Prove2me | Definitions.Def_MomentComparison_MomentNorm
-- name    : MomentComparison_MomentNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:11:11.484853+00:00
-- url     : https://prove2.me/theorems/062d0735-6400-466c-8082-622c2971a153
-- title:
--   Moment Norm
-- statement:
--   Definitions and structural lemmas for Moment Norm, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/MomentNorm.lean

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped BigOperators
namespace MomentComparison
@[expose] noncomputable def complexMomentNorm {n : ℕ} (p : ℝ) (f : Cube n → ℂ) : ℝ :=
  (cubeAverage fun x => ‖f x‖ ^ p) ^ p⁻¹
end MomentComparison


