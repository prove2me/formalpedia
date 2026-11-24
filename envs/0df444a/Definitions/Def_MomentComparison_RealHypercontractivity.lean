-- Prove2me | Definitions.Def_MomentComparison_RealHypercontractivity
-- name    : MomentComparison_RealHypercontractivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:14:25.155462+00:00
-- url     : https://prove2.me/theorems/26cf1014-cb5f-422f-9424-9816b872000b
-- title:
--   Real Hypercontractivity
-- statement:
--   Definitions and structural lemmas for Real Hypercontractivity, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/RealHypercontractivity.lean

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped BigOperators
namespace MomentComparison
noncomputable def evenPart {n : ℕ} (f : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (f (Fin.cons true x) + f (Fin.cons false x)) / 2
noncomputable def oddPart {n : ℕ} (f : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (f (Fin.cons true x) - f (Fin.cons false x)) / 2
end MomentComparison


