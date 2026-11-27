-- Prove2me | Definitions.Def_RamanujanNested_Oscillatory
-- name    : RamanujanNested_Oscillatory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:06:06.809317+00:00
-- url     : https://prove2.me/theorems/14cc2f2e-1c99-5405-bb3c-01688b32b38f
-- title:
--   Oscillatory
-- statement:
--   Definitions and structural lemmas for Oscillatory, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Oscillatory.lean

module
public import Definitions.Def_RamanujanNested_ControlledNegative
public import Definitions.Def_RamanujanNested_Convergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
@[expose] public noncomputable def oscillatoryCoeff (α : ℝ) (k : ℕ) : ℝ := 1 + α * Real.sin (k : ℝ)
end RamanujanNested


