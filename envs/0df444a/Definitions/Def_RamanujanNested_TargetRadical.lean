-- Prove2me | Definitions.Def_RamanujanNested_TargetRadical
-- name    : RamanujanNested_TargetRadical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:02:12.295785+00:00
-- url     : https://prove2.me/theorems/06a55a99-9566-4b31-a1f5-7b6d59e0caa5
-- title:
--   Target Radical
-- statement:
--   Definitions and structural lemmas for Target Radical, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/TargetRadical.lean

module
public import Definitions.Def_RamanujanNested_Bounds
public import Mathlib
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
@[expose] public noncomputable def targetCoeff (t : ℝ) : ℝ := t - 1 / t
end RamanujanNested


