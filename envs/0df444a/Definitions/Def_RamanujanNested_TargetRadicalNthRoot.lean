-- Prove2me | Definitions.Def_RamanujanNested_TargetRadicalNthRoot
-- name    : RamanujanNested_TargetRadicalNthRoot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:09:23.709812+00:00
-- url     : https://prove2.me/theorems/db11a3e8-ccab-48c0-b16e-f8a54f4f2610
-- title:
--   Target Radical Nth Root
-- statement:
--   Definitions and structural lemmas for Target Radical Nth Root, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/TargetRadicalNthRoot.lean

module
public import Definitions.Def_RamanujanNested_TargetRadical
public import Definitions.Def_RamanujanNested_NthRootChain
public import Mathlib
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
@[expose] public noncomputable def targetCoeffN (n : ℕ) (t : ℝ) : ℝ := (t ^ n - 1) / t
end RamanujanNested


