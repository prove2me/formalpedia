-- Prove2me | Definitions.Def_RamanujanNested_IdentityChain
-- name    : RamanujanNested_IdentityChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T04:58:57.725153+00:00
-- url     : https://prove2.me/theorems/bcffeba9-c4d5-4695-b724-02b3f65d60f4
-- title:
--   Identity Chain
-- statement:
--   Definitions and structural lemmas for Identity Chain, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChain.lean

module
public import Definitions.Def_RamanujanNested_Defs
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
@[expose] public noncomputable def chainClosedForm (N k : ℕ) : ℝ := (N : ℝ) + (k : ℝ) - 1
end RamanujanNested


