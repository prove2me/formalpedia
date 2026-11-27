-- Prove2me | Definitions.Def_RamanujanNested_Reconstruction
-- name    : RamanujanNested_Reconstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:05:42.987202+00:00
-- url     : https://prove2.me/theorems/2802ea67-160d-5abb-bd6c-c4c19364d512
-- title:
--   Reconstruction
-- statement:
--   Definitions and structural lemmas for Reconstruction, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Reconstruction.lean

module
public import Definitions.Def_RamanujanNested_IdentityChain
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
@[expose] public noncomputable def reconstructCoeff (R : ℕ → ℝ) (k : ℕ) : ℝ :=
  (R k ^ 2 - 1) / R (k + 1)
end RamanujanNested


