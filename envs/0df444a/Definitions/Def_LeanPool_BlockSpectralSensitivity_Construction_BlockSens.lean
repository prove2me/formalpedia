-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
-- name    : LeanPool_BlockSpectralSensitivity_Construction_BlockSens
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:47:13.857799+00:00
-- url     : https://prove2.me/theorems/314c8c57-d433-4bae-8f61-462d3cd28530
-- title:
--   Block Sens
-- statement:
--   Definitions and structural lemmas for Block Sens, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/BlockSens.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
namespace Construction
variable {ι : Type*} {r : ℕ}
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
end Construction
end BSLambda


