-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
-- name    : LeanPool_BlockSpectralSensitivity_Construction_Conflict
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:47:00.35396+00:00
-- url     : https://prove2.me/theorems/29e4e011-5244-48e1-acb7-7b436fa455f7
-- title:
--   Conflict
-- statement:
--   Definitions and structural lemmas for Conflict, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
namespace Construction
variable {ι : Type*} {r : ℕ}
section Cert
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
end Cert
section Fintype
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
end Fintype
end Construction
end BSLambda


