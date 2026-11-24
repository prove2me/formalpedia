-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:09.574832+00:00
-- url     : https://prove2.me/theorems/83904b68-ae2c-4329-8d34-f806416c56d0
-- title:
--   Schur Test
-- statement:
--   Definitions and structural lemmas for Schur Test, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped Matrix Matrix.Norms.L2Operator
namespace Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}
end Matrix


