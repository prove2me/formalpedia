-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:12.537927+00:00
-- url     : https://prove2.me/theorems/f1127316-9e54-4d0a-a4df-b2faeb48b4d2
-- title:
--   Hermitian
-- statement:
--   Definitions and structural lemmas for Hermitian, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean

module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Matrix.IsHermitian
open scoped Matrix Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
end Matrix.IsHermitian


