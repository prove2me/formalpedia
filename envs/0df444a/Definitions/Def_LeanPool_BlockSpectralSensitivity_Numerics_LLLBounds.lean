-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
-- name    : LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:47.197696+00:00
-- url     : https://prove2.me/theorems/9965b74d-f341-4597-91b0-70e6e1546aeb
-- title:
--   LLLBounds
-- statement:
--   Definitions and structural lemmas for LLLBounds, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda.Numerics
def D11 : ℕ := 2146200875100
def D12 : ℕ := 209572451535510643927671555
def D21 : ℕ := 7726323150360
def D22 : ℕ := 753455972623601870517771054
noncomputable def p1 : ℝ := 1 / 144 ^ 6
noncomputable def p2 : ℝ := 1300311466573824 / 144 ^ 20
noncomputable def x1 : ℝ := 29 / (16 * 144 ^ 6)
noncomputable def x2 : ℝ := 17 * 1300311466573824 / (2 * 144 ^ 20)
end BSLambda.Numerics


