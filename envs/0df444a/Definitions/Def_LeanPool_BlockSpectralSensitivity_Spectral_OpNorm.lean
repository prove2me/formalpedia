-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:58:22.09059+00:00
-- url     : https://prove2.me/theorems/1aebcf4e-d416-4219-b065-5108ba3d3faf
-- title:
--   Op Norm
-- statement:
--   Definitions and structural lemmas for Op Norm, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
def signPattern (f : Input V → Bool) (x : Input V) : ℝ := if f x then 1 else -1
end BSLambda


