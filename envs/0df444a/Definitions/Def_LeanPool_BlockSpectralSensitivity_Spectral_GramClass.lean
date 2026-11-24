-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_GramClass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:14:17.78012+00:00
-- url     : https://prove2.me/theorems/b4793685-b03e-42bf-b06b-c52d00402a95
-- title:
--   Gram Class
-- statement:
--   Definitions and structural lemmas for Gram Class, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
end CertFamily
end BSLambda


