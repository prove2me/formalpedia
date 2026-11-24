-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:14:45.5838+00:00
-- url     : https://prove2.me/theorems/18850f54-ada7-49ed-a42a-cbbcdc948149
-- title:
--   Cert Union
-- statement:
--   Definitions and structural lemmas for Cert Union, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
namespace CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
noncomputable def diagMat : Matrix (Ones F.ind) (Ones F.ind) ℝ :=
  Matrix.diagonal (gram F.ind).diag
noncomputable def offMat : Matrix (Ones F.ind) (Ones F.ind) ℝ := Matrix.of fun x y =>
  if F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 then gram F.ind x y else 0
noncomputable def offBound : ℝ :=
  Real.sqrt (((F.A * (F.c - 1) : ℕ) : ℝ) * (F.B : ℝ))
end CertFamily
end BSLambda


