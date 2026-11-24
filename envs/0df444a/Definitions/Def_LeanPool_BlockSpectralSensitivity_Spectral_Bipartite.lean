-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:57:52.516765+00:00
-- url     : https://prove2.me/theorems/fa087601-0994-41f7-80fd-cc32e8bc74df
-- title:
--   Bipartite
-- statement:
--   Definitions and structural lemmas for Bipartite, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev Ones (f : Input V → Bool) : Type _ := {x : Input V // f x = true}
abbrev Zeros (f : Input V → Bool) : Type _ := {x : Input V // f x = false}
noncomputable def biadj (f : Input V → Bool) : Matrix (Ones f) (Zeros f) ℝ :=
  Matrix.of fun x z => if hammingDist x.1 z.1 = 1 then (1 : ℝ) else 0
noncomputable def gram (f : Input V → Bool) : Matrix (Ones f) (Ones f) ℝ :=
  biadj f * (biadj f)ᵀ
end BSLambda


