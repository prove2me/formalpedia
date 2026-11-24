-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
-- name    : LeanPool_BlockSpectralSensitivity_Defs_Cube
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:06.139521+00:00
-- url     : https://prove2.me/theorems/828b1b05-27eb-44ca-8ebc-5a3f9db5d848
-- title:
--   Cube
-- statement:
--   Definitions and structural lemmas for Cube, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean

module
public import Mathlib.InformationTheory.Hamming
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
abbrev Input (V : Type*) : Type _ := V → Bool
def zeroInput (V : Type*) : Input V := fun _ ↦ false
variable {V : Type*}
section DecEq
variable [DecidableEq V]
def flipSet (x : Input V) (A : Finset V) : Input V := fun v ↦ if v ∈ A then !x v else x v
end DecEq
section Fintype
variable [Fintype V] [DecidableEq V]
end Fintype
end BSLambda


