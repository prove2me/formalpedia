-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp
-- name    : LeanPool_LowWeightPauliDynamics_RotationExp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:07:01.558892+00:00
-- url     : https://prove2.me/theorems/db808559-cd0e-4b63-809a-5d553dbd5473
-- title:
--   Rotation Exp
-- statement:
--   Definitions and structural lemmas for Rotation Exp, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open scoped Nat
section TopologicalAlgebra
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}
variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [T2Space A]
end TopologicalAlgebra
namespace PauliString
variable {n : ℕ} {G : PauliString n}
end PauliString
end Lean4LPD


