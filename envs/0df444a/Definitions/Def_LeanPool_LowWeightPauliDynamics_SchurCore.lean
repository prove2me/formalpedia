-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
-- name    : LeanPool_LowWeightPauliDynamics_SchurCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:48.137135+00:00
-- url     : https://prove2.me/theorems/cc2eb424-dde6-4baa-99aa-9450e130eba8
-- title:
--   Schur Core
-- statement:
--   Definitions and structural lemmas for Schur Core, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜]
noncomputable abbrev clm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m :=
  (Matrix.toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans LinearMap.toContinuousLinearMap A
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq κ]
end Lean4LPD


