-- Prove2me | Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
-- name    : LeanPool_CencovPetz_UniformScalarMultiple
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:16.646863+00:00
-- url     : https://prove2.me/theorems/75b4973e-9b57-4bc6-80fb-2eb3210c8daa
-- title:
--   Uniform Scalar Multiple
-- statement:
--   Definitions and structural lemmas for Uniform Scalar Multiple, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarMultiple.lean

module
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.BilinearForm.Properties
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
namespace TangentFin
namespace Bilin
open _root_.LeanPool.CencovPetz.TangentFin.Basis
variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]
end Bilin
end TangentFin
end LeanPool.CencovPetz


