-- Prove2me | Definitions.Def_LeanPool_CencovPetz_SimplexTopology
-- name    : LeanPool_CencovPetz_SimplexTopology
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:29.092008+00:00
-- url     : https://prove2.me/theorems/ca0c8cdf-738a-4164-9c78-2d4922d1e3fb
-- title:
--   Simplex Topology
-- statement:
--   Definitions and structural lemmas for Simplex Topology, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SimplexTopology.lean

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
namespace Simplex
instance : TopologicalSpace (Simplex α) :=
  TopologicalSpace.induced (fun p : Simplex α => p.p) inferInstance
end Simplex
end LeanPool.CencovPetz


