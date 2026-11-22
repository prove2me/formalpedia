-- Prove2me | Definitions.Def_LeanPool_CencovPetz_ReplicationInvariance
-- name    : LeanPool_CencovPetz_ReplicationInvariance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:30.520056+00:00
-- url     : https://prove2.me/theorems/1f4aa18b-7484-409e-a197-dc1fa25a9b1c
-- title:
--   Replication Invariance
-- statement:
--   Definitions and structural lemmas for Replication Invariance, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ReplicationInvariance.lean

module
public import Definitions.Def_LeanPool_CencovPetz_Replication
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
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
namespace MonotoneMetricFamily
end MonotoneMetricFamily
end LeanPool.CencovPetz


