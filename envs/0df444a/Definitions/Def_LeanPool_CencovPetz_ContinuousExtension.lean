-- Prove2me | Definitions.Def_LeanPool_CencovPetz_ContinuousExtension
-- name    : LeanPool_CencovPetz_ContinuousExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:53.250904+00:00
-- url     : https://prove2.me/theorems/3c13b9f0-b4fb-4fbd-a9fd-f5d8be8002be
-- title:
--   Continuous Extension
-- statement:
--   Definitions and structural lemmas for Continuous Extension, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ContinuousExtension.lean

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Topology.Metrizable.Uniformity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
end LeanPool.CencovPetz


