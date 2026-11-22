-- Prove2me | Definitions.Def_LeanPool_CencovPetz_FisherContinuity
-- name    : LeanPool_CencovPetz_FisherContinuity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:55.83209+00:00
-- url     : https://prove2.me/theorems/00d24412-8c4c-4a23-9e25-07aee5e99941
-- title:
--   Fisher Continuity
-- statement:
--   Definitions and structural lemmas for Fisher Continuity, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/FisherContinuity.lean

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
namespace Simplex
variable {α : Type*} [Fintype α]
end Simplex
end LeanPool.CencovPetz


