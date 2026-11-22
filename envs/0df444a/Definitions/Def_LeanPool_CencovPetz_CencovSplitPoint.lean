-- Prove2me | Definitions.Def_LeanPool_CencovPetz_CencovSplitPoint
-- name    : LeanPool_CencovPetz_CencovSplitPoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:28:45.443674+00:00
-- url     : https://prove2.me/theorems/0c1b7df2-a498-4389-921f-48c4908cdf9d
-- title:
--   Cencov Split Point
-- statement:
--   Definitions and structural lemmas for Cencov Split Point, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/CencovSplitPoint.lean

module
public import Definitions.Def_LeanPool_CencovPetz_RationalPoint
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Definitions.Def_LeanPool_CencovPetz_SplittingInvariance
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
namespace MonotoneMetricFamily
open MarkovMorphism
end MonotoneMetricFamily
end LeanPool.CencovPetz


