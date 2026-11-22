-- Prove2me | Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
-- name    : LeanPool_CencovPetz_PermutationInvariance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:27.331908+00:00
-- url     : https://prove2.me/theorems/7abd76a7-7b87-4636-9bbe-997c4fe3f73a
-- title:
--   Permutation Invariance
-- statement:
--   Definitions and structural lemmas for Permutation Invariance, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean

module
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
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
variable {α β : Type u} [Fintype α] [Fintype β]
namespace MarkovMorphism
end MarkovMorphism
namespace MonotoneMetricFamily
end MonotoneMetricFamily
end LeanPool.CencovPetz


