-- Prove2me | Definitions.Def_LeanPool_CencovPetz_UniformSimplex
-- name    : LeanPool_CencovPetz_UniformSimplex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:21:58.930412+00:00
-- url     : https://prove2.me/theorems/50b76ecf-eae2-4cb6-b6e9-55925fefc09d
-- title:
--   Uniform Simplex
-- statement:
--   Definitions and structural lemmas for Uniform Simplex, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformSimplex.lean

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Definitions.Def_LeanPool_CencovPetz_Uniform
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pos
public import Theorems.Thm_LeanPool_CencovPetz_uniformDistribution_sum_one
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
variable {α : Type*} [Fintype α] [Nonempty α]
namespace Simplex
noncomputable def uniform : Simplex α where
  p := uniformDistribution (α := α)
  pos := by
    intro a
    have hcard : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
    simpa [uniformDistribution] using (one_div_pos.2 hcard)
  sum_eq_one := by
    exact uniformDistribution_sum_one (α := α)
end Simplex
end LeanPool.CencovPetz


