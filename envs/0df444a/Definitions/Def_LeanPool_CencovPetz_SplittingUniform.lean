-- Prove2me | Definitions.Def_LeanPool_CencovPetz_SplittingUniform
-- name    : LeanPool_CencovPetz_SplittingUniform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:24:46.583083+00:00
-- url     : https://prove2.me/theorems/3a760e03-085c-4765-b5c6-1d044a7b9d16
-- title:
--   Splitting Uniform
-- statement:
--   Definitions and structural lemmas for Splitting Uniform, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SplittingUniform.lean

module
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
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
namespace Simplex
variable {α : Type u} [Fintype α]
def IsSplitRepresentable (p : Simplex α) : Prop :=
  ∃ m : α → ℕ,
    (∀ a, 0 < m a) ∧
      ∀ a,
        p.p a = (m a : ℝ) / (Fintype.card (MarkovMorphism.SplitTarget (α := α) m) : ℝ)
end Simplex
namespace MarkovMorphism
variable {α : Type u} [Fintype α] [Nonempty α]
end MarkovMorphism
end LeanPool.CencovPetz


