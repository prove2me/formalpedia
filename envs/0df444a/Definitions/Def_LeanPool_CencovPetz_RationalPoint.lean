-- Prove2me | Definitions.Def_LeanPool_CencovPetz_RationalPoint
-- name    : LeanPool_CencovPetz_RationalPoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:25.981174+00:00
-- url     : https://prove2.me/theorems/87371e3a-a3bb-4f98-b00d-c40abbf63eac
-- title:
--   Rational Point
-- statement:
--   Definitions and structural lemmas for Rational Point, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalPoint.lean

module
public import Definitions.Def_LeanPool_CencovPetz_SplittingUniform
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
namespace MarkovMorphism
variable {α : Type u} [Fintype α]
end MarkovMorphism
namespace Simplex
variable {α : Type u} [Fintype α]
def IsRational (p : Simplex α) : Prop :=
  ∃ m : α → ℕ,
    (∀ a, 0 < m a) ∧
      ∀ a, p.p a = (m a : ℝ) / ((∑ a : α, m a : ℕ) : ℝ)
end Simplex
end LeanPool.CencovPetz


