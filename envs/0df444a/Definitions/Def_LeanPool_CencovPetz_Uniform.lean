-- Prove2me | Definitions.Def_LeanPool_CencovPetz_Uniform
-- name    : LeanPool_CencovPetz_Uniform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:07.461208+00:00
-- url     : https://prove2.me/theorems/164e1d1b-811c-49c2-904a-78bf412e91da
-- title:
--   Uniform
-- statement:
--   Definitions and structural lemmas for Uniform, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Uniform.lean

module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
universe u
noncomputable abbrev uniformDistribution {α : Type u} [Fintype α] : α → ℝ :=
  Function.const α (1 / (Fintype.card α : ℝ))
def IsUniform {α : Type u} [Fintype α] (p : α → ℝ) : Prop :=
  ∀ a : α, p a = uniformDistribution (α := α) a
end LeanPool.CencovPetz


