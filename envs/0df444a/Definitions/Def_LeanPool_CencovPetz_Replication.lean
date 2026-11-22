-- Prove2me | Definitions.Def_LeanPool_CencovPetz_Replication
-- name    : LeanPool_CencovPetz_Replication
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:23:29.871548+00:00
-- url     : https://prove2.me/theorems/b713d362-8704-4b60-9391-bde54d91046a
-- title:
--   Replication
-- statement:
--   Definitions and structural lemmas for Replication, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
namespace MarkovMorphism
noncomputable def replicate (m : ℕ) (hm : 0 < m) : MarkovMorphism α (α × Fin m) := by
  classical
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := hm_pos.ne'
  refine
    { K := fun a b => if a = b.1 then (1 : ℝ) / m else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro a b
    by_cases h : a = b.1 <;> simp [h, hm_pos.le]
  · intro a
    -- Sum over `α × Fin m` by splitting into a sum over `α` and over `Fin m`.
    -- `Fintype.sum_prod_type` is the fiberwise-sum identity.
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, hm0]
  · intro b
    refine ⟨b.1, ?_⟩
    simp_all
noncomputable def coarsen (m : ℕ) (hm : 0 < m) : MarkovMorphism (α × Fin m) α := by
  classical
  refine MarkovMorphism.deterministic (α := α × Fin m) (β := α) Prod.fst ?_
  intro a
  refine ⟨(a, ⟨0, hm⟩), rfl⟩
end MarkovMorphism
end LeanPool.CencovPetz


