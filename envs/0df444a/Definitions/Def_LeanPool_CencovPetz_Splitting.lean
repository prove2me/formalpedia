-- Prove2me | Definitions.Def_LeanPool_CencovPetz_Splitting
-- name    : LeanPool_CencovPetz_Splitting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:23:17.052265+00:00
-- url     : https://prove2.me/theorems/bbac8c4a-d0b1-4b02-8257-81c0132a9658
-- title:
--   Splitting
-- statement:
--   Definitions and structural lemmas for Splitting, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Splitting.lean

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
universe u
namespace MarkovMorphism
variable {α : Type u} [Fintype α]
abbrev SplitTarget (m : α → ℕ) : Type u :=
  Sigma fun a : α => Fin (m a)
variable (m : α → ℕ) (hm : ∀ a, 0 < m a)
noncomputable def split : MarkovMorphism α (SplitTarget (α := α) m) := by
  classical
  refine
    { K := fun a b => if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro a b
    by_cases h : b.1 = a <;> simp [h]
  · intro a
    have hm_ne : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
    -- Expand the sigma-sum, discard the non-matching fibers, and sum the constant on `Fin (m a)`.
    calc
      (∑ b : SplitTarget (α := α) m, (if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0))
          = ∑ x : α, ∑ _i : Fin (m x), if x = a then (1 : ℝ) / (m a : ℝ) else 0 := by
              simpa [SplitTarget] using
                (Fintype.sum_sigma (f := fun b : SplitTarget (α := α) m =>
                  if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0))
      _ = ∑ _i : Fin (m a), (1 : ℝ) / (m a : ℝ) := by
            -- Only the fiber over `a` contributes.
            simp [eq_comm]
      _ = (m a : ℝ) * ((1 : ℝ) / (m a : ℝ)) := by
            simp_all
      _ = 1 := by
            -- Cancel `m a`.
            field_simp [hm_ne]
  · intro b
    refine ⟨b.1, ?_⟩
    simp_all
noncomputable def merge : MarkovMorphism (SplitTarget (α := α) m) α := by
  classical
  refine
    { K := fun b a => if b.1 = a then (1 : ℝ) else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro b a
    by_cases h : b.1 = a <;> simp [h]
  · intro b
    -- Exactly one `a` matches `b.1`.
    simp
  · intro a
    refine ⟨⟨a, ⟨0, hm a⟩⟩, by simp⟩
end MarkovMorphism
end LeanPool.CencovPetz


