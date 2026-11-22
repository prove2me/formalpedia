-- Prove2me | Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
-- name    : LeanPool_CencovPetz_SufficientStatistic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:21:58.216327+00:00
-- url     : https://prove2.me/theorems/ff93cbc9-8030-438d-98b9-cf03d24bad23
-- title:
--   Sufficient Statistic
-- statement:
--   Definitions and structural lemmas for Sufficient Statistic, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SufficientStatistic.lean

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pos
public import Theorems.Thm_LeanPool_CencovPetz_tangentSpace_mem_iff
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
namespace Simplex
noncomputable def pushforward (g : α → β) (hg : Function.Surjective g) (p : Simplex α) :
    Simplex β := by
  classical
  refine
    { p := fun b => ∑ a with g a = b, p.p a
      pos := ?_
      sum_eq_one := ?_ }
  · intro b
    rcases hg b with ⟨a0, rfl⟩
    -- The fiber `{a | g a = g a0}` contains `a0`, and every `p.p a` is nonnegative.
    have h_nonneg : ∀ a : α, 0 ≤ p.p a := fun a => (p.pos a).le
    have h_pos : 0 < ∑ a ∈ (Finset.univ.filter fun a : α => g a = g a0), p.p a := by
      refine Finset.sum_pos' (s := (Finset.univ.filter fun a : α => g a = g a0))
        (f := p.p) (h := fun a _ => h_nonneg a) ?_
      exact ⟨a0, by simp, p.pos a0⟩
    simpa using h_pos
  · -- Normalization follows from summing over fibers.
    have hfib :
        (∑ b : β, ∑ a with g a = b, p.p a) = ∑ a : α, p.p a := by
      simpa using (Finset.sum_fiberwise (s := (Finset.univ : Finset α)) (g := g) (f := p.p))
    simpa [hfib] using p.sum_eq_one
@[simp] lemma pushforward_apply (g : α → β) (hg : Function.Surjective g) (p : Simplex α) (b : β) :
    (pushforward g hg p).p b = ∑ a with g a = b, p.p a :=
  rfl
end Simplex
noncomputable def tangentPushforward (g : α → β) (u : tangentSpace (α := α)) :
    tangentSpace (α := β) := by
  classical
  refine ⟨fun b => ∑ a with g a = b, ((u : α → ℝ) a), ?_⟩
  -- Sum over fibers gives back the original total sum.
  have hfib :
      (∑ b : β, ∑ a with g a = b, ((u : α → ℝ) a)) = ∑ a : α, (u : α → ℝ) a := by
    simpa using
      (Finset.sum_fiberwise (s := (Finset.univ : Finset α)) (g := g) (f := fun a => (u : α → ℝ) a))
  have hu_sum : (∑ a : α, (u : α → ℝ) a) = 0 :=
    (tangentSpace.mem_iff (α := α) (u := (u : α → ℝ))).1 u.property
  -- Finish via the membership characterization of `tangentSpace`.
  refine (tangentSpace.mem_iff (α := β) (u := fun b => ∑ a with g a = b, ((u : α → ℝ) a))).2 ?_
  simp [hfib, hu_sum]
end LeanPool.CencovPetz


