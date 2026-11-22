-- Prove2me | Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
-- name    : LeanPool_CencovPetz_MarkovMorphism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:22:06.615368+00:00
-- url     : https://prove2.me/theorems/e6087046-66e7-474c-a8ca-273e2cb7d251
-- title:
--   Markov Morphism
-- statement:
--   Definitions and structural lemmas for Markov Morphism, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean

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
variable {α β : Type*} [Fintype α] [Fintype β]
structure MarkovMorphism (α β : Type*) [Fintype α] [Fintype β] : Type _ where
  /-- Transition weights `K a b`. -/
  K : α → β → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ a b, 0 ≤ K a b
  /-- Each row sums to `1`. -/
  row_sum_eq_one : ∀ a, (∑ b, K a b) = 1
  /-- Each column has a strictly positive entry (so the open simplex maps to the open simplex). -/
  col_pos : ∀ b, ∃ a, 0 < K a b
namespace MarkovMorphism
variable (κ : MarkovMorphism α β)
noncomputable def deterministic (g : α → β) (hg : Function.Surjective g) : MarkovMorphism α β := by
  classical
  refine
    { K := fun a b => if g a = b then (1 : ℝ) else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro a b
    by_cases h : g a = b <;> simp [h]
  · intro a
    simp
  · intro b
    rcases hg b with ⟨a0, rfl⟩
    refine ⟨a0, ?_⟩
    simp
noncomputable def pushforward (p : Simplex α) : Simplex β := by
  classical
  refine
    { p := fun b => ∑ a, p.p a * κ.K a b
      pos := ?_
      sum_eq_one := ?_ }
  · intro b
    rcases κ.col_pos b with ⟨a0, ha0⟩
    have h_nonneg : ∀ a : α, 0 ≤ p.p a * κ.K a b :=
      fun a => mul_nonneg (p.pos a).le (κ.nonneg a b)
    have h_pos : 0 < ∑ a : α, p.p a * κ.K a b := by
      -- Use that one term is strictly positive.
      refine Finset.sum_pos' (s := (Finset.univ : Finset α))
        (f := fun a => p.p a * κ.K a b) (h := fun a _ => h_nonneg a) ?_
      refine ⟨a0, by simp, mul_pos (p.pos a0) ha0⟩
    simpa using h_pos
  · -- `∑_b ∑_a p(a) K(a,b) = ∑_a p(a) (∑_b K(a,b)) = ∑_a p(a)`.
    have hcomm :
        (∑ b : β, ∑ a : α, p.p a * κ.K a b) =
          ∑ a : α, ∑ b : β, p.p a * κ.K a b := by
      simpa using
        (Finset.sum_comm (s := (Finset.univ : Finset β)) (t := (Finset.univ : Finset α))
          (f := fun b a => p.p a * κ.K a b))
    calc
      (∑ b : β, ∑ a : α, p.p a * κ.K a b)
          = ∑ a : α, ∑ b : β, p.p a * κ.K a b := hcomm
      _ = ∑ a : α, p.p a * (∑ b : β, κ.K a b) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            simp [Finset.mul_sum]
      _ = ∑ a : α, p.p a := by simp [κ.row_sum_eq_one]
      _ = 1 := p.sum_eq_one
noncomputable def tangentPushforward (u : tangentSpace (α := α)) : tangentSpace (α := β) := by
  classical
  refine ⟨fun b => ∑ a : α, ((u : α → ℝ) a) * κ.K a b, ?_⟩
  -- Prove the pushed-forward vector has total sum `0`.
  have hcomm :
      (∑ b : β, ∑ a : α, ((u : α → ℝ) a) * κ.K a b) =
        ∑ a : α, ∑ b : β, ((u : α → ℝ) a) * κ.K a b := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset β)) (t := (Finset.univ : Finset α))
        (f := fun b a => ((u : α → ℝ) a) * κ.K a b))
  have hu_sum : (∑ a : α, (u : α → ℝ) a) = 0 :=
    (tangentSpace.mem_iff (α := α) (u := (u : α → ℝ))).1 u.property
  refine (tangentSpace.mem_iff (α := β) (u := fun b => ∑ a : α, ((u : α → ℝ) a) * κ.K a b)).2 ?_
  calc
    (∑ b : β, (∑ a : α, ((u : α → ℝ) a) * κ.K a b))
        = ∑ a : α, ∑ b : β, ((u : α → ℝ) a) * κ.K a b := hcomm
    _ = ∑ a : α, (u : α → ℝ) a * (∑ b : β, κ.K a b) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          simp [Finset.mul_sum]
    _ = ∑ a : α, (u : α → ℝ) a := by simp [κ.row_sum_eq_one]
    _ = 0 := hu_sum
@[simp] lemma pushforward_apply (p : Simplex α) (b : β) :
    (κ.pushforward p).p b = ∑ a : α, p.p a * κ.K a b :=
  rfl
@[simp] lemma tangentPushforward_apply (u : tangentSpace (α := α)) (b : β) :
    (κ.tangentPushforward u : β → ℝ) b = ∑ a : α, ((u : α → ℝ) a) * κ.K a b :=
  rfl
noncomputable def tangentPushforwardLinear : tangentSpace (α := α) →ₗ[ℝ] tangentSpace (α := β) := by
  classical
  refine
    { toFun := κ.tangentPushforward
      map_add' := ?_
      map_smul' := ?_ }
  · intro u v
    ext b
    simp [MarkovMorphism.tangentPushforward_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · intro c u
    ext b
    simp [MarkovMorphism.tangentPushforward_apply, Pi.smul_apply, smul_eq_mul,
      mul_assoc, Finset.mul_sum]
end MarkovMorphism
end LeanPool.CencovPetz


