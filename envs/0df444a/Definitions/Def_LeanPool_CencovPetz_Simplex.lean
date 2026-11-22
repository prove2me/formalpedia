-- Prove2me | Definitions.Def_LeanPool_CencovPetz_Simplex
-- name    : LeanPool_CencovPetz_Simplex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:09.421821+00:00
-- url     : https://prove2.me/theorems/febbd600-2e3d-4a0c-b612-dcc087bb2cd5
-- title:
--   Simplex
-- statement:
--   Definitions and structural lemmas for Simplex, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean

module
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
variable {α : Type*} [Fintype α]
structure Simplex (α : Type*) [Fintype α] : Type _ where
  /-- Coordinate representation `p : α → ℝ`. -/
  p : α → ℝ
  /-- Strict positivity of each coordinate. -/
  pos : ∀ a, 0 < p a
  /-- Normalization. -/
  sum_eq_one : (∑ a, p a) = 1
namespace Simplex
variable (p : Simplex α)
@[ext] lemma ext {p q : Simplex α} (h : p.p = q.p) : p = q := by
  cases p
  simp_all
end Simplex
noncomputable def sumLinearMap (α : Type*) [Fintype α] : (α → ℝ) →ₗ[ℝ] ℝ := by
  classical
  refine
    { toFun := fun u => ∑ a, u a
      map_add' := ?_
      map_smul' := ?_ }
  · intro u v
    -- `∑ (u+v) = ∑ u + ∑ v`.
    simpa [Pi.add_apply] using
      (Finset.sum_add_distrib (s := (Finset.univ : Finset α)) (f := u) (g := v))
  · intro c u
    -- `∑ (c • u) = c • ∑ u`.
    simpa [Pi.smul_apply, smul_eq_mul] using
      (Finset.mul_sum (s := (Finset.univ : Finset α)) (a := c) (f := u)).symm
noncomputable abbrev tangentSpace (α : Type*) [Fintype α] : Submodule ℝ (α → ℝ) :=
  LinearMap.ker (sumLinearMap α)
namespace tangentSpace
variable (α)
end tangentSpace
noncomputable def fisherBilin (p : Simplex α) : LinearMap.BilinForm ℝ (tangentSpace (α := α)) := by
  classical
  refine LinearMap.mk₂ ℝ
    (fun u v => ∑ a, ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a) ?_ ?_ ?_ ?_
  · intro u₁ u₂ v
    -- Additivity in the first argument.
    simp [add_mul, add_div, Finset.sum_add_distrib]
  · intro c u v
    -- Homogeneity in the first argument.
    -- Factor `c` out of the finite sum.
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      (Finset.mul_sum (s := (Finset.univ : Finset α)) (a := c)
        (f := fun a => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a)).symm
  · intro u v₁ v₂
    -- Additivity in the second argument.
    simp [mul_add, add_div, Finset.sum_add_distrib]
  · intro c u v
    -- Homogeneity in the second argument.
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      (Finset.mul_sum (s := (Finset.univ : Finset α)) (a := c)
        (f := fun a => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a)).symm
namespace fisherBilin
variable (p : Simplex α)
end fisherBilin
end LeanPool.CencovPetz


