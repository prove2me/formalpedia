-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CategoryHomogeneousAssembly_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CategoryHomogeneousAssembly_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:22.351992+00:00
-- url     : https://prove2.me/theorems/01b8ab19-5bec-4ea3-b8a6-6de913e0468b
-- title:
--   Category Homogeneous Assembly — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for category homogeneous assembly used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CategoryHomogeneousAssembly.lean, selected declarations in lines 11–25; source SHA-256 b9d9fdbc46b3002661075cbe3aa45a7803d1f844f00388b838c48d4ea14ef8b1; exact-source certificate Sapelo2 job 49296539.

import Mathlib.CategoryTheory.Category.Basic

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v

theorem categoryHomogeneousAssembly {C : Type u} [Category.{v} C]
    {A₀ A₁ B₀ B₁ H₀ H₁ N₀ N₁ : C}
    (E₀ : H₀ ⟶ N₀) (E₁ : H₁ ⟶ N₁) (i₀ : A₀ ⟶ H₀) (i₁ : A₁ ⟶ H₁)
    (r : H₁ ⟶ H₀) (v : A₁ ⟶ A₀) (e₀ : A₀ ⟶ B₀) (e₁ : A₁ ⟶ B₁)
    (p₀ : B₀ ⟶ N₀) (p₁ : B₁ ⟶ N₁) (cv : B₁ ⟶ B₀) (R : N₁ ⟶ N₀)
    (hs : i₁ ≫ r = v ≫ i₀) (h₀ : i₀ ≫ E₀ = e₀ ≫ p₀)
    (h₁ : i₁ ≫ E₁ = e₁ ≫ p₁) (hc : v ≫ e₀ = e₁ ≫ cv)
    (ht : p₁ ≫ R = cv ≫ p₀) :
    i₁ ≫ r ≫ E₀ = i₁ ≫ E₁ ≫ R := by
  calc
    _ = v ≫ i₀ ≫ E₀ := by rw [← Category.assoc, hs, Category.assoc]
    _ = v ≫ e₀ ≫ p₀ := by rw [h₀]
    _ = e₁ ≫ cv ≫ p₀ := by rw [← Category.assoc, hc, Category.assoc]
    _ = e₁ ≫ p₁ ≫ R := by rw [← ht]
    _ = _ := by rw [← Category.assoc, ← h₁, Category.assoc]

end LPCA


