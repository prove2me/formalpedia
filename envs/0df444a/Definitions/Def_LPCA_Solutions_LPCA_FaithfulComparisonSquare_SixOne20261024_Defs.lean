-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaithfulComparisonSquare_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_FaithfulComparisonSquare_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:34.952081+00:00
-- url     : https://prove2.me/theorems/503f04dc-053c-4d13-95d7-52acbc70a35f
-- title:
--   Faithful Comparison Square — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for faithful comparison square used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Differential compatibility can be checked in faithful field views with
--   all four comparison squares retained explicitly.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_FaithfulComparisonSquare.lean, selected declarations in lines 11–37; source SHA-256 3bdc4ca2c7d477820e2a222eefb9c1134b04fdf15e9f3fd8527190ccf60373a2; exact-source certificate Sapelo2 job 49296539.

import Mathlib.CategoryTheory.Functor.FullyFaithful

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v u' v'

/-- Differential compatibility can be checked in faithful field views with
all four comparison squares retained explicitly. -/
theorem faithfulComparisonSquare {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful]
    {M₀ M₁ N₀ N₁ : C} {P₀ P₁ Q₀ Q₁ : D}
    (α₀ : F.obj M₀ ≅ P₀) (α₁ : F.obj M₁ ≅ P₁)
    (β₀ : F.obj N₀ ≅ Q₀) (β₁ : F.obj N₁ ≅ Q₁)
    (e₀ : M₀ ⟶ N₀) (e₁ : M₁ ⟶ N₁) (E₀ : P₀ ⟶ Q₀) (E₁ : P₁ ⟶ Q₁)
    (d : M₀ ⟶ M₁) (D' : N₀ ⟶ N₁) (dP : P₀ ⟶ P₁) (dQ : Q₀ ⟶ Q₁)
    (he₀ : F.map e₀ ≫ β₀.hom = α₀.hom ≫ E₀)
    (he₁ : F.map e₁ ≫ β₁.hom = α₁.hom ≫ E₁)
    (hs : F.map d ≫ α₁.hom = α₀.hom ≫ dP)
    (ht : F.map D' ≫ β₁.hom = β₀.hom ≫ dQ)
    (hE : E₀ ≫ dQ = dP ≫ E₁) : e₀ ≫ D' = d ≫ e₁ := by
  apply F.map_injective
  apply (cancel_mono β₁.hom).mp
  simp only [Functor.map_comp, Category.assoc]
  calc
    _ = F.map e₀ ≫ β₀.hom ≫ dQ := by rw [ht]
    _ = (F.map e₀ ≫ β₀.hom) ≫ dQ := by simp only [Category.assoc]
    _ = (α₀.hom ≫ E₀) ≫ dQ := by rw [he₀]
    _ = α₀.hom ≫ E₀ ≫ dQ := by simp only [Category.assoc]
    _ = α₀.hom ≫ dP ≫ E₁ := by rw [hE]
    _ = (α₀.hom ≫ dP) ≫ E₁ := by simp only [Category.assoc]
    _ = (F.map d ≫ α₁.hom) ≫ E₁ := by rw [← hs]
    _ = F.map d ≫ α₁.hom ≫ E₁ := by simp only [Category.assoc]
    _ = _ := by rw [← he₁]

end LPCA


