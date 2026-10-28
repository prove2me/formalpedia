-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialFieldPieces_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_GradedPolynomialFieldPieces_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:07:18.993738+00:00
-- url     : https://prove2.me/theorems/0d8cd339-d038-4357-b5db-7de91f9ec05c
-- title:
--   Graded Polynomial Field Pieces — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for graded polynomial field pieces used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Bundle actual field subspaces of an existing native polynomial module
--   as its internal integer grading. Its native action and all pieces are fixed.
--
--   A native comparison square transfers preservation of specified field
--   subspaces without defining any of the underlying native maps by transport.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_GradedPolynomialFieldPieces.lean, selected declarations in lines 14–74; source SHA-256 7a4692b2e98f5ab08248898a11ed5eb0bdad4edfad9b2ec9cff7d0b8710a4df7; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialModuleCat_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgrade_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

theorem moduleRangeSquare_mem (R : Type u) [Ring R] (A B H N : ModuleCat.{u} R)
    (f : A ⟶ H) (g : B ⟶ N) (v : A ⟶ B) (m : H ⟶ N)
    (hs : f ≫ m = v ≫ g) (x : H) (hx : x ∈ LinearMap.range f.hom) :
    m x ∈ LinearMap.range g.hom := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨v y, ?_⟩
  exact (moduleSquare_apply R A H B N f m v g hs y).symm

/-- A native comparison square transfers preservation of specified field
subspaces without defining any of the underlying native maps by transport. -/
theorem nativeFieldPieces_comparison (R S : Type u) [Ring R] [Ring S] (f : R →+* S)
    (M₀ M₁ N₀ N₁ : ModuleCat.{u} S)
    (e₀ : M₀ ⟶ N₀) (e₁ : M₁ ⟶ N₁) (d : M₀ ⟶ M₁) (D : N₀ ⟶ N₁)
    (A₀ : Submodule R ((ModuleCat.restrictScalars f).obj M₀))
    (A₁ : Submodule R ((ModuleCat.restrictScalars f).obj M₁))
    (B₀ : Submodule R ((ModuleCat.restrictScalars f).obj N₀))
    (B₁ : Submodule R ((ModuleCat.restrictScalars f).obj N₁))
    (h₀ : ∀ x, x ∈ A₀ ↔ (ModuleCat.restrictScalars f).map e₀ x ∈ B₀)
    (h₁ : ∀ y, y ∈ A₁ ↔ (ModuleCat.restrictScalars f).map e₁ y ∈ B₁)
    (hD : ∀ z, z ∈ B₀ → (ModuleCat.restrictScalars f).map D z ∈ B₁)
    (hs : e₀ ≫ D = d ≫ e₁) (x : (ModuleCat.restrictScalars f).obj M₀) (hx : x ∈ A₀) :
    (ModuleCat.restrictScalars f).map d x ∈ A₁ := by
  have h : (ModuleCat.restrictScalars f).map e₀ ≫ (ModuleCat.restrictScalars f).map D =
      (ModuleCat.restrictScalars f).map d ≫ (ModuleCat.restrictScalars f).map e₁ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hs]
  apply (h₁ _).mpr
  have hv := moduleSquare_apply R _ _ _ _ _ _ _ _ h x
  rw [← hv]
  exact hD _ ((h₀ x).mp hx)

theorem moduleIso_predicate_inv (S : Type u) [Ring S] (M N : ModuleCat.{u} S)
    (e : M ≅ N) (P : M → Prop) (Q : N → Prop)
    (h : ∀ x, P x ↔ Q (e.hom x)) (y : N) : Q y ↔ P (e.inv y) := by
  have h' := h (e.inv y)
  have hi : e.hom (e.inv y) = y := e.toLinearEquiv.apply_symm_apply y
  rw [hi] at h'
  exact h'.symm

variable {V W : Type u} [DecidableEq V] [Fintype V] [DecidableEq W]
variable (k : Type u) [Field k]

/-- Bundle actual field subspaces of an existing native polynomial module
as its internal integer grading. Its native action and all pieces are fixed. -/
noncomputable def gradedPolynomialOfFieldPieces (e : W ↪ V)
    (M : ModuleCat.{u} (MvPolynomial W k))
    (Q : (V → ℤ) → Submodule k
      ((ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M))
    (hQ : DirectSum.IsInternal Q)
    (hX : ∀ (j : W) (a : V → ℤ) (x : (ModuleCat.restrictScalars
      (MvPolynomial.C : k →+* MvPolynomial W k)).obj M),
      x ∈ Q a → polynomialVariableFieldHom k W M j x ∈ Q (shiftDegreeAt a (e j))) :
    GradedPolynomialModule k e where
  module := M
  piece a := (Q a).toAddSubgroup
  internal := hQ
  constant_mem c a x hx := by
    change c • (show (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M from x) ∈ Q a
    exact (Q a).smul_mem c hx
  variable_mem j a x hx := by
    change polynomialVariableFieldHom k W M j x ∈ Q (shiftDegreeAt a (e j))
    exact hX j a x hx

end LPCA


