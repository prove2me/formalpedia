-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ModuleIsoPieceSquares_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ModuleIsoPieceSquares_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:07:34.355266+00:00
-- url     : https://prove2.me/theorems/0854fae0-73c5-4f5f-8e52-f0924f025d9e
-- title:
--   Module Iso Piece Squares — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for module iso piece squares used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ModuleIsoPieceSquares.lean, selected declarations in lines 12–42; source SHA-256 f099bf1069514cd64ceeddff0b3633c1e90ce3e55787e96d33190670bac8ce2e; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Definitions.Def_LPCA_Solutions_LPCA_CochainSuccessorIso_SixOne20261024_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u v

theorem moduleHom_range_bot_of_subsingleton (R : Type u) [Ring R]
    (A N : ModuleCat.{u} R) (f : A ⟶ N) (h : Subsingleton A) : LinearMap.range f.hom = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro y ⟨x, rfl⟩
  have hx : x = 0 := h.elim x 0
  rw [hx, map_zero]
  exact Submodule.zero_mem _

theorem moduleIsoPieces_forward_square (R : Type u) [Ring R]
    (M₀ M₁ N₀ N₁ : ModuleCat.{u} R) (e₀ : M₀ ≅ N₀) (e₁ : M₁ ≅ N₁)
    (d : M₀ ⟶ M₁) (D : N₀ ⟶ N₁)
    (P₀ : M₀ → Prop) (P₁ : M₁ → Prop) (Q₀ : N₀ → Prop) (Q₁ : N₁ → Prop)
    (h₀ : ∀ x, P₀ x ↔ Q₀ (e₀.hom x)) (h₁ : ∀ x, P₁ x ↔ Q₁ (e₁.hom x))
    (hd : ∀ x, P₀ x → P₁ (d x)) (hs : e₀.hom ≫ D = d ≫ e₁.hom)
    (y : N₀) (hy : Q₀ y) : Q₁ (D y) := by
  obtain ⟨x, rfl⟩ := e₀.toLinearEquiv.surjective y
  have hx := hd x ((h₀ x).mpr hy)
  have h : D (e₀.hom x) = e₁.hom (d x) := congrArg (fun f => f x) hs
  change Q₁ (D (e₀.hom x))
  rw [h]
  exact (h₁ _).mp hx

theorem isoSquare_factor {C : Type u} [Category.{v} C] {M N P Q : C}
    (e : M ≅ N) (f : P ≅ Q) (r : M ⟶ P) (R : N ⟶ Q)
    (h : e.hom ≫ R = r ≫ f.hom) : e.inv ≫ r ≫ f.hom = R := by
  rw [← h, e.inv_hom_id_assoc]

@[simp] theorem cochainSuccessorIso_inv_f {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X Y : CochainComplex C ℕ) (E : ∀ p, X.X p ≅ Y.X p)
    (h : ∀ p, (E p).hom ≫ Y.d p (p + 1) = X.d p (p + 1) ≫ (E (p + 1)).hom) (p : ℕ) :
    (cochainSuccessorIso X Y E h).inv.f p = (E p).inv := rfl

end LPCA


