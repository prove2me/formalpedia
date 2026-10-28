-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialModuleCat_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_GradedPolynomialModuleCat_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:45.651984+00:00
-- url     : https://prove2.me/theorems/bd3f7519-4390-4a59-8c98-4d224dced1d5
-- title:
--   Graded Polynomial Module Cat — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for graded polynomial module cat used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   An internally integer-graded module over the polynomial ring on W,
--   with deg(X_j)=the unit degree at e(j). Constant and variable compatibility
--   encode the standard polynomial graded action; morphisms retain native
--   polynomial linearity and preserve every specified homogeneous subgroup.
--
--   A native polynomial-linear isomorphism with exact grade membership
--   iff is an isomorphism in the category of graded polynomial modules.
--
--   Equip an existing native module and its specified homogeneous
--   subgroups with the graded action verified through a native module iso.
--   Neither the module action nor the supplied subgroups are changed.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_GradedPolynomialModuleCat.lean, selected declarations in lines 18–92; source SHA-256 6bb30f9f2fa9da63b10819fc5e38f92c8a3ff8a7463aec3d75cad4f423df0832; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.MvPolynomial.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V W : Type u} [DecidableEq V] [Fintype V] [DecidableEq W]
variable (k : Type u) [Field k] (e : W ↪ V)

def shiftDegreeAt (a : V → ℤ) (j : V) : V → ℤ := fun v => a v + if v = j then 1 else 0

/-- An internally integer-graded module over the polynomial ring on W,
with deg(X_j)=the unit degree at e(j). Constant and variable compatibility
encode the standard polynomial graded action; morphisms retain native
polynomial linearity and preserve every specified homogeneous subgroup. -/
structure GradedPolynomialModule where
  module : ModuleCat.{u} (MvPolynomial W k)
  piece : (V → ℤ) → AddSubgroup module
  internal : DirectSum.IsInternal piece
  constant_mem : ∀ (c : k) (a : V → ℤ) (x : module), x ∈ piece a →
    (MvPolynomial.C c : MvPolynomial W k) • x ∈ piece a
  variable_mem : ∀ (j : W) (a : V → ℤ) (x : module), x ∈ piece a →
    (MvPolynomial.X j : MvPolynomial W k) • x ∈ piece (shiftDegreeAt a (e j))

namespace GradedPolynomialModule

variable {k e}

structure Hom (A B : GradedPolynomialModule k e) where
  map : A.module ⟶ B.module
  map_piece : ∀ (a : V → ℤ) (x : A.module), x ∈ A.piece a → map x ∈ B.piece a

@[ext] theorem hom_ext {A B : GradedPolynomialModule k e} {f g : Hom A B}
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

noncomputable instance : Category (GradedPolynomialModule k e) where
  Hom A B := Hom A B
  id A := ⟨𝟙 A.module, fun _ _ hx => hx⟩
  comp f g := ⟨f.map ≫ g.map, fun a x hx => g.map_piece a _ (f.map_piece a x hx)⟩
  id_comp f := by apply hom_ext; exact Category.id_comp f.map
  comp_id f := by apply hom_ext; exact Category.comp_id f.map
  assoc f g h := by apply hom_ext; exact Category.assoc f.map g.map h.map

noncomputable def forget : GradedPolynomialModule k e ⥤ ModuleCat.{u} (MvPolynomial W k) where
  obj A := A.module
  map f := f.map



/-- A native polynomial-linear isomorphism with exact grade membership
iff is an isomorphism in the category of graded polynomial modules. -/
noncomputable def isoOfPieces {A B : GradedPolynomialModule k e}
    (f : A.module ≅ B.module)
    (hf : ∀ (a : V → ℤ) (x : A.module), x ∈ A.piece a ↔ f.hom x ∈ B.piece a) : A ≅ B where
  hom := ⟨f.hom, fun a x hx => (hf a x).mp hx⟩
  inv := ⟨f.inv, fun a y hy => (hf a (f.inv y)).mpr (by
    simpa only [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply] using hy)⟩
  hom_inv_id := by apply hom_ext; exact f.hom_inv_id
  inv_hom_id := by apply hom_ext; exact f.inv_hom_id

/-- Equip an existing native module and its specified homogeneous
subgroups with the graded action verified through a native module iso.
Neither the module action nor the supplied subgroups are changed. -/
noncomputable def ofIso (A : GradedPolynomialModule k e)
    (B : ModuleCat.{u} (MvPolynomial W k)) (Q : (V → ℤ) → AddSubgroup B)
    (hQ : DirectSum.IsInternal Q) (f : A.module ≅ B)
    (hf : ∀ (a : V → ℤ) (x : A.module), x ∈ A.piece a ↔ f.hom x ∈ Q a) :
    GradedPolynomialModule k e where
  module := B
  piece := Q
  internal := hQ
  constant_mem c a y hy := by
    obtain ⟨x, rfl⟩ := f.toLinearEquiv.surjective y
    rw [← f.toLinearEquiv.map_smul]
    exact (hf a _).mp (A.constant_mem c a x ((hf a x).mpr hy))
  variable_mem j a y hy := by
    obtain ⟨x, rfl⟩ := f.toLinearEquiv.surjective y
    rw [← f.toLinearEquiv.map_smul]
    exact (hf (shiftDegreeAt a (e j)) _).mp (A.variable_mem j a x ((hf a x).mpr hy))

end GradedPolynomialModule

end LPCA


