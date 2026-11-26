-- Prove2me | Definitions.Def_ProEtale_Algebra_FaithfullyFlat
-- name    : ProEtale_Algebra_FaithfullyFlat
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:11:23.172515+00:00
-- url     : https://prove2.me/theorems/2066f608-e995-4ed3-9338-f82394307e74
-- title:
--   Flat modules and algebras as object properties, stable under filtered colimits
-- statement:
--   The object properties of flat $R$-modules (`ModuleCat.flat`) and flat commutative $R$-algebras (`CommAlgCat.flat`), with the fact that a filtered colimit of flat modules, respectively algebras, is flat, so that each property equals its own ind-completion.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/FaithfullyFlat.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Ind-(faithfully flat) is faithfully flat

-/

universe w v u

open CategoryTheory Limits TensorProduct

namespace ModuleCat

/-- The object property of flat modules. -/
def flat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.Flat R M

variable (R : Type u) [CommRing R]


variable {R} in
open MonoidalCategory in
lemma flat_of_colimitPresentation {M : ModuleCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J M)
    (h : ∀ j, Module.Flat R (pres.diag.obj j)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]
  intro C hC
  let S : ShortComplex (J ⥤ ModuleCat.{u} R) :=
    { X₁ := pres.diag ⋙ tensorRight C.X₁
      X₂ := pres.diag ⋙ tensorRight C.X₂
      X₃ := pres.diag ⋙ tensorRight C.X₃
      f := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.f
      g := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.g
      zero := by simp [← CategoryTheory.Functor.whiskerLeft_comp, ← Functor.map_comp, C.zero] }
  apply colim.exact_mapShortComplex (S := S)
      (hc₁ := isColimitOfPreserves _ pres.isColimit)
      (hc₂ := isColimitOfPreserves _ pres.isColimit)
      (hc₃ := isColimitOfPreserves _ pres.isColimit)
  · rw [CategoryTheory.ShortComplex.exact_iff_evaluation]
    intro j
    exact Module.Flat.lTensor_shortComplex_exact (pres.diag.obj j) C hC
  · simp [S, whisker_exchange]
  · simp [S, whisker_exchange]

open MonoidalCategory in
@[simp]
lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  refine le_antisymm (fun M ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  exact flat_of_colimitPresentation pres h

end ModuleCat

namespace CommAlgCat

variable {R : Type u} [CommRing R]

/-- The object property of flat `R`-algebras. -/
def flat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.flat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)

@[simp]
lemma flat_iff {S : CommAlgCat R} : flat R S ↔ Module.Flat R S := .rfl

lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  refine le_antisymm ?_ (ObjectProperty.le_ind _)
  rw [flat]
  refine le_trans (ObjectProperty.ind_inverseImage_le _ _) ?_
  rw [ModuleCat.ind_flat]


end CommAlgCat


namespace Module

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {S : Type u} [CommRing S]

namespace Flat


/-- Flat is equivalent to ind-flat. -/
theorem iff_ind_flat [Algebra R S] : Module.Flat R S ↔
    ObjectProperty.ind.{u} (CommAlgCat.flat R) (.of R S) := by
  rw [CommAlgCat.ind_flat]
  rfl

end Flat


end Module


