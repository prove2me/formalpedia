-- Prove2me | Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
-- name    : ProEtale_Algebra_FaithfullyFlat_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:15.58729+00:00
-- url     : https://prove2.me/theorems/9c897bc2-99b0-4bd8-92a9-c296f98a1bac
-- title:
--   Filtered colimits of faithfully flat algebras are faithfully flat; ind-(faithfully flat) ring maps are faithfully flat
-- statement:
--   This file continues the published file of the same name (`Algebra/FaithfullyFlat`). Let $R$ be a commutative ring. It defines:
--
--   - the property of $R$-modules being faithfully flat, and the induced property of commutative $R$-algebras (faithful flatness of the underlying module);
--   - the classes of ring maps $\varphi : R \to S$ with surjective $\operatorname{Spec}(\varphi) : \operatorname{Spec} S \to \operatorname{Spec} R$, and of faithfully flat ring maps, as morphism properties of the category of commutative rings.
--
--   Principal results:
--
--   1. If a commutative $R$-algebra $S$ is a filtered colimit $S = \operatorname{colim}_j S_j$ of $R$-algebras that are flat over $R$, then $S$ is flat over $R$.
--   2. If each $S_j$ is faithfully flat over $R$, then $S$ is faithfully flat over $R$.
--   3. Consequently, the ind-closure of the class of faithfully flat $R$-algebras is the class itself: $\operatorname{ind}(\text{faithfully flat}) = \text{faithfully flat}$.
--   4. A ring map is faithfully flat if and only if it is flat and induces a surjection on spectra: $\text{faithfully flat} = \text{flat} \cap \text{surjective on } \operatorname{Spec}$.
--   5. Faithfully flat ring maps are stable under cobase change; maps surjective on spectra and faithfully flat maps both contain identities and are closed under composition.
--   6. For ring maps, $\operatorname{ind}(\text{faithfully flat}) = \text{faithfully flat}$: a filtered colimit of faithfully flat ring maps out of a fixed ring $R$ is faithfully flat.
--
--   These facts show that ind-étale faithfully flat maps, and similar ind-constructions, keep faithful flatness. That is needed for coverings in the pro-étale topology.
--
--   **Formalization Note** Main declarations: `ModuleCat.faithfullyFlat`, `CommAlgCat.faithfullyFlat`, `CommAlgCat.flat_of_colimitPresentation`, `CommAlgCat.faithfullyFlat_of_colimitPresentation`, `CommAlgCat.ind_faithfullyFlat`, `CommRingCat.surjectiveSpec`, `CommRingCat.faithfullyFlat`, `CommRingCat.faithfullyFlat_eq`, `CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat`. Filtered colimits are given by a `ColimitPresentation` indexed by a small filtered category, and ind-closures are taken in the same universe `u` as the rings (`ind.{u}`). `CommAlgCat.faithfullyFlat` is defined for algebras in an arbitrary universe `w`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/FaithfullyFlat.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Algebra_FaithfullyFlat of the same module.

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHomProperties
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Ind-(faithfully flat) is faithfully flat

-/

universe w v u

open CategoryTheory Limits TensorProduct

namespace ModuleCat


variable (R : Type u) [CommRing R]


/-- The object property of faithfully flat modules. -/
def faithfullyFlat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.FaithfullyFlat R M


end ModuleCat

namespace CommAlgCat

variable {R : Type u} [CommRing R]


/-- A `CommAlgCat`-level filtered colimit of flat `R`-algebras is flat over `R`. -/
lemma flat_of_colimitPresentation {S : CommAlgCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J S)
    (h : ∀ j, Module.Flat R (pres.diag.obj j)) :
    Module.Flat R S := by
  rw [← flat_iff, flat, ObjectProperty.inverseImage, ← ModuleCat.ind_flat R,
    ← ObjectProperty.prop_inverseImage_iff (ModuleCat.flat.{u} R).ind]
  refine ObjectProperty.ind_inverseImage_le _ _ _ ⟨J, ‹_›, ‹_›, pres, fun j ↦ ?_⟩
  exact h j

/-- The object property of faithfully-flat `R`-algebras. -/
def faithfullyFlat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.faithfullyFlat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)


lemma faithfullyFlat_of_colimitPresentation {S : CommAlgCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J S)
    (h : ∀ j, Module.FaithfullyFlat R (pres.diag.obj j)) :
    Module.FaithfullyFlat R S := by
  have : Module.Flat R S := flat_of_colimitPresentation pres fun j ↦ (h j).1
  refine Module.FaithfullyFlat.of_nontrivial_tensor_quotient fun m hm ↦ ?_
  let qpres : ColimitPresentation J (CommAlgCat.of R <| (R ⧸ m) ⊗[R] S) :=
    pres.map <| MonoidalCategory.tensorLeft (CommAlgCat.of R (R ⧸ m))
  have (j : J) : Nontrivial ((qpres.diag ⋙ forget₂ (CommAlgCat R) CommRingCat).obj j) := by
    simp only [ColimitPresentation.map_diag, Functor.comp_obj,
      MonoidalCategory.curriedTensor_obj_obj, forget₂_commRingCat_obj, coe_tensorObj,
      Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left, qpres]
    infer_instance
  change Nontrivial ((forget₂ _ CommRingCat).mapCocone qpres.cocone).pt
  exact CommRingCat.FilteredColimits.nontrivial (isColimitOfPreserves _ qpres.isColimit)

lemma ind_faithfullyFlat :
    ObjectProperty.ind.{u} (faithfullyFlat.{u} R) = faithfullyFlat.{u} R := by
  refine le_antisymm (fun S ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  exact faithfullyFlat_of_colimitPresentation pres h

end CommAlgCat

namespace CommRingCat

/-- The morphism property of ring maps inducing surjective maps on prime spectra. -/
def surjectiveSpec : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty fun f ↦ Function.Surjective (PrimeSpectrum.comap f)

@[simp]
lemma surjectiveSpec_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    surjectiveSpec f ↔ Function.Surjective (PrimeSpectrum.comap f.hom) := .rfl

/-- The morphism property of faithfully flat ring maps. -/
def faithfullyFlat : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.FaithfullyFlat

@[simp]
lemma faithfullyFlat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    faithfullyFlat f ↔ f.hom.FaithfullyFlat := .rfl

lemma faithfullyFlat_eq : faithfullyFlat = flat ⊓ surjectiveSpec := by
  ext X Y f
  simp only [faithfullyFlat_iff, RingHom.FaithfullyFlat.eq_and]
  rfl

instance inst_AlgebraFaithfullyFlat_L167 : faithfullyFlat.IsStableUnderCobaseChange := by
  rw [faithfullyFlat, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.FaithfullyFlat.isStableUnderBaseChange

instance inst_AlgebraFaithfullyFlat_L171 : surjectiveSpec.IsMultiplicative where
  id_mem R := Function.surjective_id
  comp_mem _ _ h1 h2 := by simpa using h1.comp h2

instance inst_AlgebraFaithfullyFlat_L175 : faithfullyFlat.IsMultiplicative where
  id_mem _ := .of_bijective Function.bijective_id
  comp_mem _ _ := RingHom.FaithfullyFlat.stableUnderComposition _ _


lemma ind_faithfullyFlat_eq_faithfullyFlat :
    MorphismProperty.ind.{u} faithfullyFlat.{u} = faithfullyFlat.{u} := by
  refine le_antisymm (fun {R S} f hf ↦ ?_) (MorphismProperty.le_ind _)
  rw [MorphismProperty.ind_iff_ind_underMk] at hf
  algebraize [f.hom]
  suffices h : ObjectProperty.ind.{u} (CommAlgCat.faithfullyFlat.{u} R) (.of R S) by
    rwa [CommAlgCat.ind_faithfullyFlat] at h
  exact ObjectProperty.ind_inverseImage_le (F := (commAlgCatEquivUnder R).inverse)
    (P := CommAlgCat.faithfullyFlat.{u} R) (Under.mk f) hf

end CommRingCat


