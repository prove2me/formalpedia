-- Prove2me | Definitions.Def_ProEtale_Algebra_Etale_Lib
-- name    : ProEtale_Algebra_Etale_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:40:40.848475+00:00
-- url     : https://prove2.me/theorems/ad202a24-c02d-5c6c-9112-838cddea814e
-- title:
--   Étale ring maps as a morphism property: cancellation, finite presentability, descent along filtered colimits, essential smallness
-- statement:
--   This file continues the published file on étale ring maps. It studies the class $\mathrm{Et}$ of étale ring homomorphisms, viewed as a class of morphisms in the category $\mathsf{CRing}$ of commutative rings.
--
--   Principal results:
--
--   1. Routine facts: a finitely generated subalgebra is of finite type, and an étale ring map is smooth. Evaluation functors on functor categories preserve homology. In a braided monoidal category, $- \otimes c$ preserves limits (resp. colimits) of a shape whenever $c \otimes -$ does.
--   2. Every étale ring map is a finitely presentable object of the under-category, i.e. $\mathrm{Et}$ is contained in the class of finitely presentable morphisms.
--   3. $\mathrm{Et}$ is stable under cobase change (tensor products) and is multiplicative: it contains identities and is closed under composition.
--   4. Cancellation: if $f\colon R \to S$ and $g \circ f\colon R \to T$ are étale, then $g\colon S \to T$ is étale.
--   5. **Descent to a finite stage.** $\mathrm{Et}$ "pre-ind-spreads": if $S = \operatorname{colim}_i D_i$ is a filtered colimit and $S \to T$ is étale, then there are an index $j$ and an étale map $D_j \to T'$ with $T \cong S \otimes_{D_j} T'$ (a pushout square).
--   6. For a ring $R$, the categories of étale $R$-algebras and of étale, faithfully flat $R$-algebras are essentially small. The same holds for the corresponding over-category in $\mathsf{CRing}^{\mathrm{op}}$.
--
--   These facts let one form ind-étale and pro-étale constructions, such as ind-closures and limits over all étale covers, inside the categorical framework used throughout the formalization.
--
--   **Formalization Note** Rings live in universe `u`. The class is `CommRingCat.etale` (defined in the published file as `RingHom.toMorphismProperty RingHom.Etale`). The declarations are `Subalgebra.FG.finiteType`, `RingHom.Etale.smooth`, `CommRingCat.etale_iff`, `CommRingCat.etale_le_isFinitelyPresentable`, and instances of `IsStableUnderCobaseChange`, `HasOfPrecompProperty etale`, `IsMultiplicative`, `MorphismProperty.PreIndSpreads.{u} etale` and `EssentiallySmall.{u}` for `MorphismProperty.Under etale ⊤ R`, `MorphismProperty.Under (etale ⊓ faithfullyFlat) ⊤ R` and `(etale.op ⊓ faithfullyFlat.op).Over ⊤ R`. The tensor-preservation instances are `CategoryTheory.MonoidalCategory.Limits.preservesLimitsOfShape_tensorRight_of_braided` and its colimit analogue. `PreIndSpreads` is the Mathlib class described in item 5.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/Etale.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Algebra_Etale of the same module.

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Algebra_Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Etale ind-spreads
-/

universe w u


open TensorProduct CategoryTheory Limits

@[reducible]
def Subalgebra.FG.finiteType {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {A : Subalgebra R S} (h : A.FG) :
    Algebra.FiniteType R A :=
  A.fg_iff_finiteType.mp h

lemma RingHom.Etale.smooth {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Etale) :
    f.Smooth := by
  rw [RingHom.etale_iff_formallyUnramified_and_smooth] at hf
  exact hf.2

instance inst_AlgebraEtale_L56 {J : Type*} [Category J] {C : Type*} [Category C] [Preadditive C]
    [HasLimitsOfShape WalkingParallelPair C] [HasColimitsOfShape WalkingParallelPair C] (j : J) :
    ((evaluation J C).obj j).PreservesHomology where

instance CategoryTheory.MonoidalCategory.Limits.preservesLimitsOfShape_tensorRight_of_braided
    {J : Type*} [Category J] {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] (c : C)
    [PreservesLimitsOfShape J (tensorLeft c)] :
    PreservesLimitsOfShape J (MonoidalCategory.tensorRight c) where

instance CategoryTheory.MonoidalCategory.Limits.preservesColimitsOfShape_tensorRight_of_braided
    {J : Type*} [Category J] {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] (c : C)
    [PreservesColimitsOfShape J (tensorLeft c)] :
    PreservesColimitsOfShape J (MonoidalCategory.tensorRight c) where


namespace CommRingCat


@[simp]
lemma etale_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    etale f ↔ f.hom.Etale := .rfl

lemma etale_le_isFinitelyPresentable :
    etale.{u} ≤ MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} :=
  fun _ _ _ hf ↦ CommRingCat.isFinitelyPresentable_under _ _ hf.2

instance inst_AlgebraEtale_L99 : etale.IsStableUnderCobaseChange := by
  rw [etale, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Etale.isStableUnderBaseChange

instance inst_AlgebraEtale_L103 : etale.HasOfPrecompProperty etale where
  of_precomp f g hf hfg := RingHom.Etale.of_comp hf (by rwa [← CommRingCat.hom_comp])

instance inst_AlgebraEtale_L106 : etale.IsMultiplicative where
  id_mem R := .of_bijective Function.bijective_id
  comp_mem {R S T} f g hf hg := by
    apply RingHom.Etale.stableUnderComposition
    · exact hf
    · exact hg

variable {J : Type*} [Category J] (D : J ⥤ CommRingCat.{u})

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance inst_AlgebraEtale_L115 : MorphismProperty.PreIndSpreads.{u} etale.{u} := by
  refine .of_isInitial CommRingCat.isInitial fun R S f hf ↦ ?_
  algebraize [f.hom]
  have hf_eq : f = ofHom (algebraMap R S) := rfl
  have : Algebra.Etale R S := hf
  obtain ⟨R₀, S₀, _, _, hfg, h, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ R S
  let g : S₀ →+* S := e.symm.toRingHom.comp <| Algebra.TensorProduct.includeRight.toRingHom
  algebraize [g]
  have : IsScalarTower R₀ S₀ ↑S := .of_algebraMap_eq fun x ↦ by
    have := (e.symm.toAlgHom.commutes x.val).symm
    simp only [RingHom.algebraMap_toAlgebra, g, RingHom.comp_apply] at this ⊢
    refine this.trans (congrArg e.symm ?_)
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul x
  refine ⟨.of R₀, .of S₀, CommRingCat.ofHom (algebraMap R₀ R),
      CommRingCat.ofHom g, CommRingCat.ofHom (algebraMap R₀ S₀), ?_, ?_, ?_⟩
  · apply CommRingCat.isFinitelyPresentable_under
    dsimp
    have : isInitial.to (of R₀) = ofHom ((algebraMap ℤ R₀).comp ULift.ringEquiv.toRingHom) :=
      isInitial.hom_ext _ _
    rw [this]
    apply RingHom.FinitePresentation.comp
    · rw [RingHom.finitePresentation_algebraMap, ← Algebra.FinitePresentation.of_finiteType]
      exact hfg.finiteType
    · exact .of_bijective ULift.ringEquiv.bijective
  · simpa [RingHom.etale_algebraMap]
  · rw [hf_eq, ← RingHom.algebraMap_toAlgebra g, isPushout_iff_isPushout]
    exact Algebra.IsPushout.of_equiv (S' := ↑R ⊗[↥R₀] S₀) e.symm rfl

instance inst_AlgebraEtale_L144 (R : CommRingCat.{u}) : EssentiallySmall.{u} (MorphismProperty.Under etale ⊤ R) :=
  essentiallySmall_of_le (fun _ _ _ hf ↦ .of_finitePresentation hf.2) _

instance inst_AlgebraEtale_L147 (R : CommRingCat.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Under (etale ⊓ faithfullyFlat) ⊤ R) :=
  essentiallySmall_of_le (fun _ _ _ hf ↦ .of_finitePresentation hf.1.2) _

instance inst_AlgebraEtale_L151 (R : CommRingCat.{u}ᵒᵖ) :
    EssentiallySmall.{u} ((etale.op ⊓ faithfullyFlat.op).Over ⊤ R) := by
  let e : ((etale.op ⊓ faithfullyFlat.op).Over ⊤ R) ≌
      (MorphismProperty.Under (etale ⊓ faithfullyFlat) ⊤ R.unop)ᵒᵖ :=
    .rightOp <| .symm <| MorphismProperty.Under.equivOpOverOp _ _ _
  rw [essentiallySmall_congr e]
  infer_instance

end CommRingCat


