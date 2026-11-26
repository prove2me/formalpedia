-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_CohomologyComparison
-- name    : ProEtale_Topology_Comparison_CohomologyComparison
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:22:34.666315+00:00
-- url     : https://prove2.me/theorems/635c7aef-1002-4f9c-a269-eb4e2da4a805
-- title:
--   Exactness of pullback from étale to pro-étale abelian sheaves
-- statement:
--   Instances recording that $\nu^* : \operatorname{Ab}(X_{\text{ét}}) \to \operatorname{Ab}(X_{\text{proét}})$ preserves finite limits and finite colimits and is additive, and that abelian étale sheaves form a Grothendieck abelian category; these are what make the induced maps on $\operatorname{Ext}$ groups meaningful.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Section 5.1. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/CohomologyComparison.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_WContractible
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Topology_Comparison_Affine
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Comparison of étale and pro-étale cohomology

Let `S` be a scheme and `ν^* : Sheaf S.smallEtaleTopology Ab ⥤ Sheaf (ProEt.topology S) Ab`
the pullback functor along the inclusion of the small étale site into the pro-étale site.
We show:

- `AlgebraicGeometry.Scheme.ProEt.mapExt_bijective_sheafPullback`: `ν^*` induces bijections
  on all `Ext`-groups of abelian sheaves ([BS15, Corollary 5.1.8] in the abelian setting).
- `AlgebraicGeometry.Scheme.ProEt.sheafHAddEquiv`: for an abelian sheaf `K` on the small
  étale site, `H^n(S_proét, ν^*K) ≃+ H^n(S_ét, K)` ([BS15, Corollary 5.1.6]).

The proof applies `Functor.mapExt_bijective_of_exists_epi`: the functor `ν^*` is exact and
fully faithful, and every abelian sheaf on the small étale site admits an epimorphism from
a coproduct of free abelian sheaves on *affine* étale `S`-schemes. By the key acyclicity
result `ProEt.subsingleton_ext_sheafPullback_injective`, the pullbacks of injective sheaves
have no higher `Ext`s from pullbacks of such free sheaves; a dimension shifting argument
(`CategoryTheory.subsingleton_ext_coproduct`) extends this vanishing to the coproducts.
-/

universe w t v u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory


section LanEvaluation

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
  {E : Type u₁} [Category.{v₁} E]

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved. -/
noncomputable def Functor.lanEvaluationIsoColim' (F : C ⥤ D) (X : D)
    [∀ G : C ⥤ E, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ E) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

end LanEvaluation

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})


instance : HasFilteredColimitsOfSize.{u, u + 1} Ab.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

instance : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}

/-- The category of abelian sheaves on the small étale site of `S : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. -/
instance : IsGrothendieckAbelian.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

namespace ProEt

/-- The left Kan extension of abelian presheaves along the inclusion of the étale site
into the pro-étale site is exact, since the inclusion is representably flat. -/
noncomputable instance preservesFiniteLimits_lan :
    PreservesFiniteLimits ((toProEtale S).op.lan :
      (S.Etaleᵒᵖ ⥤ Ab.{u + 1}) ⥤ S.ProEtᵒᵖ ⥤ Ab.{u + 1}) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro K
  haveI : IsFiltered (CostructuredArrow (toProEtale S).op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (toProEtale S) (unop K))
  exact preservesLimitsOfShape_of_natIso
    (Functor.lanEvaluationIsoColim' (toProEtale S).op K).symm

instance : PreservesFiniteLimits (ProEt.sheafPullback S Ab.{u + 1}) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits (toProEtale S) Ab.{u + 1}
    (smallEtaleTopology S) (ProEt.topology S)

instance : PreservesFiniteColimits (ProEt.sheafPullback S Ab.{u + 1}) :=
  haveI : PreservesColimitsOfSize.{0, 0} (ProEt.sheafPullback S Ab.{u + 1}) :=
    (ProEt.sheafAdjunction S Ab.{u + 1}).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

instance : (ProEt.sheafPullback S Ab.{u + 1}).Additive := by
  haveI : (ProEt.sheafPullback S Ab.{u + 1}).IsLeftAdjoint :=
    (ProEt.sheafAdjunction S Ab.{u + 1}).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _


end ProEt

end AlgebraicGeometry.Scheme


