-- Prove2me | Definitions.Def_FiniteFields_Etale_ExactPullback
-- name    : FiniteFields_Etale_ExactPullback
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T11:40:42.563242+00:00
-- url     : https://prove2.me/theorems/e864a984-c995-5f9e-bab2-6f47853af9ea
-- title:
--   Exactness of the inverse image $f^{-1}$ of abelian étale sheaves
-- statement:
--   For a morphism of schemes $f\colon X\to Y$, the inverse image functor $f^{-1}$ from abelian sheaves on the small étale site of $Y$ to those of $X$ preserves finite limits and finite colimits: it is exact. Consequently it commutes with kernels and cokernels (canonical comparison isomorphisms are provided) and carries short exact sequences of sheaves to short exact sequences.
--
--   The finite-limit part rests on the fact that base change of étale schemes is representably flat, so that the left Kan extension computing the presheaf pullback is a filtered colimit; the file proves this for categories whose objects and morphisms live in different universes, a case not covered by Mathlib's `lan_preservesFiniteLimits_of_flat`.
-- source:
--   The Stacks Project, Chapter 59 (Étale Cohomology), Section 59.36 (Inverse image), and Chapter 7 (Sites and Sheaves), sections on continuous functors and morphisms of topoi.

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_Functoriality
import Definitions.Def_FiniteFields_Etale_Sites

noncomputable section

open CategoryTheory

namespace FiniteFields.Etale

open AlgebraicGeometry CategoryTheory.Limits

universe v u₁ u₂

-- Portage v4.33 : option nécessaire avec Mathlib `0df444a` (comme dans `Sites/Etale.lean`).
set_option backward.isDefEq.respectTransparency.types false

namespace MixedUniverseLan

variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
variable (E : Type u₂) [Category.{u₁} E]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise left Kan extension as a colimit, with the object and morphism
universes of the indexing categories separated.  This is the mixed-universe
form of `CategoryTheory.lanEvaluationIsoColim`. -/
private noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
        apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
        intro T
        have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
          (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
          (colimit.isColimit _) T
        have h₂ := congr_app (F.lanUnit.naturality φ) T.left
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc] at h₁ ⊢
        simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
        rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
          ι_colimMap, Functor.whiskerLeft_app]
        rfl)

variable {FE : E → E → Type*} {CE : E → Type u₁}
variable [∀ X Y, FunLike (FE X Y) (CE X) (CE Y)] [ConcreteCategory E FE]
variable [HasLimits E] [HasColimits E] [ReflectsLimits (forget E)]
variable [PreservesFilteredColimits (forget E)] [PreservesLimits (forget E)]
variable [UnivLE.{max u₁ v, u₁}]

/-- A representably flat functor whose objects and morphisms occupy different
universes still induces a finite-limit-preserving left Kan extension.  This is
the proof of mathlib's `lan_preservesFiniteLimits_of_flat` with only the
unnecessary `SmallCategory` restriction removed. -/
noncomputable instance lanPreservesFiniteLimitsOfFlat
    (F : C ⥤ D) [RepresentablyFlat F]
    [∀ G : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension G] :
    PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  letI : HasColimitsOfSize.{v, max u₁ v} E :=
    hasColimitsOfSizeOfUnivLE.{u₁, u₁, v, max u₁ v} E
  letI : PreservesFilteredColimitsOfSize.{v, max u₁ v} (forget E) :=
    preservesFilteredColimitsOfSize_of_univLE.{u₁, u₁, v, max u₁ v}
      (forget E)
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  haveI : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence F (Opposite.unop K))
  exact preservesLimitsOfShape_of_natIso
    (lanEvaluationIsoColim E F.op K).symm

end MixedUniverseLan

universe u

/-- The genuine inverse-image functor on native small-etale abelian sheaves
preserves finite limits. -/
noncomputable instance smallEtalePullback_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtalePullback f) := by
  letI : HasFiniteLimits (SmallEtaleSite Y) := by
    change HasFiniteLimits
      (CategoryTheory.MorphismProperty.Over @AlgebraicGeometry.Etale ⊤ Y)
    infer_instance
  letI : RepresentablyFlat (smallEtaleBaseChange f) :=
    flat_of_preservesFiniteLimits _
  letI : PreservesFiniteLimits
      ((smallEtaleBaseChange f).op.lan :
        ((SmallEtaleSite Y)ᵒᵖ ⥤ Ab.{u + 1}) ⥤
          ((SmallEtaleSite X)ᵒᵖ ⥤ Ab.{u + 1})) := by
    apply MixedUniverseLan.lanPreservesFiniteLimitsOfFlat
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (smallEtaleBaseChange f) Ab.{u + 1}
      (smallEtaleSiteTopology Y) (smallEtaleSiteTopology X)

/-- The genuine inverse-image functor preserves finite colimits because it is
the left adjoint in ET1F's native pullback/pushforward adjunction. -/
noncomputable instance smallEtalePullback_preservesFiniteColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (smallEtalePullback f) := by
  haveI : PreservesColimits (smallEtalePullback f) :=
    (smallEtalePullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  infer_instance



/-- The canonical kernel comparison isomorphism for native small-etale
pullback.  Its forward morphism is `kernelComparison`. -/
noncomputable def smallEtalePullback_mapKernelIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : SmallEtaleAbelianSheaf Y} (g : A ⟶ B) :
    (smallEtalePullback f).obj (kernel g) ≅
      kernel ((smallEtalePullback f).map g) :=
  PreservesKernel.iso (smallEtalePullback f) g

/-- The canonical cokernel comparison isomorphism for native small-etale
pullback.  Its inverse morphism is `cokernelComparison`. -/
noncomputable def smallEtalePullback_mapCokernelIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : SmallEtaleAbelianSheaf Y} (g : A ⟶ B) :
    (smallEtalePullback f).obj (cokernel g) ≅
      cokernel ((smallEtalePullback f).map g) :=
  PreservesCokernel.iso (smallEtalePullback f) g

/-- Native small-etale pullback transports short exact sequences. -/
theorem smallEtalePullback_map_shortExact
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex (SmallEtaleAbelianSheaf Y)} (hS : S.ShortExact) :
    (S.map (smallEtalePullback f)).ShortExact :=
  hS.map_of_exact (smallEtalePullback f)

end FiniteFields.Etale


