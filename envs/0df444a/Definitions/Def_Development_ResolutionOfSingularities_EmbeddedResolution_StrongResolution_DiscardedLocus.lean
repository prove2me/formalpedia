-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_DiscardedLocus
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_DiscardedLocus
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:09.257274+00:00
-- url     : https://prove2.me/theorems/7db4b0ff-7327-4c15-8909-bc73f8d49751
-- title:
--   Discarded Locus
-- statement:
--   Definitions and structural lemmas for Discarded Locus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/DiscardedLocus.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def coprodSwapAssocHom (A F G : Scheme.{u}) : (A ⨿ (F ⨿ G)) ⟶ ((A ⨿ G) ⨿ F) :=
  coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc coprod.inr (coprod.inr ≫ coprod.inl))
def coprodSwapAssocInv (A F G : Scheme.{u}) : ((A ⨿ G) ⨿ F) ⟶ (A ⨿ (F ⨿ G)) :=
  coprod.desc (coprod.desc coprod.inl (coprod.inr ≫ coprod.inr)) (coprod.inl ≫ coprod.inr)
namespace AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)
def discardedLocusOpens (i : ℕ) (h : IsOpen (S.discardedLocus i)) : (S.strictTransform i).Opens :=
  ⟨S.discardedLocus i, h⟩
end AffineSpacePrincipalizationData
def EmbeddedPrincipalizationDiscardedLocusIsOpen (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (i : ℕ),
    i < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength →
      IsOpen ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedLocus i)
def EmbeddedPrincipalizationAmbientIsNoetherian (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (i : ℕ),
    i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength →
      AlgebraicGeometry.IsNoetherian ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)
end FunctorialResolution.EmbeddedResolution
end


