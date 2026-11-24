-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationConstruction
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationConstruction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:29:16.74871+00:00
-- url     : https://prove2.me/theorems/5d0fe129-4445-4c47-8019-0145b67e5ec5
-- title:
--   Principalization Construction
-- statement:
--   Definitions and structural lemmas for Principalization Construction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/PrincipalizationConstruction.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ConstantCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_projectionToSpec_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def markedTripleOrderOne (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  MarkedIdealWithBoundary.mk k X p I 1 E
def SmoothSubschemeIdealIsRadical : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (Z : X.IdealSheafData)
    [AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)] (J : X.IdealSheafData),
    (↑Z.support : Set ↥X) ⊆ (↑J.support : Set ↥X) → J ≤ Z
namespace PrincipalizationRules
def markedBlowupSeq (B : PrincipalizationRules.{u}) (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : MarkedSequenceOfBlowups p I 1 E :=
  (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E)
end PrincipalizationRules
def CommutesWithClosedImmersion (B : PrincipalizationRules.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X' : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (p' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
    [AlgebraicGeometry.QuasiCompact p']
    (j : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion j],
    j ≫ p' = p →
    ∀ (c : ℕ), 1 ≤ c → HasEtaleCoordCodim p' j c →
    ∀ (I : X.IdealSheafData), NonzeroOnComponents I →
      NonzeroOnComponents (imageIdealSheaf j I) →
      InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) →
      InStrictNormalCrossingPosition p' ([] : List X'.IdealSheafData) →
      IsPushforwardBlowupSeq j (B.markedBlowupSeq k X p I []).toSequenceOfBlowups
        (B.markedBlowupSeq k X' p' (imageIdealSheaf j I) []).toSequenceOfBlowups
namespace PrincipalizationRules
theorem hasReducedCenters_markedBlowupSeq (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (_hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) :
    HasReducedCenters (B.markedBlowupSeq k X p I E) := by
  intro i hi J hJ
  have hsm : AlgebraicGeometry.Smooth
      (((B.markedBlowupSeq k X p I E).center i).subschemeι ≫ (B.markedBlowupSeq k X p I E).projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact (B.markedBlowupSeq k X p I E).center_smooth i hi
  exact hrad k ((B.markedBlowupSeq k X p I E).schemeAt i) ((B.markedBlowupSeq k X p I E).projectionToSpec i)
    ((B.markedBlowupSeq k X p I E).center i) J hJ
def principalizationSeq (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) : IdealBlowupSequence p I E :=
  (B.markedBlowupSeq k X p I E).toIdealBlowupSequence (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)
def principalization (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u}) :
    PrincipalizationAlgorithm.{u} :=
  fun k ik icz X p ism ift iqc I hI E hE =>
    @principalizationSeq B hrad k ik icz X p ism ift iqc I hI E hE
end PrincipalizationRules
end FunctorialResolution.EmbeddedResolution


