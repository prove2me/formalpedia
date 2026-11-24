-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T17:34:32.767442+00:00
-- url     : https://prove2.me/theorems/7cddbd7f-af40-44c9-ade8-56a742674c63
-- title:
--   Monomial Part Along Divisor
-- statement:
--   Definitions and structural lemmas for Monomial Part Along Divisor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialPartAlongDivisor.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_finite_isIrreducibleComponentOfSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
variable {k : Type u} [Field k]
@[reducible]
def IsEtaleLocallyCoordinateDivisor (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
    restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}
def orderAlongComponent (I : X.IdealSheafData) {C : Set X} (hC : IsIrreducible C) : ℕ :=
  (orderAt I hC.genericPoint).toNat
def componentPowerIdeal (I D : X.IdealSheafData) (C : Set X) : X.IdealSheafData :=
  letI : Decidable (IsIrreducibleComponentOfSupport D C) := Classical.propDecidable _
  if h : IsIrreducibleComponentOfSupport D C then
    Scheme.IdealSheafData.vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
      orderAlongComponent I h.isIrreducible
  else ⊤
def supportComponentsFinset [TopologicalSpace.NoetherianSpace ↥X] (D : X.IdealSheafData) :
    Finset (Set X) :=
  (finite_isIrreducibleComponentOfSupport D).toFinset
def monomialPartAlongDivisor [TopologicalSpace.NoetherianSpace ↥X] (I D : X.IdealSheafData) :
    X.IdealSheafData :=
  (supportComponentsFinset D).inf (fun C => componentPowerIdeal I D C)
def monomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X] (E : List X.IdealSheafData)
    (I : X.IdealSheafData) : X.IdealSheafData :=
  (E.map (fun D => monomialPartAlongDivisor I D)).prod
def nonMonomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) : X.IdealSheafData :=
  idealSheafColon I (monomialFactorIdeal E I)
end FunctorialResolution.EmbeddedResolution
end


