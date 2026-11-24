-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:50:07.223884+00:00
-- url     : https://prove2.me/theorems/866f500d-7bd1-4cf1-a426-6c1ff2dcad7d
-- title:
--   Coordinate Quotient
-- statement:
--   Definitions and structural lemmas for Coordinate Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateQuotient.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
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
namespace FunctorialResolution.EmbeddedResolution
noncomputable def etaleChartCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) : Ideal S :=
  Ideal.span (etaleChartCoord k m S '' (J : Set (Fin m)))
@[reducible] noncomputable def algebraQuotientCoordIdeal (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    Algebra (MvPolynomial (ULift.{u} (Fin (m - J.card))) k) (S ⧸ etaleChartCoordIdeal k m S J) :=
  RingHom.toAlgebra
    (((Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)).comp
      (algebraMap (CoordPolynomialRing k m) S)).comp (renameCompl k m J).toRingHom)
end FunctorialResolution.EmbeddedResolution


