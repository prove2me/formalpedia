-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T12:59:41.141977+00:00
-- url     : https://prove2.me/theorems/2f1c0a9e-d867-42bf-9d69-ab17eb6f92f3
-- title:
--   Chart Ring
-- statement:
--   Definitions and structural lemmas for Chart Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartRing.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
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
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def affineSpaceGlobalSectionsHom (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(affineSpaceFin k m, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
def EtaleChart.coord (c : EtaleChart p U m) (j : Fin m) : Γ(X, U) :=
  U.topIso.hom.hom
    (c.map.appTop.hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))))
def EtaleChart.coordRingHom (c : EtaleChart p U m) :
    MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, U) :=
  (U.topIso.hom.hom.comp c.map.appTop.hom).comp (affineSpaceGlobalSectionsHom k m)
@[reducible] def EtaleChart.algebra (c : EtaleChart p U m) :
    Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
  c.coordRingHom.toAlgebra
end FunctorialResolution.EmbeddedResolution


