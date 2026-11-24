-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:12.587888+00:00
-- url     : https://prove2.me/theorems/13242b8f-5586-4d2a-be00-1db1b26908dd
-- title:
--   Polynomial Ring Over Global Sections
-- statement:
--   Definitions and structural lemmas for Polynomial Ring Over Global Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) :
    MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
      Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)), ⊤) :=
  MvPolynomial.eval₂Hom ((projLeft k M n).appTop).hom
    (fun i : Fin n =>
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)))
def polynomialRingOverGlobalSections (k : Type u) [Field k] (M n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
def globalSectionsToPolynomialRing (k : Type u) [Field k] (M n : ℕ) :
    Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) ⟶ polynomialRingOverGlobalSections k M n :=
  CommRingCat.ofHom
    (MvPolynomial.C :
      Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
        MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
def polynomialRingVariables (k : Type u) [Field k] (M n : ℕ) : Fin n → polynomialRingOverGlobalSections k M n :=
  fun i => MvPolynomial.X i
def specPolynomialRingToAffineSpaceSum (k : Type u) [Field k] (M n : ℕ) :
    Spec (polynomialRingOverGlobalSections k M n) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)) :=
  specToAffineSpaceExtendCoords k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n (polynomialRingVariables k M n)
def affineSpaceSumToSpecPolynomialRing (k : Type u) [Field k] (M n : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)) ⟶ Spec (polynomialRingOverGlobalSections k M n) :=
  (affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n))
end FunctorialResolution.EmbeddedResolution
end


