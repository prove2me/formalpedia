-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:11.311933+00:00
-- url     : https://prove2.me/theorems/cb0275bb-c1a7-4ee6-8f41-a011847d853b
-- title:
--   Ideal Blowup Sequence
-- statement:
--   Definitions and structural lemmas for Ideal Blowup Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
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
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure SmoothCenterBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : Type (u + 1) where
  center : X.IdealSheafData
  center_smooth : AlgebraicGeometry.Smooth (center.subschemeι ≫ p)
  center_snc : HasStrictNormalCrossingsWith p center E
  ideal_vanishes : VanishesAlong I center
  obj : Scheme.{u}
  map : obj ⟶ X
  isBlowup : Blowup.IsBlowupAlongIdealSheaf map center
  idealUp : obj.IdealSheafData
  transform_rule : Blowup.exceptionalIdeal map center * idealUp = I.comap map
namespace SmoothCenterBlowup
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}
def structureMorphism (s : SmoothCenterBlowup p I E) : s.obj ⟶ Spec (CommRingCat.of k) := s.map ≫ p
def exceptionalIdeal (s : SmoothCenterBlowup p I E) : s.obj.IdealSheafData :=
  Blowup.exceptionalIdeal s.map s.center
def boundary (s : SmoothCenterBlowup p I E) : List s.obj.IdealSheafData :=
  E.map (Blowup.strictTransform s.map s.center) ++ [s.exceptionalIdeal]
end SmoothCenterBlowup
structure IdealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap (toSequenceOfBlowups.projectionToBase 0)
  boundary_zero : boundary 0 = E.map (fun D => D.comap (toSequenceOfBlowups.projectionToBase 0))
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    AlgebraicGeometry.Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  ideal_vanishes : ∀ i, i < toSequenceOfBlowups.length →
    VanishesAlong (ideal i) (toSequenceOfBlowups.center i)
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]
namespace IdealBlowupSequence
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}
def structureMorphism (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p
def exceptionalIdeal (s : IdealBlowupSequence p I E) (i : ℕ) : (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)
def lastIdeal (s : IdealBlowupSequence p I E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length
def lastBoundary (s : IdealBlowupSequence p I E) :
    List (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.boundary s.toSequenceOfBlowups.length
end IdealBlowupSequence
end FunctorialResolution.EmbeddedResolution


