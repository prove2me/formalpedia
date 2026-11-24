-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:15.812701+00:00
-- url     : https://prove2.me/theorems/5901d760-dac4-4ada-831a-10b27b27a739
-- title:
--   Strict Normal Crossings
-- statement:
--   Definitions and structural lemmas for Strict Normal Crossings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean

import Mathlib
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
abbrev restrictIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) :
    U.toScheme.IdealSheafData :=
  I.comap U.ι
abbrev zeroLocus {X : Scheme.{u}} (I : X.IdealSheafData) : TopologicalSpace.Closeds X :=
  I.support
def VanishesAlong {X : Scheme.{u}} (I J : X.IdealSheafData) : Prop := I ≤ J
def NonzeroOnComponents {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (I.support : Set ↥X)
def IsSmoothDivisor {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) : Prop :=
  Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ AlgebraicGeometry.Smooth (D.subschemeι ≫ p)
abbrev affineSpaceFin (k : Type u) [Field k] (m : ℕ) : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))
abbrev affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) :
    affineSpaceFin k m ⟶ Spec (CommRingCat.of k) :=
  (affineSpaceFin k m ↘ Spec (CommRingCat.of k))
structure EtaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (m : ℕ) : Type u where
  map : U.toScheme ⟶ affineSpaceFin k m
  comp_struct : map ≫ affineSpaceFinToSpec k m = U.ι ≫ p
  isEtale : AlgebraicGeometry.Etale map
def coordSubspaceIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (affineSpaceFin k m).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span
      ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
        (S : Set (Fin m))))
def EtaleChart.coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) : U.toScheme.IdealSheafData :=
  (coordSubspaceIdeal k m S).comap c.map
def InStrictNormalCrossingPositionAt {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
    (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
    (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
    (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t})
def InStrictNormalCrossingPosition {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) : Prop :=
  (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, InStrictNormalCrossingPositionAt p E x
def HasStrictNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support,
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
      (S : Finset (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      restrictIdeal Z U = c.coordIdeal S
end FunctorialResolution.EmbeddedResolution


