-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:25.630012+00:00
-- url     : https://prove2.me/theorems/c5ab97fc-f119-49f8-a03e-7b1bab43017c
-- title:
--   Marked Sequence Of Blowups
-- statement:
--   Definitions and structural lemmas for Marked Sequence Of Blowups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_one_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_vanishesAlong_iff_le

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
def withBotSuccToNat : WithBot ℕ∞ → ℕ
  | ⊥ => 0
  | (n : ℕ∞) => n.toNat + 1
def krullDimSucc (X : Scheme.{u}) : ℕ := withBotSuccToNat (topologicalKrullDim ↥X)
structure MarkedIdealWithBoundary : Type (u + 1) where
  base : Type u
  [instField : Field base]
  scheme : Scheme.{u}
  structMap : scheme ⟶ Spec (CommRingCat.of base)
  ideal : scheme.IdealSheafData
  mult : ℕ
  boundary : List scheme.IdealSheafData
attribute [instance] MarkedIdealWithBoundary.instField
abbrev MarkedIdealWithBoundary.krullDimSucc (T : MarkedIdealWithBoundary.{u}) : ℕ := EmbeddedResolution.krullDimSucc T.scheme
structure MarkedIdealWithBoundary.IsAdmissible (T : MarkedIdealWithBoundary.{u}) : Prop where
  charZero : CharZero T.base
  locallyOfFiniteType : AlgebraicGeometry.LocallyOfFiniteType T.structMap
  nonzeroOnComponents : NonzeroOnComponents T.ideal
  one_le_mult : 1 ≤ T.mult
  quasiCompact : AlgebraicGeometry.QuasiCompact T.structMap
  smooth : AlgebraicGeometry.Smooth T.structMap
  snc : InStrictNormalCrossingPosition T.structMap T.boundary
structure MarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toSequenceOfBlowups.isoZero.hom
  boundary_zero : boundary 0 = E.map (fun D => D.comap toSequenceOfBlowups.isoZero.hom)
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    AlgebraicGeometry.Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  center_order : ∀ i, i < toSequenceOfBlowups.length →
    ((toSequenceOfBlowups.center i).support : Set ↥(toSequenceOfBlowups.schemeAt i)) ⊆ orderAtLeastLocus (ideal i) m
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]
namespace MarkedSequenceOfBlowups
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
def projectionToSpec (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p
def exceptionalDivisor (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)
def lastIdeal (s : MarkedSequenceOfBlowups p I m E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length
def lastBoundary (s : MarkedSequenceOfBlowups p I m E) :
    List (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.boundary s.toSequenceOfBlowups.length
def IsResolution (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  orderAtLeastLocus s.lastIdeal m = ∅
end MarkedSequenceOfBlowups
def emptySequenceOfBlowups (X : Scheme.{u}) : SequenceOfBlowups X where
  length := 0
  tower := (CategoryTheory.Functor.const ℕᵒᵖ).obj X
  isoZero := Iso.refl X
  center := fun _ => ⊥
  isBlowup := fun i hi => absurd hi (Nat.not_lt_zero i)
def emptyMarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := emptySequenceOfBlowups X
  ideal := fun _ => I.comap (emptySequenceOfBlowups X).isoZero.hom
  boundary := fun _ => E.map (fun D => D.comap (emptySequenceOfBlowups X).isoZero.hom)
  ideal_zero := rfl
  boundary_zero := rfl
  center_smooth := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_snc := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_order := fun i hi => absurd hi (Nat.not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
abbrev MarkedIdealWithBoundary.SequenceOfBlowups (T : MarkedIdealWithBoundary.{u}) : Type (u + 1) :=
  MarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
def PrincipalizationAssignment : Type (u + 1) := ∀ T : MarkedIdealWithBoundary.{u}, T.SequenceOfBlowups
def trivialPrincipalizationAssignment : PrincipalizationAssignment.{u} :=
  fun (T : MarkedIdealWithBoundary.{u}) => emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
structure OrderReductionData : Type (u + 1) where
  maxOrderRed : PrincipalizationAssignment.{u}
  orderRed : PrincipalizationAssignment.{u}
def trivialOrderReductionData : OrderReductionData.{u} where
  maxOrderRed := trivialPrincipalizationAssignment
  orderRed := trivialPrincipalizationAssignment
section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
def HasReducedCenters (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  ∀ i, i < s.toSequenceOfBlowups.length → ∀ J : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData,
    ((s.toSequenceOfBlowups.center i).support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) ⊆
        (J.support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) →
      J ≤ s.toSequenceOfBlowups.center i
theorem markedSequenceOfBlowups_ideal_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.ideal 0 = I.comap (s.toSequenceOfBlowups.projectionToBase 0) := by
  rw [s.ideal_zero, s.toSequenceOfBlowups.projectionToBase_zero]
theorem markedSequenceOfBlowups_boundary_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.boundary 0 = E.map (fun D => D.comap (s.toSequenceOfBlowups.projectionToBase 0)) := by
  rw [s.boundary_zero, s.toSequenceOfBlowups.projectionToBase_zero]
theorem markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ (s : MarkedSequenceOfBlowups p I 1 E) (i : ℕ)
    (h : i < s.toSequenceOfBlowups.length) :
    Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) * s.ideal (i + 1) =
      (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by
  have hs := s.ideal_succ i h
  rwa [pow_one] at hs
theorem markedSequenceOfBlowups_ideal_vanishesAlong_center (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    VanishesAlong (s.ideal i) (s.toSequenceOfBlowups.center i) := by
  rw [vanishesAlong_iff_le]
  refine hmax i h (s.ideal i) ?_
  intro x hx
  have hx' := s.center_order i h hx
  rw [mem_orderAtLeastLocus_one_iff] at hx'
  exact hx'
def MarkedSequenceOfBlowups.toIdealBlowupSequence (s : MarkedSequenceOfBlowups p I 1 E) (hmax : HasReducedCenters s) :
    IdealBlowupSequence p I E where
  toSequenceOfBlowups := s.toSequenceOfBlowups
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := markedSequenceOfBlowups_ideal_zero s
  boundary_zero := markedSequenceOfBlowups_boundary_zero s
  center_smooth := s.center_smooth
  center_snc := s.center_snc
  ideal_vanishes := fun i h => markedSequenceOfBlowups_ideal_vanishesAlong_center s hmax i h
  ideal_succ := fun i h => markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ s i h
  boundary_succ := s.boundary_succ
end
end FunctorialResolution.EmbeddedResolution


