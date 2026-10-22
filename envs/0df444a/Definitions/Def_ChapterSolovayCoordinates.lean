-- Prove2me | Definitions.Def_ChapterSolovayCoordinates
-- name    : ChapterSolovayCoordinates
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T15:38:57.17744+00:00
-- url     : https://prove2.me/theorems/c0cda261-ec4a-42f2-982f-75bd1d2a9882
-- title:
--   Chapter SolovayCoordinates
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSolovayCoordinates.lean`): generated def bundle for ChapterSolovayCoordinates. See BookProof/ChapterSolovayCoordinates.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSolovayCoordinates.lean

import Mathlib
import Definitions.Def_PhysMehler


/-!
# Coordinate Gaussian extension of the Solovay tail

This module supplies the coordinate realization that the earlier abstract
`L²[0,1]` substrate did not expose.  The tail is an infinite sequence of real
Gaussian coordinates.  Splitting off finitely many coordinates is a measurable,
measure-preserving equivalence, and two tails can be interleaved into one.

The logical language remains deliberately small: a language is represented by a
Boolean decision procedure.  Its tensor product is conjunction on pairs, so the
combined language is decidable by construction.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BookProof.ChapterSolovayCoordinates

/-- Standard one-dimensional Gaussian law. -/
abbrev standardGaussian : Measure ℝ := gaussianReal 0 1

/-- A finite product of standard Gaussian coordinates. -/
def gaussianHead (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => standardGaussian)

instance gaussianHead_isProbability (k : ℕ) :
    IsProbabilityMeasure (gaussianHead k) := by
  unfold gaussianHead
  infer_instance

/-- The concrete coordinate tail. -/
abbrev CoordinateTail := ℕ → ℝ

/-- Its Mehler law: the countable product of standard Gaussians. -/
abbrev coordinateTailMeasure : Measure CoordinateTail := PhysHSGaussian.gammaMeasure

instance coordinateTailMeasure_isProbability :
    IsProbabilityMeasure coordinateTailMeasure := by
  exact PhysHSGaussian.gammaMeasure_isProbability







/-- Split the first `k` coordinates from an infinite sequence. -/
def tailSplitEquiv (k : ℕ) : CoordinateTail ≃ᵐ (Fin k → ℝ) × CoordinateTail :=
  (MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv k)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ ℕ => ℝ))



/-- Bijection used to interleave two sequences into one. -/
def pairIndexEquiv : Fin 2 × ℕ ≃ ℕ :=
  (Equiv.prodCongr finTwoEquiv (Equiv.refl ℕ)).trans
    Equiv.boolProdNatEquivNat

/-- Pack a pair of tails into one by interleaving coordinates.  The intermediate
`Fin 2 → ℕ → ℝ` presentation makes the product-measure argument explicit. -/
def tailTensorEquiv : CoordinateTail × CoordinateTail ≃ᵐ CoordinateTail :=
  MeasurableEquiv.finTwoArrow.symm |>.trans
    ((MeasurableEquiv.curry (Fin 2) ℕ ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) pairIndexEquiv))



/-- A finite head coupled to the coordinate Gaussian tail. -/
abbrev CoordinateSpace (N : ℕ) := (Fin N → ℝ) × CoordinateTail

/-- Product state law for an arbitrary probability distribution on the head. -/
def coordinateStateMeasure (N : ℕ) (headDist : Measure (Fin N → ℝ))
    [IsProbabilityMeasure headDist] : Measure (CoordinateSpace N) :=
  headDist.prod coordinateTailMeasure

instance coordinateStateMeasure_isProbability (N : ℕ)
    (headDist : Measure (Fin N → ℝ)) [IsProbabilityMeasure headDist] :
    IsProbabilityMeasure (coordinateStateMeasure N headDist) := by
  unfold coordinateStateMeasure
  infer_instance

/-- Split `k` Gaussian coordinates out of the tail and append them to the finite
head.  This is the coordinate-level cross-dimensional enlargement. -/
def enlargeEquiv (N k : ℕ) :
    CoordinateSpace N ≃ᵐ CoordinateSpace (N + k) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin N → ℝ))
      (tailSplitEquiv k)).trans <|
    MeasurableEquiv.prodAssoc.symm.trans <|
      MeasurableEquiv.prodCongr
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin (N + k) => ℝ)
          (finSumFinEquiv (m := N) (n := k))).symm.trans
          (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin k => ℝ))).symm
        (MeasurableEquiv.refl CoordinateTail)

/-- The enlarged head law obtained by adjoining `k` independent Gaussian
coordinates and concatenating the two finite blocks. -/
def enlargedHeadMeasure (N k : ℕ) (headDist : Measure (Fin N → ℝ)) :
    Measure (Fin (N + k) → ℝ) :=
  Measure.map
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin (N + k) => ℝ)
      (finSumFinEquiv (m := N) (n := k))).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin k => ℝ))).symm
    (headDist.prod (gaussianHead k))

instance enlargedHeadMeasure_isProbability (N k : ℕ)
    (headDist : Measure (Fin N → ℝ)) [IsProbabilityMeasure headDist] :
    IsProbabilityMeasure (enlargedHeadMeasure N k headDist) := by
  unfold enlargedHeadMeasure
  exact Measure.isProbabilityMeasure_map
    (MeasurableEquiv.measurable _).aemeasurable


/-- A decidable language is an explicit Boolean classifier. -/
structure DecidableLanguage (α : Type*) where
  decide : α → Bool

/-- Tensor product of two decidable languages. -/
def DecidableLanguage.tensor {α β : Type*}
    (L₁ : DecidableLanguage α) (L₂ : DecidableLanguage β) :
    DecidableLanguage (α × β) where
  decide x := L₁.decide x.1 && L₂.decide x.2

/-- Membership in the tensor language is decidable. -/
instance tensor_language_membership_decidable {α β : Type*}
    (L₁ : DecidableLanguage α) (L₂ : DecidableLanguage β) (x : α × β) :
    Decidable ((L₁.tensor L₂).decide x = true) := by
  infer_instance

/-- The tensor decision procedure computes conjunction of the component
procedures. -/
@[simp] theorem tensor_decide_apply {α β : Type*}
    (L₁ : DecidableLanguage α) (L₂ : DecidableLanguage β) (x : α × β) :
    (L₁.tensor L₂).decide x = (L₁.decide x.1 && L₂.decide x.2) := rfl

end BookProof.ChapterSolovayCoordinates

-- Republish attempt2 (§2.49): the earlier failure (PhysHSGaussian.gammaMeasure*
-- unknown) is stale — those decls have since been published; text unchanged.


