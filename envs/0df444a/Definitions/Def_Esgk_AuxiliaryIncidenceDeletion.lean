-- Prove2me | Definitions.Def_Esgk_AuxiliaryIncidenceDeletion
-- name    : Esgk_AuxiliaryIncidenceDeletion
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:56:43.757984+00:00
-- url     : https://prove2.me/theorems/b43524cc-69fe-44a4-8faf-787358664097
-- title:
--   Encoded auxiliary distance incidences
-- statement:
--   This encodes ordered pairs of planar points, equal-distance incidences and the finite sets of distance partners for a fixed curve label. It also defines propositions asserting a $2d$ bound on such partner sets and exclusion of the associated distance circle from the supporting curve.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_CirclePolynomialRestriction
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw


noncomputable def preparedSecondCurvePolynomial {d : ℕ}
    (X : PreparedBipartiteInput d) : PachDeZeeuw.Algebraic.PlanePoly :=
  Classical.choose X.hC₂


theorem preparedSecondCurvePolynomial_irreducible {d : ℕ}
    (X : PreparedBipartiteInput d) :
    Irreducible (preparedSecondCurvePolynomial X) :=
  (Classical.choose_spec X.hC₂).2.2.1


noncomputable def encodedAuxPoint (pq : Point2 × Point2) : Point4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm fun
    | 0 => pq.1 0
    | 1 => pq.1 1
    | 2 => pq.2 0
    | _ => pq.2 1

 
noncomputable def decodedAuxFirst (z : Point4) : Point2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun
    | 0 => z 0
    | _ => z 1

 
noncomputable def decodedAuxSecond (z : Point4) : Point2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun
    | 0 => z 2
    | _ => z 3

@[simp]
theorem decodedAuxFirst_encodedAuxPoint (pq : Point2 × Point2) :
    decodedAuxFirst (encodedAuxPoint pq) = pq.1 := by
  ext i
  fin_cases i <;> simp [decodedAuxFirst, encodedAuxPoint]

@[simp]
theorem decodedAuxSecond_encodedAuxPoint (pq : Point2 × Point2) :
    decodedAuxSecond (encodedAuxPoint pq) = pq.2 := by
  ext i
  fin_cases i <;> simp [decodedAuxSecond, encodedAuxPoint]


theorem exists_encodedAuxPoint_eq_of_mem_auxPointSet {d : ℕ}
    (X : PreparedBipartiteInput d) {z : Point4} (hz : z ∈ auxPointSet X) :
    ∃ pq ∈ X.P₂.product X.P₂, encodedAuxPoint pq = z := by
  classical
  rcases Finset.mem_image.mp hz with ⟨pq, hpq, hpqz⟩
  exact ⟨pq, hpq, hpqz⟩

 
noncomputable def auxPointPreimage {d : ℕ} (X : PreparedBipartiteInput d)
    (z : {z // z ∈ auxPointSet X}) : Point2 × Point2 :=
  Classical.choose
    (exists_encodedAuxPoint_eq_of_mem_auxPointSet X z.property)

theorem auxPointPreimage_mem {d : ℕ} (X : PreparedBipartiteInput d)
    (z : {z // z ∈ auxPointSet X}) :
    auxPointPreimage X z ∈ X.P₂.product X.P₂ :=
  (Classical.choose_spec
    (exists_encodedAuxPoint_eq_of_mem_auxPointSet X z.property)).1

theorem encodedAuxPoint_auxPointPreimage {d : ℕ}
    (X : PreparedBipartiteInput d) (z : {z // z ∈ auxPointSet X}) :
    encodedAuxPoint (auxPointPreimage X z) = z :=
  (Classical.choose_spec
    (exists_encodedAuxPoint_eq_of_mem_auxPointSet X z.property)).2

theorem bundle_Esgk_AuxiliaryIncidenceDeletion_encodedAuxPoint_sqDistance_of_mem_auxCurve {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    (pq : Point2 × Point2)
    (hmem : encodedAuxPoint pq ∈ auxCurve X ij.1 ij.2) :
    dist (ij.1 : Point2) pq.1 ^ 2 =
      dist (ij.2 : Point2) pq.2 ^ 2 := by
  have hsq := hmem.2.2
  change
    dist (ij.1 : Point2) (decodedAuxFirst (encodedAuxPoint pq)) ^ 2 =
      dist (ij.2 : Point2) (decodedAuxSecond (encodedAuxPoint pq)) ^ 2 at hsq
  simpa using hsq

 
noncomputable def auxIncidencesWithCurveLabel {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁) :
    Finset (Point4 × (X.P₁ × X.P₁)) := by
  classical
  exact (auxIncidences X).filter fun incidence => incidence.2 = ij


noncomputable def auxDistancePairsWithCurveLabel {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁) :
    Finset (Point2 × Point2) := by
  classical
  exact (X.P₂.product X.P₂).filter fun pq =>
    dist (ij.1 : Point2) pq.1 = dist (ij.2 : Point2) pq.2

 
noncomputable def auxDistancePartners {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁) (p : Point2) :
    Finset Point2 := by
  classical
  exact X.P₂.filter fun q =>
    dist (ij.1 : Point2) p = dist (ij.2 : Point2) q


def SharpAuxiliaryCircleFiberBoundStatement : Prop :=
  ∀ d : ℕ, ∀ X : PreparedBipartiteInput d,
    ∀ ij : X.P₁ × X.P₁, ∀ p ∈ X.P₂,
      (auxDistancePartners X ij p).card ≤ 2 * d


def AuxiliaryDistanceCircleNoncontainmentStatement : Prop :=
  ∀ d : ℕ, ∀ X : PreparedBipartiteInput d,
    ∀ ij : X.P₁ × X.P₁, ∀ p ∈ X.P₂,
      ¬ Metric.sphere (ij.2 : Point2) (dist (ij.1 : Point2) p) ⊆
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (preparedSecondCurvePolynomial X)


theorem bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_point_mem_auxPointSet {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    {incidence : Point4 × (X.P₁ × X.P₁)}
    (hincidence : incidence ∈ auxIncidencesWithCurveLabel X ij) :
    incidence.1 ∈ auxPointSet X := by
  classical
  have haux := (Finset.mem_filter.mp hincidence).1
  exact (Finset.mem_product.mp (Finset.mem_filter.mp haux).1).1

theorem bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_label_eq {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    {incidence : Point4 × (X.P₁ × X.P₁)}
    (hincidence : incidence ∈ auxIncidencesWithCurveLabel X ij) :
    incidence.2 = ij := by
  classical
  exact (Finset.mem_filter.mp hincidence).2

theorem bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_point_mem_auxCurve {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    {incidence : Point4 × (X.P₁ × X.P₁)}
    (hincidence : incidence ∈ auxIncidencesWithCurveLabel X ij) :
    incidence.1 ∈ auxCurve X ij.1 ij.2 := by
  classical
  have haux := (Finset.mem_filter.mp hincidence).1
  have hcurve := (Finset.mem_filter.mp haux).2
  rw [bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_label_eq X ij hincidence] at hcurve
  exact hcurve

 
def bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePoint {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    (incidence :
      {incidence // incidence ∈ auxIncidencesWithCurveLabel X ij}) :
    {z // z ∈ auxPointSet X} :=
  ⟨incidence.1.1,
    bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_point_mem_auxPointSet X ij incidence.property⟩


noncomputable def bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    (incidence :
      {incidence // incidence ∈ auxIncidencesWithCurveLabel X ij}) :
    Point2 × Point2 :=
  auxPointPreimage X (bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePoint X ij incidence)

theorem bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair_mem_distancePairs {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    (incidence :
      {incidence // incidence ∈ auxIncidencesWithCurveLabel X ij}) :
    bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair X ij incidence ∈
      auxDistancePairsWithCurveLabel X ij := by
  classical
  let z := bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePoint X ij incidence
  let pq := bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair X ij incidence
  have hpq : pq ∈ X.P₂.product X.P₂ := by
    exact auxPointPreimage_mem X z
  have hencoded : encodedAuxPoint pq = incidence.1.1 := by
    exact encodedAuxPoint_auxPointPreimage X z
  have hcurve : incidence.1.1 ∈ auxCurve X ij.1 ij.2 :=
    bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_point_mem_auxCurve X ij incidence.property
  rw [← hencoded] at hcurve
  have hsq := bundle_Esgk_AuxiliaryIncidenceDeletion_encodedAuxPoint_sqDistance_of_mem_auxCurve X ij pq hcurve
  have hnonneg₁ : 0 ≤ dist (ij.1 : Point2) pq.1 := dist_nonneg
  have hnonneg₂ : 0 ≤ dist (ij.2 : Point2) pq.2 := dist_nonneg
  have hdist :
      dist (ij.1 : Point2) pq.1 = dist (ij.2 : Point2) pq.2 := by
    nlinarith
  exact Finset.mem_filter.mpr ⟨hpq, hdist⟩

 
noncomputable def bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidenceToDistancePair {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁) :
    {incidence // incidence ∈ auxIncidencesWithCurveLabel X ij} →
      {pq // pq ∈ auxDistancePairsWithCurveLabel X ij} :=
  fun incidence =>
    ⟨bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair X ij incidence,
      bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair_mem_distancePairs X ij incidence⟩


noncomputable def auxIncidencesOverCurveLabels {d : ℕ}
    (X : PreparedBipartiteInput d) (labels : Finset (X.P₁ × X.P₁)) :
    Finset (Point4 × (X.P₁ × X.P₁)) := by
  classical
  exact (auxIncidences X).filter fun incidence => incidence.2 ∈ labels


namespace AuxiliaryIncidenceDeletionCertificate


end AuxiliaryIncidenceDeletionCertificate

 
noncomputable def bundle_Esgk_AuxiliaryIncidenceDeletion_auxIncidenceFiberUnion {d : ℕ}
    (X : PreparedBipartiteInput d) (labels : Finset (X.P₁ × X.P₁)) :
    Finset (Point4 × (X.P₁ × X.P₁)) := by
  classical
  exact labels.biUnion (auxIncidencesWithCurveLabel X)


end Esgk


