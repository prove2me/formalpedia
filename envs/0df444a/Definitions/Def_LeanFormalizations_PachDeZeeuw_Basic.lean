-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
-- name    : LeanFormalizations_PachDeZeeuw_Basic
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:22.327842+00:00
-- url     : https://prove2.me/theorems/30e6698c-2725-4aa9-b04f-67398157f983
-- title:
--   Prepared samples for bipartite distances on curves
-- statement:
--   This defines bipartite distance values and equal-distance quadruples, together with finite samples on two irreducible curves of bounded degree. The prepared data record nonverticality, disjointness, circle-center avoidance, sparse circle and line fibers, and exclusion of parallel or orthogonal line pairs and concentric circle pairs.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry

 
abbrev Point4 := EuclideanSpace ℝ (Fin 4)

 
noncomputable def bipartiteDistances (P Q : Finset Point2) : Finset ℝ :=
  (P.product Q).image (fun pq ↦ dist pq.1 pq.2)

def bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet (a b c : ℝ) : Set Point2 :=
  {p : Point2 | a * p 0 + b * p 1 = c}

 
def ParallelLinePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ a b c₁ c₂ : ℝ, (a, b) ≠ (0, 0) ∧
    C₁ = bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a b c₁ ∧ C₂ = bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a b c₂

 
def OrthogonalLinePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℝ, (a₁, b₁) ≠ (0, 0) ∧ (a₂, b₂) ≠ (0, 0) ∧
    a₁ * a₂ + b₁ * b₂ = 0 ∧
    C₁ = bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a₁ b₁ c₁ ∧ C₂ = bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a₂ b₂ c₂

 
def ConcentricCirclePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ center : Point2, ∃ r₁ r₂ : ℝ,
    C₁ = Metric.sphere center r₁ ∧ C₂ = Metric.sphere center r₂


def ExceptionalCurvePair (C₁ C₂ : Set Point2) : Prop :=
  ParallelLinePair C₁ C₂ ∨ OrthogonalLinePair C₁ C₂ ∨ ConcentricCirclePair C₁ C₂

lemma exceptionalCurvePair_of_parallelLines {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inl h


lemma exceptionalCurvePair_of_concentricCircles {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inr (Or.inr h)


def IsVerticalLine (C : Set Point2) : Prop :=
  ∃ c : ℝ, C = {p : Point2 | p 0 = c}


def CircleCenterNotIn (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ (center : Point2) (r : ℝ), C = Metric.sphere center r → center ∉ (P : Set Point2)


def ConcentricFibersSparse (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ (center : Point2) (r : ℝ), C = Metric.sphere center r →
    ∀ ρ : ℝ, ((P : Set Point2) ∩ Metric.sphere center ρ).Subsingleton


def ParallelReflectionFibersSparse (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ a b c : ℝ, (a, b) ≠ (0, 0) → C = bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a b c →
    ∀ c' : ℝ,
      ((P : Set Point2) ∩ (bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a b c' ∪ bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a b (2 * c - c'))).Subsingleton


def OrthogonalFibersSparse (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ a b c : ℝ, (a, b) ≠ (0, 0) → C = bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a b c →
    ∀ a' b' c' : ℝ, a * a' + b * b' = 0 →
      ((P : Set Point2) ∩ bundle_LeanFormalizations_PachDeZeeuw_Basic_lineSet a' b' c').Subsingleton


structure Assumption31Data
    (C₁ C₂ : Set Point2) (P₁ P₂ : Finset Point2) where
   
  noVerticalComponent₁ : ¬ IsVerticalLine C₁
   
  noVerticalComponent₂ : ¬ IsVerticalLine C₂
   
  pointSetsDisjoint : Disjoint (P₁ : Set Point2) (P₂ : Set Point2)
   

  circleCenterNotInPointSet :
    CircleCenterNotIn C₁ P₂ ∧ CircleCenterNotIn C₂ P₁
   

  sparseConcentricFibers :
    ConcentricFibersSparse C₁ P₂ ∧ ConcentricFibersSparse C₂ P₁
   

  sparseParallelFibers :
    ParallelReflectionFibersSparse C₁ P₂ ∧ ParallelReflectionFibersSparse C₂ P₁
   

  sparseOrthogonalFibers :
    OrthogonalFibersSparse C₁ P₂ ∧ OrthogonalFibersSparse C₂ P₁
   
  noExceptionalPair : ¬ ExceptionalCurvePair C₁ C₂


structure PreparedBipartiteInput (d : ℕ) where
  C₁ : Set Point2
  C₂ : Set Point2
  P₁ : Finset Point2
  P₂ : Finset Point2
  hC₁ : PlaneCurve.IsIrreducibleCurve d C₁
  hC₂ : PlaneCurve.IsIrreducibleCurve d C₂
  hP₁ : (P₁ : Set Point2) ⊆ C₁
  hP₂ : (P₂ : Set Point2) ⊆ C₂
  notExceptional : ¬ ExceptionalCurvePair C₁ C₂
  assumption31 : Assumption31Data C₁ C₂ P₁ P₂

noncomputable def bundle_LeanFormalizations_PachDeZeeuw_Basic_distanceFiber (P Q : Finset Point2) (r : ℝ) :
    Finset (Point2 × Point2) :=
  (P.product Q).filter (fun pq ↦ dist pq.1 pq.2 = r)

noncomputable def bundle_LeanFormalizations_PachDeZeeuw_Basic_equalDistanceQuadruplePairs {d : ℕ}
    (X : PreparedBipartiteInput d) :
    Finset ((Point2 × Point2) × (Point2 × Point2)) :=
  ((X.P₁.product X.P₂).product (X.P₁.product X.P₂)).filter
    (fun pp ↦ dist pp.1.1 pp.1.2 = dist pp.2.1 pp.2.2)


noncomputable def equalDistanceQuadruples {d : ℕ}
    (X : PreparedBipartiteInput d) :
    Finset ((Point2 × Point2) × (Point2 × Point2)) :=
  bundle_LeanFormalizations_PachDeZeeuw_Basic_equalDistanceQuadruplePairs X


end PachDeZeeuw


