-- Prove2me | Definitions.Def_Esgk_MaximallyCircularIntrinsicCellCover
-- name    : Esgk_MaximallyCircularIntrinsicCellCover
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:07:05.322498+00:00
-- url     : https://prove2.me/theorems/046aa072-7c22-49ef-bccb-7ede004c114d
-- title:
--   Finite cell-cover data for auxiliary incidences
-- statement:
--   This structure records cells, target pairs, label pairs, exceptional pairs, covering conditions, incidence-label containment, and the stated cardinality bounds. Its accompanying proposition specifies when such a cover is required; it does not by itself assert that one exists.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_MaximallyCircularAuxiliaryCodegree
import Definitions.Def_Esgk_MaximallyCircularLargeScaleIncidence
import Definitions.Def_Esgk_PachDeZeeuwQuadraticDegree
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_Esgk_PlaneNonabsoluteRealPointBound
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)


structure IntrinsicAuxiliaryCellCover {d : ℕ}
    (X : PreparedBipartiteInput d) (N j : ℕ) where
  cells : Finset ℕ
  points : ℕ → Finset (X.P₂ × X.P₂)
  labels : ℕ → Finset (X.P₁ × X.P₁)
  exceptional : Finset (X.P₂ × X.P₂)
  exceptional_card_le : exceptional.card ≤ 4 * d ^ 2 * N
  covers : ∀ pq, pq ∉ exceptional → ∃ ω ∈ cells, pq ∈ points ω
  labels_cover : ∀ ω ∈ cells, ∀ pq ∈ points ω, ∀ ij,
    auxPointPairCurveIncidence X pq ij → ij ∈ labels ω
  cells_card_le : (cells.card : ℝ) ≤ 2 * (d : ℝ) ^ 2 * (j : ℝ) ^ 2
  points_card_le : ∀ ω ∈ cells,
    ((points ω).card : ℝ) ≤ 4 * (N : ℝ) ^ 2 / ((d : ℝ) ^ 2 * (j : ℝ) ^ 2)
  labels_card_le : (∑ ω ∈ cells, ((labels ω).card : ℝ)) ≤
    20 * (d : ℝ) ^ 2 * (j : ℝ) * (N : ℝ) ^ 2


def MaximallyCircularIntrinsicCellCoverStatement : Prop :=
  ∀ (G : PlanePoly) (S : Finset PachDeZeeuw.Algebraic.Point2)
    (X : PreparedBipartiteInput G.totalDegree),
    Irreducible G →
    IsAbsolutelyIrreducible G →
    ¬ IsCircleFactor G →
    IsMaximallyCircular G →
    (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G →
    SelfCurvePreparedInput X →
    X.C₂ = PlaneCurveZeroSet G →
    Disjoint X.P₁ X.P₂ →
    X.P₁ ∪ X.P₂ = S →
    X.P₁.card ≤ 2 * X.P₂.card →
    X.P₂.card ≤ 2 * X.P₁.card →
    0 < X.P₁.card * X.P₂.card →
    ∀ j : ℕ, 24 * G.totalDegree ≤ j →
      j * G.totalDegree < S.card →
      Nonempty (IntrinsicAuxiliaryCellCover X S.card j)


end Esgk


