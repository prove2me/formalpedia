-- Prove2me | Definitions.Def_Esgk_MaximallyCircularQuarticFromIncidence
-- name    : Esgk_MaximallyCircularQuarticFromIncidence
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:03:31.596368+00:00
-- url     : https://prove2.me/theorems/19793687-9ae2-480e-bec5-5055c30a5951
-- title:
--   The all-scale auxiliary incidence proposition
-- statement:
--   This defines the proposition asserting a universal constant $K\ge1$ for the bound $I\le K(dN^3/\sqrt j+d^2jN^2+N^2+d^4j^2+d^3N^2)$ on auxiliary incidences. Its hypotheses require an irreducible, absolutely irreducible, noncircular maximally circular degree-$d$ polynomial, an $N$-point sample on its zero set, prepared data on that same curve with a disjoint partition into two nonempty samples each at most twice the other’s size, and $24d\le j$.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_FiniteIncidenceCodegreeBound
import Definitions.Def_Esgk_MaximallyCircularAuxiliaryCodegree
import Definitions.Def_Esgk_MaximallyCircularQuarticBootstrap
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

open Filter PachDeZeeuw.Algebraic
open PachDeZeeuw (PreparedBipartiteInput)


def MaximallyCircularRawAuxiliaryIncidenceStatement : Prop :=
  ∃ K : ℕ, 1 ≤ K ∧
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
        (finiteIncidenceCount
          (Finset.univ : Finset (X.P₂ × X.P₂))
          (Finset.univ : Finset (X.P₁ × X.P₁))
          (auxPointPairCurveIncidence X) : ℝ) ≤
          (K : ℝ) * ((G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 /
              Real.sqrt (j : ℝ) +
            (G.totalDegree : ℝ) ^ 2 * (j : ℝ) * (S.card : ℝ) ^ 2 +
            (S.card : ℝ) ^ 2 +
            (G.totalDegree : ℝ) ^ 4 * (j : ℝ) ^ 2 +
            (G.totalDegree : ℝ) ^ 3 * (S.card : ℝ) ^ 2)


end Esgk


