-- Prove2me | Definitions.Def_Esgk_MaximallyCircularQuarticBootstrap
-- name    : Esgk_MaximallyCircularQuarticBootstrap
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:02:08.404788+00:00
-- url     : https://prove2.me/theorems/6e6b1603-fd10-4b33-8378-c53d3518c4f7
-- title:
--   The quartic distinct-distance proposition
-- statement:
--   This defines the proposition asserting positive universal natural constants $T,C$ such that $N^4\le C d^4 D(S)^3$ whenever $Td^5\le N^2$. Here $S$ is an $N$-point sample on the real zero set of an irreducible, absolutely irreducible, noncircular maximally circular polynomial of degree $d$, and $D(S)$ counts its positive distinct distances.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceDeficiencyNewton
import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_MaximallyCircularCurveDistinctDistances
import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_Esgk_PlaneNonabsoluteRealPointBound
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open Filter PachDeZeeuw.Algebraic

variable {n : ℕ}

 
def MaximallyCircularQuarticDistinctDistancesStatement : Prop :=
  ∃ T C : ℕ, 0 < T ∧ 0 < C ∧
    ∀ (G : PlanePoly) (S : Finset PachDeZeeuw.Algebraic.Point2),
      Irreducible G →
      IsAbsolutelyIrreducible G →
      ¬ IsCircleFactor G →
      IsMaximallyCircular G →
      (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G →
      T * G.totalDegree ^ 5 ≤ S.card ^ 2 →
        S.card ^ 4 ≤ C * G.totalDegree ^ 4 * (EuclideanGeometry.distinctDistances S) ^ 3


end Esgk


