-- Prove2me | Definitions.Def_Esgk_PlaneCurveCellVisits
-- name    : Esgk_PlaneCurveCellVisits
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:54:14.134982+00:00
-- url     : https://prove2.me/theorems/0983bba6-3559-4cad-9f4a-02832ba29a8a
-- title:
--   Arc pairs meeting an equal-distance relation
-- statement:
--   For a finite family of curve arcs and two fixed centers, this defines the ordered pairs of arcs containing points whose squared distances to the respective centers are equal.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCurveArcPartition
import Definitions.Def_Esgk_PlaneCurveRegularChart
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib
import Mathlib.Data.Finset.Preimage

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology
open scoped Classical
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

 
def planeCurveArcPairVisits {G : PlanePoly}
    (A : Finset (Set (planeCurveRegularLocus G))) (a b : Point2) :=
  (A ×ˢ A).filter (fun C ↦ ∃ p : planeCurveRegularLocus G, p ∈ C.1 ∧
    ∃ q : planeCurveRegularLocus G, q ∈ C.2 ∧
    dist (p : Point2) a ^ 2 = dist (q : Point2) b ^ 2)


end Esgk


