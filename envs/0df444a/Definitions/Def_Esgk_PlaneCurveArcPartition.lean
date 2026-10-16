-- Prove2me | Definitions.Def_Esgk_PlaneCurveArcPartition
-- name    : Esgk_PlaneCurveArcPartition
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:53:14.810234+00:00
-- url     : https://prove2.me/theorems/bf9defec-b249-4bdf-9e7e-2d772ad580a4
-- title:
--   Finite arc partitions with controlled sample size
-- statement:
--   This records a partition of a regular curve region, after finitely many cuts, into disjoint nonempty open connected arcs with a prescribed sample-size bound. The data include bounds on cuts, arcs and boundary points, together with the requirement that at most two arc closures contain any point.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCurveRegularChart
import Definitions.Def_Esgk_PlaneCurveSafeComponents
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

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


structure PlaneCurveArcPartition (G : PlanePoly) (ε : ℝ) (o : Point2)
    (P : Finset (planeCurveRegularLocus G)) (d k : ℕ) where
  cuts : Finset (planeCurveRegularLocus G)
  arcs : Finset (Set (planeCurveRegularLocus G))
  boundary : Finset (planeCurveRegularLocus G)
  level_pos : 0 < ε
  cuts_subset : (cuts : Set (planeCurveRegularLocus G)) ⊆ planeCurveSafeSet G ε o
  cuts_disjoint : Disjoint P cuts
  cuts_card_le : cuts.card ≤ P.card / k
  arcs_card_le : arcs.card ≤ cuts.card + 6 * d * d
  boundary_card_le : boundary.card ≤ cuts.card + 3 * d * d
  arc_properties : ∀ A ∈ arcs, A.Nonempty ∧ IsOpen A ∧ IsConnected A ∧
    A ⊆ planeCurveSafeSet G ε o ∧ Disjoint A (cuts : Set (planeCurveRegularLocus G)) ∧
    (P.filter (fun p ↦ p ∈ A)).card ≤ k
  arcs_disjoint : (arcs : Set (Set (planeCurveRegularLocus G))).Pairwise Disjoint
  arcs_cover : (⋃ A ∈ arcs, A) = planeCurveSafeSet G ε o \ (cuts : Set (planeCurveRegularLocus G))
  arc_frontier : ∀ A ∈ arcs, frontier A ⊆ (boundary : Set (planeCurveRegularLocus G))
  closure_card_le : ∀ p : planeCurveRegularLocus G,
    (arcs.filter (fun A ↦ p ∈ closure A)).card ≤ 2


end Esgk


