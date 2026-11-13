-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:48:44.53762+00:00
-- url     : https://prove2.me/theorems/bb7fa001-0051-40b0-b897-b6d133377eb7
-- title:
--   Chapter 1, thm_1_1_common_refinement_points: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_common_refinement_points`: `partitionOfStrictEndpointList`, `partitionOfStrictEndpointList_mem_node`, `DarbouxCommonRefinementPointList`, `concreteCommonRefinementPointList`, `concreteCommonRefinementPartition`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_refinement_points.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

noncomputable def partitionOfStrictEndpointList {a b : ℝ} (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b) :
    Partition a b where
  n := l.length - 1
  hn := by omega
  pts := fun i => l.getD i.val b
  pts_start := by
    exact hstart
  pts_end := by
    have hlast : l.length - 1 < l.length := by omega
    change l.getD (l.length - 1) b = b
    rw [List.getD_eq_getElem l b hlast]
    rw [List.getD_eq_getElem l a hlast] at hend
    exact hend
  strict_mono := by
    refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i
    have hi_succ : i.val + 1 < l.length := by omega
    simpa using hstrict hi_succ


structure DarbouxCommonRefinementPointList {a b : ℝ}
    (P Q : Partition a b) where
  points : List ℝ
  sorted : points.Pairwise (fun x y : ℝ => x ≤ y)
  nodup : points.Nodup
  left_mem : a ∈ points
  right_mem : b ∈ points
  covers_left : ∀ i : Fin (P.n + 1), P.pts i ∈ points
  covers_right : ∀ i : Fin (Q.n + 1), Q.pts i ∈ points
  subset_Icc : ∀ {x : ℝ}, x ∈ points → x ∈ Icc a b

noncomputable def concreteCommonRefinementPointList {a b : ℝ}
    (P Q : Partition a b) :
    DarbouxCommonRefinementPointList P Q where
  points := commonRefinementPointList P Q
  sorted := commonRefinementPointList_sorted P Q
  nodup := commonRefinementPointList_nodup P Q
  left_mem := commonRefinementPointList_left_mem P Q
  right_mem := commonRefinementPointList_right_mem P Q
  covers_left := by
    intro i
    exact commonRefinementPointList_covers_left P Q i
  covers_right := by
    intro i
    exact commonRefinementPointList_covers_right P Q i
  subset_Icc := by
    intro x hx
    exact commonRefinementPointList_subset_Icc P Q hx

noncomputable def concreteCommonRefinementPartition {a b : ℝ}
    (P Q : Partition a b) :
    Partition a b :=
  partitionOfStrictEndpointList
    (commonRefinementPointList P Q)
    (commonRefinementPointList_length_two_le P Q)
    (commonRefinementPointList_getD_zero P Q)
    (commonRefinementPointList_getD_last P Q)
    (fun hi => commonRefinementPointList_adjacent_getD_lt P Q hi)
end Thm11SourceRoute


