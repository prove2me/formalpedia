-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_SchedulingGeometry
-- name    : VehicleRoutingSurvey_Routing_SchedulingGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:11:47.009054+00:00
-- url     : https://prove2.me/theorems/086aa14c-20a4-452c-8e36-4633bf7b38ce
-- title:
--   Completion-window vehicle schedules and Euclidean tour decisions
-- statement:
--   A vehicle schedule retains outbound travel, each trip duration, pairwise deadhead travel and return travel. Trips are assigned exactly once to ordered vehicle routes. Completion times lie in their windows and consecutive trips respect travel and service duration. Departure and return times are existentially specified without an additional depot horizon. The common-window language has zero lower bounds and one common upper bound. Separately, Euclidean instances encode rational planar coordinates and a rational threshold, and compare true square-root Euclidean lengths along a cyclic permutation.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), §§2–3, pp. 2–4; Table 2 VSP and §3 geometric TSP paragraph

import Definitions.Def_VehicleRoutingSurvey_Routing_Encodings

namespace VehicleRoutingSurvey.Routing

/-- Given trip and deadhead durations; no metric axiom and no depot horizon. -/
structure VehicleScheduleInstance where
  n : ℕ
  outbound : Fin n → ℚ
  duration : Fin n → ℚ
  deadhead : Fin n → Fin n → ℚ
  inbound : Fin n → ℚ
  lower : Fin n → ℚ
  upper : Fin n → ℚ
  vehicles : ℕ

def VehicleScheduleInstance.code (x : VehicleScheduleInstance) : List ℕ :=
  [x.n, x.vehicles] ++ (List.finRange x.n).flatMap (fun j =>
    rationalCode (x.outbound j) ++ rationalCode (x.duration j) ++
    rationalCode (x.inbound j) ++ rationalCode (x.lower j) ++ rationalCode (x.upper j) ++
    (List.finRange x.n).flatMap (fun k => rationalCode (x.deadhead j k)))

def ScheduleYes (x : VehicleScheduleInstance) : Prop :=
  (∀ j, 0 ≤ x.outbound j ∧ 0 ≤ x.duration j ∧ 0 ≤ x.inbound j ∧
    ∀ k, 0 ≤ x.deadhead j k) ∧
  (∀ j, x.lower j = 0) ∧ (∃ u, ∀ j, x.upper j = u) ∧
  ∃ (routes : List (List (Fin x.n))) (completion : Fin x.n → ℝ)
    (depart returnTime : ℕ → ℝ),
    routes.length ≤ x.vehicles ∧ routes.flatten.Perm (List.finRange x.n) ∧
    (∀ j, (x.lower j : ℝ) ≤ completion j ∧ completion j ≤ (x.upper j : ℝ)) ∧
    ∀ i r, routes[i]? = some r →
      r.IsChain (fun j k => completion j + (x.deadhead j k : ℝ) +
        (x.duration k : ℝ) ≤ completion k) ∧
      (∀ j, r.head? = some j → depart i + (x.outbound j : ℝ) +
        (x.duration j : ℝ) ≤ completion j) ∧
      (∀ j, r.getLast? = some j → completion j + (x.inbound j : ℝ) ≤ returnTime i)

def cycleCost {α : Type} (cost : α → α → ℝ) : List α → ℝ
  | [] => 0
  | u :: us => ((u :: us).zip (us ++ [u])).foldl (fun s e => s + cost e.1 e.2) 0

structure EuclideanInstance where
  n : ℕ
  x : Fin n → ℚ
  y : Fin n → ℚ
  threshold : ℚ

def EuclideanInstance.code (I : EuclideanInstance) : List ℕ :=
  [I.n] ++ (List.finRange I.n).flatMap (fun j => rationalCode (I.x j) ++ rationalCode (I.y j)) ++
    rationalCode I.threshold

noncomputable def euclideanDistance (I : EuclideanInstance) (j k : Fin I.n) : ℝ :=
  Real.sqrt (((I.x j : ℝ) - (I.x k : ℝ)) ^ 2 + ((I.y j : ℝ) - (I.y k : ℝ)) ^ 2)

def EuclideanYes (I : EuclideanInstance) : Prop :=
  0 < I.n ∧ ∃ tour, tour.Perm (List.finRange I.n) ∧
    cycleCost (euclideanDistance I) tour ≤ (I.threshold : ℝ)

end VehicleRoutingSurvey.Routing


