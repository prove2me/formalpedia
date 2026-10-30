-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_OptimizationModels
-- name    : VehicleRoutingSurvey_Routing_OptimizationModels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:12:39.235483+00:00
-- url     : https://prove2.me/theorems/2050d492-8e1d-4fa6-b60b-64a984765b19
-- title:
--   General TSP and capacitated tree routing
-- statement:
--   General TSP has a symmetric nonnegative rational matrix without a triangle inequality, and feasible tours are permutations of all vertices. Capacitated tree routing retains the encoded physical tree, depot, positive fleet size, arbitrary nonnegative demands and capacity. Every demand is allocated whole to exactly one vehicle, and visiting or traversing for travel alone need not serve it. Each vehicle returns to the depot and its allocated demand respects capacity. The objective is the sum of all tour costs. Inputs without any feasible service allocation are excluded only from approximation guarantees. Outputs list k depot tours with 1 ≤ k ≤ m and encode the remaining vehicles implicitly as idle, so a binary fleet size never forces a long list of unused vehicles.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), §4, p. 6; Table 4

import Definitions.Def_VehicleRoutingSurvey_Routing_Approximation

namespace VehicleRoutingSurvey.Routing

noncomputable def decodedCost {α : Type} (code : α → List ℕ)
    (cost : α → List ℕ → ℝ) (x y : List ℕ) : ℝ := by
  classical
  exact if h : ∃ I, code I = x then cost (Classical.choose h) y else 0

/-- The concrete instance code determines the data; malformed strings are invalid. -/
noncomputable def encodedProblem {α : Type} (code : α → List ℕ)
    (valid : α → Prop) (feasible : α → List ℕ → Prop) (cost : α → List ℕ → ℝ) :
    MinimizationProblem where
  valid x := ∃ I, code I = x ∧ valid I
  feasible x y := ∃ I, code I = x ∧ valid I ∧ feasible I y
  cost := decodedCost code cost

structure GeneralTSPInstance where
  n : ℕ
  weight : Fin n → Fin n → ℚ

def GeneralTSPInstance.code (I : GeneralTSPInstance) : List ℕ :=
  I.n :: (List.finRange I.n).flatMap (fun i =>
    (List.finRange I.n).flatMap (fun j => rationalCode (I.weight i j)))

def GeneralTSPInstance.cost (I : GeneralTSPInstance) (tour : List ℕ) : ℚ :=
  let pairs := match tour with
    | [] => []
    | [_] => []
    | u :: us => (u :: us).zip (us ++ [u])
  (pairs.map (fun p => if h : p.1 < I.n ∧ p.2 < I.n then
    I.weight ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 0)).sum

def GeneralTSPInstance.Valid (I : GeneralTSPInstance) : Prop :=
  0 < I.n ∧ (∀ i j, 0 ≤ I.weight i j) ∧ (∀ i j, I.weight i j = I.weight j i)

noncomputable def generalTSP : MinimizationProblem :=
  encodedProblem GeneralTSPInstance.code GeneralTSPInstance.Valid
    (fun I tour => tour.Perm (List.range I.n)) (fun I tour => (I.cost tour : ℝ))

structure CapacitatedInstance where
  data : EncodedService
  m : ℕ
  depot : Fin data.n
  vertexDemand : Fin data.n → ℚ
  linkDemand : Fin data.q → ℚ
  capacity : ℚ

def CapacitatedInstance.code (I : CapacitatedInstance) : List ℕ :=
  I.data.code ++ [I.m, I.depot.val] ++ rationalCode I.capacity ++
    (List.finRange I.data.n).flatMap (fun v => rationalCode (I.vertexDemand v)) ++
    (List.finRange I.data.q).flatMap (fun e => rationalCode (I.linkDemand e))

def CapacitatedInstance.Valid (edges : Bool) (I : CapacitatedInstance) : Prop :=
  let S := I.data.service
  0 < I.m ∧ Connected S.graph ∧ Nonnegative S.graph ∧ Undirected S.graph ∧
  I.data.q + 1 = I.data.n ∧ 0 ≤ I.capacity ∧
  (∀ v, 0 ≤ I.vertexDemand v) ∧ (∀ e, 0 ≤ I.linkDemand e) ∧
  HasKind I.data (if edges then .cpp else .tsp)

/-- Only the listed vehicles are encoded; the remaining fleet is idle. -/
def allocationCode (I : CapacitatedInstance) (k : ℕ)
    (routes : Fin k → List (Traversal I.data.service.graph))
    (va : Fin I.data.n → Fin k) (ea : Fin I.data.q → Fin k) : List ℕ :=
  [k] ++ (List.finRange k).flatMap (fun k =>
    (routes k).length :: (routes k).flatMap (fun t => [t.1.val, if t.2 then 1 else 0])) ++
  (List.finRange I.data.n).map (fun v => (va v).val) ++
  (List.finRange I.data.q).map (fun e => (ea e).val)

/-- Each demand is assigned whole to one vehicle; travel alone does not serve it. -/
def CapSolution (edges : Bool) (I : CapacitatedInstance) (y : List ℕ) : Prop :=
  ∃ (k : ℕ) (routes : Fin k → List (Traversal I.data.service.graph))
    (va : Fin I.data.n → Fin k) (ea : Fin I.data.q → Fin k),
    0 < k ∧ k ≤ I.m ∧ y = allocationCode I k routes va ea ∧
    ∀ k, IsPath I.data.service.graph I.depot (routes k) I.depot ∧
      (if edges then
        (∀ e, ea e = k → ∃ t ∈ routes k, t.1 = e) ∧
        (∑ e : Fin I.data.q, if ea e = k then I.linkDemand e else 0) ≤ I.capacity
      else
        (∀ v, va v = k → v ∈ Visited I.data.service.graph I.depot (routes k)) ∧
        (∑ v : Fin I.data.n, if va v = k then I.vertexDemand v else 0) ≤ I.capacity)

/-- Rational total cost, computed from the length-delimited output route blocks. -/
def capRouteCost (I : CapacitatedInstance) : ℕ → List ℕ → ℚ
  | 0, _ => 0
  | _ + 1, [] => 0
  | k + 1, len :: xs =>
      ((List.range len).map (fun j =>
        let e := xs[2 * j]?.getD I.data.q
        if h : e < I.data.q then I.data.weight ⟨e, h⟩ else 0)).sum +
      capRouteCost I k (xs.drop (2 * len))

noncomputable def capacitatedTree (edges : Bool) : MinimizationProblem :=
  encodedProblem CapacitatedInstance.code (CapacitatedInstance.Valid edges)
    (CapSolution edges) (fun I y => (capRouteCost I (y.headD 0) y.tail : ℝ))

end VehicleRoutingSurvey.Routing


