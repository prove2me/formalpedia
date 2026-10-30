-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_Encodings
-- name    : VehicleRoutingSurvey_Routing_Encodings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:10:42.791879+00:00
-- url     : https://prove2.me/theorems/e8166d50-e4bf-40f8-b94a-a825a69b6b95
-- title:
--   Encoded routing decision languages and planarity
-- statement:
--   Rational link weights and decision thresholds are represented by sign, numerator and denominator. Codes retain dimensions, endpoint identities, directions and service flags. Single-vehicle yes-instances have a feasible tour below the threshold. Fleet yes-instances have a positive number of depot-based tours jointly serving every obligation, each below the threshold. Idle tours are permitted. Planarity means a crossing-free topological drawing of the physical multigraph. Routing-kind predicates implement Table 1. Binary encodings separate every integer field; strong hardness uses the published unary encoding of all fields.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), §§2–3, pp. 1–4; Tables 1–2

import Definitions.Def_VehicleRoutingSurvey_Routing_Service
import Definitions.Def_ResourceScheduling_Chain_Complexity

namespace VehicleRoutingSurvey.Routing

abbrev BinarySymbol := Option Bool

def binaryCode (xs : List ℕ) : List BinarySymbol :=
  xs.flatMap (fun n => ((Nat.digits 2 n).map (fun b => some (decide (b = 1)))) ++ [none])

def rationalCode (x : ℚ) : List ℕ :=
  [if x.num < 0 then 1 else 0, x.num.natAbs, x.den]

def binaryLanguage {α : Type} (code : α → List ℕ) (yes : α → Prop) :
    CookPvsNP.Lang BinarySymbol := {s | ∃ x, yes x ∧ s = binaryCode (code x)}

/-- Rational data for bit/unary complexity; the real approximation model is separate. -/
structure EncodedService where
  n : ℕ
  q : ℕ
  tail : Fin q → Fin n
  head : Fin q → Fin n
  directed : Fin q → Bool
  weight : Fin q → ℚ
  vertexRequired : Fin n → Bool
  linkRequired : Fin q → Bool

def EncodedService.service (x : EncodedService) : Service where
  graph := ⟨x.n, x.q, x.tail, x.head, x.directed, fun e => (x.weight e : ℝ)⟩
  vertices := Finset.univ.filter (fun v => x.vertexRequired v)
  links := Finset.univ.filter (fun e => x.linkRequired e)

def EncodedService.code (x : EncodedService) : List ℕ :=
  [x.n, x.q] ++ ((List.finRange x.n).map (fun v => if x.vertexRequired v then 1 else 0)) ++
  (List.finRange x.q).flatMap (fun e =>
    [(x.tail e).val, (x.head e).val, if x.directed e then 1 else 0,
      if x.linkRequired e then 1 else 0] ++ rationalCode (x.weight e))

/-- A topological embedding of the physical multigraph, directions forgotten. -/
def Planar (G : Network) : Prop :=
  ∃ (point : Fin G.n → ℝ × ℝ) (curve : Fin G.q → ℝ → ℝ × ℝ),
    Function.Injective point ∧
    (∀ e, ContinuousOn (curve e) (Set.Icc 0 1) ∧
      curve e 0 = point (G.tail e) ∧ curve e 1 = point (G.head e) ∧
      Set.InjOn (curve e) (Set.Ioo 0 1) ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ v, curve e t ≠ point v) ∧
    ∀ e f, e ≠ f → ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      curve e t ≠ curve f s

inductive RoutingKind where
  | vrp | tsp | dtsp | cpp | dcpp | mcpp | rpp | drpp | scp

def HasKind (x : EncodedService) : RoutingKind → Prop
  | .vrp => True
  | .tsp => (∀ e, x.directed e = false) ∧ (∀ v, x.vertexRequired v = true) ∧
      (∀ e, x.linkRequired e = false)
  | .dtsp => (∀ e, x.directed e = true) ∧ (∀ v, x.vertexRequired v = true) ∧
      (∀ e, x.linkRequired e = false)
  | .cpp => (∀ e, x.directed e = false) ∧ (∀ v, x.vertexRequired v = false) ∧
      (∀ e, x.linkRequired e = true)
  | .dcpp => (∀ e, x.directed e = true) ∧ (∀ v, x.vertexRequired v = false) ∧
      (∀ e, x.linkRequired e = true)
  | .mcpp => (∀ v, x.vertexRequired v = false) ∧ (∀ e, x.linkRequired e = true)
  | .rpp => (∀ e, x.directed e = false) ∧ (∀ v, x.vertexRequired v = false)
  | .drpp => (∀ e, x.directed e = true) ∧ (∀ v, x.vertexRequired v = false)
  | .scp => (∀ v, x.vertexRequired v = false) ∧ (∀ e, x.linkRequired e = x.directed e)

structure RoutingDecision where
  data : EncodedService
  threshold : ℚ

def RoutingDecision.code (x : RoutingDecision) : List ℕ :=
  x.data.code ++ rationalCode x.threshold

def RoutingYes (kind : RoutingKind) (planar : Bool) (x : RoutingDecision) : Prop :=
  let I := x.data.service
  Connected I.graph ∧ Nonnegative I.graph ∧ HasKind x.data kind ∧
    (planar = true → Planar I.graph) ∧
    ∃ u ts, Feasible I u ts ∧ pathCost I.graph ts ≤ (x.threshold : ℝ)

structure FleetDecision where
  data : EncodedService
  m : ℕ
  depot : Fin data.n
  threshold : ℚ

def FleetDecision.code (x : FleetDecision) : List ℕ :=
  x.data.code ++ [x.m, x.depot.val] ++ rationalCode x.threshold

def FleetFeasible (I : Service) (d : Fin I.graph.n) (m : ℕ)
    (tours : List (List (Traversal I.graph))) : Prop :=
  tours.length = m ∧ (∀ ts ∈ tours, IsPath I.graph d ts d) ∧
  (∀ v ∈ I.vertices, ∃ ts ∈ tours, v ∈ Visited I.graph d ts) ∧
  ∀ e ∈ I.links, ∃ ts ∈ tours, ∃ t ∈ ts, t.1 = e

def FleetYes (kind : RoutingKind) (planar : Bool) (fixed : Option ℕ)
    (x : FleetDecision) : Prop :=
  let I := x.data.service
  0 < x.m ∧ (∀ k, fixed = some k → x.m = k) ∧
  Connected I.graph ∧ Nonnegative I.graph ∧ HasKind x.data kind ∧
  (planar = true → Planar I.graph) ∧
  ∃ tours, FleetFeasible I x.depot x.m tours ∧
    ∀ ts ∈ tours, pathCost I.graph ts ≤ (x.threshold : ℝ)

end VehicleRoutingSurvey.Routing


