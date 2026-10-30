-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_RuralRuntime
-- name    : VehicleRoutingSurvey_Routing_RuralRuntime
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:12:35.069149+00:00
-- url     : https://prove2.me/theorems/a736115a-0c0d-4876-a22a-4d95fe647942
-- title:
--   Rural postman arithmetic input and implementation contract
-- statement:
--   The input stores the number of vertices and links, endpoints, required flags, and real weights. The output stores a start vertex and the identifier and orientation of each traversal. A single finite arithmetic program must halt with an admissible rural run on every rural instance. For one positive constant C and size threshold N, its step count is at most C(v^3+e) whenever v+e is at least N. The program, C and N are independent of the network and of its weights.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), Table 3, p. 5, RPP complexity cell [9]

import Definitions.Def_VehicleRoutingSurvey_Routing_RuralAlgorithm
import Definitions.Def_VehicleRoutingSurvey_Routing_ArithmeticMachine

namespace VehicleRoutingSurvey.Routing

def ruralNatInput (I : Service) : List ℕ :=
  [I.graph.n, I.graph.q] ++ (List.finRange I.graph.q).flatMap
    (fun e => [(I.graph.tail e).val, (I.graph.head e).val, if e ∈ I.links then 1 else 0])

def ruralRealInput (I : Service) : List ℝ :=
  (List.finRange I.graph.q).map I.graph.weight

def tourCode (G : Network) (u : Fin G.n) (ts : List (Traversal G)) : List ℕ :=
  u.val :: ts.flatMap (fun t => [t.1.val, if t.2 then 1 else 0])

/-- One fixed finite program, correct on every instance, with uniform eventual work bound. -/
def RuralImplementation (p : List ArithmeticInstruction) (C N : ℕ) : Prop :=
  0 < C ∧ ∀ I : Service, Rural I →
    ∃ t u ts, let s := arithmeticRun p t (ruralNatInput I) (ruralRealInput I)
      s.halted = true ∧ arithmeticOutput s = tourCode I.graph u ts ∧ RuralRun I u ts ∧
      (N ≤ I.graph.n + I.graph.q → t ≤ C * (I.graph.n ^ 3 + I.graph.q))

end VehicleRoutingSurvey.Routing


