-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_Service
-- name    : VehicleRoutingSurvey_Routing_Service
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:09:40.355228+00:00
-- url     : https://prove2.me/theorems/12257fc1-02bf-41e0-9070-0ce82ccaa054
-- title:
--   Required service and routing optima
-- statement:
--   A service instance consists of a mixed network, a subset of required vertices, and a subset of required links. A feasible solution is a closed walk visiting each required vertex and traversing each required link. Its optimum is the infimum of feasible walk costs. Rural instances are connected undirected networks with nonnegative real weights, no required vertices, and arbitrary required links. Empty service permits an idle tour; required components need not be connected.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), §2, pp. 1–2; Table 1

import Definitions.Def_VehicleRoutingSurvey_Routing_Network

namespace VehicleRoutingSurvey.Routing

/-- Service obligations are separate from the travel network. -/
structure Service where
  graph : Network
  vertices : Finset (Fin graph.n)
  links : Finset (Fin graph.q)

def Visited (G : Network) (u : Fin G.n) (ts : List (Traversal G)) : Finset (Fin G.n) :=
  {u} ∪ (ts.map (finish G)).toFinset

def Feasible (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)) : Prop :=
  IsPath I.graph u ts u ∧ I.vertices ⊆ Visited I.graph u ts ∧
    ∀ e ∈ I.links, ∃ t ∈ ts, t.1 = e

noncomputable def optimum (I : Service) : ℝ :=
  sInf {c | ∃ u ts, Feasible I u ts ∧ c = pathCost I.graph ts}

def Rural (I : Service) : Prop :=
  Connected I.graph ∧ Nonnegative I.graph ∧ Undirected I.graph ∧ I.vertices = ∅

end VehicleRoutingSurvey.Routing


