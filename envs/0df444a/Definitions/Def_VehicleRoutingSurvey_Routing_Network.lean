-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_Network
-- name    : VehicleRoutingSurvey_Routing_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:08:51.107834+00:00
-- url     : https://prove2.me/theorems/ef8a29d5-08df-40a8-a9e5-a541b9344ea9
-- title:
--   Finite weighted mixed multigraphs and walks
-- statement:
--   A network has finitely many vertices and separately identified links. Each link has two endpoints, a direction flag, and a real weight. A directed link can be traversed only forward; an undirected link permits both orientations. Paths retain every traversal occurrence, so repeated links contribute repeatedly to the cost. Connectivity includes a vertex and directed reachability between every pair. Shortest distance is the infimum of path costs; a shortest-path predicate compares concrete paths. Nonnegativity and undirectedness are separate predicates.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), §2, pp. 1–2

import Mathlib

namespace VehicleRoutingSurvey.Routing

/-- A finite mixed multigraph. Link identifiers distinguish parallel links and loops. -/
structure Network where
  n : ℕ
  q : ℕ
  tail : Fin q → Fin n
  head : Fin q → Fin n
  directed : Fin q → Bool
  weight : Fin q → ℝ

abbrev Traversal (G : Network) := Fin G.q × Bool

def start (G : Network) (t : Traversal G) : Fin G.n :=
  if t.2 then G.tail t.1 else G.head t.1

def finish (G : Network) (t : Traversal G) : Fin G.n :=
  if t.2 then G.head t.1 else G.tail t.1

def IsPath (G : Network) : Fin G.n → List (Traversal G) → Fin G.n → Prop
  | u, [], v => u = v
  | u, t :: ts, v => u = start G t ∧
      (G.directed t.1 = false ∨ t.2 = true) ∧ IsPath G (finish G t) ts v

def pathCost (G : Network) (ts : List (Traversal G)) : ℝ :=
  (ts.map (fun t => G.weight t.1)).sum

def Connected (G : Network) : Prop :=
  0 < G.n ∧ ∀ u v, ∃ ts, IsPath G u ts v

def Nonnegative (G : Network) : Prop := ∀ e, 0 ≤ G.weight e

def Undirected (G : Network) : Prop := ∀ e, G.directed e = false

noncomputable def distance (G : Network) (u v : Fin G.n) : ℝ :=
  sInf {c | ∃ ts, IsPath G u ts v ∧ c = pathCost G ts}

def ShortestPath (G : Network) (u v : Fin G.n) (ts : List (Traversal G)) : Prop :=
  IsPath G u ts v ∧ ∀ ss, IsPath G u ss v → pathCost G ts ≤ pathCost G ss

end VehicleRoutingSurvey.Routing


