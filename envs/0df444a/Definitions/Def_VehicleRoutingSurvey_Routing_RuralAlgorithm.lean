-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_RuralAlgorithm
-- name    : VehicleRoutingSurvey_Routing_RuralAlgorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:10:58.928582+00:00
-- url     : https://prove2.me/theorems/6a034c9c-73fd-4c31-be7e-0e7a3cec362d
-- title:
--   Rural postman spanning tree plus matching runs
-- statement:
--   The required-link endpoints are partitioned by required-edge connectivity. A minimum-cost tree joins their components using original shortest-path distances, keeping endpoints and path copies. A minimum perfect matching joins the odd-degree vertices of the resulting multigraph; its edges are also expanded to shortest paths. The output is an Euler tour of all required and augmentation copies. The empty required set returns an idle tour. Matching uses the published perfect-matching definitions, with a list retaining endpoint orientation and multiplicity information. The procedure never uses the optimal rural tour as an input.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), Table 3, p. 5, RPP row [9]; concrete reading specified by the captain brief

import Definitions.Def_VehicleRoutingSurvey_Routing_Service
import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace VehicleRoutingSurvey.Routing

def requiredVertices (I : Service) : Finset (Fin I.graph.n) :=
  I.links.image I.graph.tail ∪ I.links.image I.graph.head

def requiredAdjacent (I : Service) (u v : Fin I.graph.n) : Prop :=
  ∃ e ∈ I.links, (I.graph.tail e = u ∧ I.graph.head e = v) ∨
    (I.graph.tail e = v ∧ I.graph.head e = u)

def sameComponent (I : Service) := Relation.ReflTransGen (requiredAdjacent I)

/-- One representative of each nonempty required component. -/
def ComponentRepresentatives (I : Service) (cs : List (Fin I.graph.n)) : Prop :=
  (∀ u ∈ cs, u ∈ requiredVertices I) ∧
  cs.Pairwise (fun u v => ¬ sameComponent I u v) ∧
  ∀ u ∈ requiredVertices I, ∃ v ∈ cs, sameComponent I u v

noncomputable def pairCost (G : Network) (ps : List (Fin G.n × Fin G.n)) : ℝ :=
  (ps.map (fun p => distance G p.1 p.2)).sum

/-- A tree on the required components, with the actual endpoints retained. -/
def ComponentTree (I : Service) (ps : List (Fin I.graph.n × Fin I.graph.n)) : Prop :=
  (∃ cs, ComponentRepresentatives I cs ∧ ps.length + 1 = cs.length) ∧
  (∀ p ∈ ps, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧
    ¬ sameComponent I p.1 p.2) ∧
  ∀ u ∈ requiredVertices I, ∀ v ∈ requiredVertices I,
    Relation.ReflTransGen (fun x y => requiredAdjacent I x y ∨
      (x, y) ∈ ps ∨ (y, x) ∈ ps) u v

def MinimumComponentTree (I : Service)
    (ps : List (Fin I.graph.n × Fin I.graph.n)) : Prop :=
  ComponentTree I ps ∧ ∀ qs, ComponentTree I qs → pairCost I.graph ps ≤ pairCost I.graph qs

/-- Expansion retains every copy of an edge on every chosen shortest path. -/
def Expands (G : Network) (ps : List (Fin G.n × Fin G.n))
    (paths : List (List (Traversal G))) : Prop :=
  List.Forall₂ (fun p ts => ShortestPath G p.1 p.2 ts) ps paths

def degree (G : Network) (es : List (Fin G.q)) (v : Fin G.n) : ℕ :=
  (es.filter (fun e => G.tail e = v)).length +
    (es.filter (fun e => G.head e = v)).length

def oddVertices (G : Network) (es : List (Fin G.q)) : Finset (Fin G.n) :=
  Finset.univ.filter (fun v => Odd (degree G es v))

def matchingEdges (G : Network) (ps : List (Fin G.n × Fin G.n)) : Finset (Sym2 (Fin G.n)) :=
  (ps.map (fun p => s(p.1, p.2))).toFinset

def PerfectMatching (G : Network) (es : List (Fin G.q))
    (ps : List (Fin G.n × Fin G.n)) : Prop :=
  (ps.map (fun p => s(p.1, p.2))).Nodup ∧
  SupplyChainTheory.IsPerfectMatchingOn (oddVertices G es) (matchingEdges G ps)

def MinimumMatching (G : Network) (es : List (Fin G.q))
    (ps : List (Fin G.n × Fin G.n)) : Prop :=
  (ps.map (fun p => s(p.1, p.2))).Nodup ∧
  SupplyChainTheory.IsMinMatchingOn (distance G) (oddVertices G es) (matchingEdges G ps)

/-- The spanning-tree-plus-matching run relation. No objective bound occurs here. -/
def RuralRun (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)) : Prop :=
  if I.links = ∅ then ts = [] else
    ∃ (base : List (Fin I.graph.q))
      (tree matching : List (Fin I.graph.n × Fin I.graph.n))
      (tp mp : List (List (Traversal I.graph))),
      base.Nodup ∧ base.toFinset = I.links ∧
      MinimumComponentTree I tree ∧ Expands I.graph tree tp ∧
      MinimumMatching I.graph (base ++ (tp.flatten.map Prod.fst)) matching ∧
      Expands I.graph matching mp ∧ IsPath I.graph u ts u ∧
      (ts.map Prod.fst).Perm
        (base ++ tp.flatten.map Prod.fst ++ mp.flatten.map Prod.fst)

end VehicleRoutingSurvey.Routing


