-- Prove2me | Definitions.Def_GoldsteinMCSP_Hardness_Gadget
-- name    : GoldsteinMCSP_Hardness_Gadget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:12:11.753085+00:00
-- url     : https://prove2.me/theorems/49f80340-828c-4a84-b10d-70a3a6601ceb
-- title:
--   The concrete cubic-graph string gadget and socket-splicing construction
-- statement:
--   Graphs are simple undirected graphs on vertices 0,...,N−1 with decidable adjacency. Cubic means that every vertex has exactly three neighbors. An independent vertex set contains no adjacent pair. Edges are enumerated in vertex order. Repeated leaf peeling, a bounded nonbacktracking walk and cycle deletion select a maximal edge-disjoint cycle family. Each selected cycle is oriented cyclically; the remaining forest is oriented away from its least degree-one vertex in each nontrivial component. All choices are deterministic.
--
--   Vertex u has ten symbols 10u+j, in the order a,b,c,d,e,f,g,h,k,l. The seven X components are d, ab, cde, befg, fhk, gl, h; the seven Y components are b, cd, abe, defh, fgl, hk, g. These are the exact equation (3) lists, with 16 letters per side. For each oriented edge u→v, outgoing rank selects k_u then l_u, and incoming rank selects a_v then c_v. The equation (4) splice replaces R s_u by R s_u S, replaces s_v S by the singleton s_u, and renames s_v to s_u in Y. The construction folds these operations over all edges and returns the global pair of component lists. It does not assume that the modified local pairs are related, or assume any optimum identity or reduction correctness. Empty graphs yield two empty families.
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Section 2, printed/PDF pp. 6–8, equations (3)–(4)

import Definitions.Def_GoldsteinMCSP_Hardness_Strings

namespace GoldsteinMCSP.Hardness

abbrev Edges := List (ℕ × ℕ)

def adjacent (es : Edges) (u v : ℕ) : Bool :=
  es.contains (u,v) || es.contains (v,u)

def neighbors (es : Edges) (u : ℕ) : List ℕ :=
  es.filterMap fun e => if e.1 == u then some e.2
    else if e.2 == u then some e.1 else none

def graphEdges {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : Edges :=
  (List.finRange N).flatMap fun u =>
    ((List.finRange N).filter fun v => u.val < v.val && decide (G.Adj u v)).map
      fun v => (u.val,v.val)

/-- One round of leaf peeling; iteration removes dangling trees. -/
def peel (_N : ℕ) (es : Edges) : Edges :=
  es.filter fun e => (neighbors es e.1).length > 1 && (neighbors es e.2).length > 1

def core (N : ℕ) (es : Edges) : Edges :=
  (List.range N).foldl (fun edges _ => peel N edges) es

/-- In a finite minimum-degree-two graph, a non-backtracking walk finds a cycle. -/
def findCycleWalk (es : Edges) : ℕ → Option ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, _ => []
  | k+1, prev, v, path =>
    if path.contains v then path.dropWhile (· != v)
    else match ((neighbors es v).filter fun w => some w != prev).head? with
      | none => []
      | some w => findCycleWalk es k (some v) w (path ++ [v])

def cycleEdges (vs : List ℕ) : Edges := vs.zip (vs.drop 1 ++ vs.take 1)

/-- Greedily remove the first cycle until none remains. This yields the page's maximal
edge-disjoint cycle family, with all tie choices fixed by the input vertex order. -/
def orientCycles (N : ℕ) : ℕ → Edges → Edges × Edges
  | 0, es => ([], es)
  | k+1, es =>
    let cs := core N es
    match cs.head? with
    | none => ([], es)
    | some e =>
      let cyc := cycleEdges (findCycleWalk cs (N+1) none e.1 [])
      if cyc.isEmpty then ([], es)
      else
        let rest := es.filter fun e => !adjacent cyc e.1 e.2
        let (done, forest) := orientCycles N k rest
        (cyc ++ done, forest)

def reach (es : Edges) : ℕ → List ℕ → List ℕ
  | 0, vs => vs
  | k+1, vs => reach es k ((vs ++ vs.flatMap (neighbors es)).eraseDups)

def distance (N : ℕ) (es : Edges) (u v : ℕ) : ℕ :=
  ((List.range (N+1)).find? fun k => (reach es k [u]).contains v).getD (N+1)

/-- Root each nontrivial tree at its least-labelled degree-one vertex, then orient outward. -/
def orientForest (N : ℕ) (es : Edges) : Edges := es.map fun e =>
  let component := reach es N [e.1]
  let root := ((List.range N).find? fun u => component.contains u &&
    (neighbors es u).length == 1).getD e.1
  if distance N es root e.1 < distance N es root e.2 then e else (e.2,e.1)

def orientedEdges {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : Edges :=
  let es := graphEdges G
  let (cycles,forest) := orientCycles N es.length es
  cycles ++ orientForest N forest

/-- Ten distinct symbols per vertex, in the order a,b,c,d,e,f,g,h,k,l. -/
def symbol (u j : ℕ) : ℕ := 10*u+j

def gadgetX (u : ℕ) : Family :=
  [[3], [0,1], [2,3,4], [1,4,5,6], [5,7,8], [6,9], [7]].map
    (List.map (symbol u))

def gadgetY (u : ℕ) : Family :=
  [[1], [2,3], [0,1,4], [3,4,5,7], [5,6,9], [7,8], [6]].map
    (List.map (symbol u))

/-- Equation (4), applied to global component lists. Unique sockets identify exactly
one affected component on each side, so multiplicity and component ownership persist. -/
def spliceSockets (su sv : ℕ) (a b : Family) : Family × Family :=
  let tail := ((a.find? fun w => w.head? == some sv).getD []).drop 1
  let a' := a.map fun w =>
    if w.getLast? == some su then w ++ tail
    else if w.head? == some sv then [su] else w
  let b' := b.map (List.map fun x => if x == sv then su else x)
  (a', b')

/-- Process every edge once; outgoing and incoming ranks choose the two free sockets. -/
def gadgetInstance {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : Family × Family :=
  let es := orientedEdges G
  es.zipIdx.foldl (fun state ei =>
    let (u,v) := ei.1
    let prev := es.take ei.2
    let outRank := (prev.filter fun e => e.1 == u).length
    let inRank := (prev.filter fun e => e.2 == v).length
    let su := symbol u (if outRank == 0 then 8 else 9)
    let sv := symbol v (if inRank == 0 then 0 else 2)
    spliceSockets su sv state.1 state.2)
    ((List.range N).flatMap gadgetX, (List.range N).flatMap gadgetY)

/-- Simple undirected graphs have the Mathlib meaning; cubic means degree exactly three. -/
def cubic {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : Prop :=
  ∀ u, ((List.finRange N).filter fun v => decide (G.Adj u v)).length = 3

def independent {N : ℕ} (G : SimpleGraph (Fin N)) (s : Finset (Fin N)) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v

end GoldsteinMCSP.Hardness


