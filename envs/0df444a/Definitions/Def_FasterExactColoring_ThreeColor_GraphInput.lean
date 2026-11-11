-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_GraphInput
-- name    : FasterExactColoring_ThreeColor_GraphInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:50.318043+00:00
-- url     : https://prove2.me/theorems/4cb9dbbb-356c-49ab-a9ba-82811aa8e00c
-- title:
--   Finite graph inputs, colorings and distance-two packings
-- statement:
--   A graph on $n$ labeled vertices is a simple undirected graph with a computable adjacency relation. A proper $k$-coloring assigns a color to every vertex and assigns different colors to adjacent vertices. A list coloring additionally respects an arbitrary finite allowed-color list at each vertex, including an empty list.
--
--   A distance-two packing $P$ satisfies
--   $$u\ne v\in P\Longrightarrow uv\notin E(G)\text{ and }N_G(u)\cap N_G(v)=\varnothing.$$
--   Thus vertices in different components may both be chosen. Degrees, maximum degree (zero for the empty graph), and components are computed from adjacency. Components use $n$ rounds of finite neighborhood expansion. The graph code contains $n$ followed by its full $n\times n$ adjacency matrix. Finite vertex sets are encoded by their size and increasing labels.
--
--   These are the common input and combinatorial interfaces for all statements. **Formalization Note** Vertices use $\mathrm{Fin}(n)$ and colors $\mathrm{Fin}(k)$, replacing the source's labels $1,\ldots,k$ by $0,\ldots,k-1$. The empty graph and zero-color palette remain available.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Section 2, pp. 2–3 (PDF pp. 4–5); Section 4.3, p. 7 (PDF p. 9)

import Mathlib

namespace FasterExactColoring.ThreeColor

/-- Section 2: finite simple labeled graphs, with executable adjacency. -/
structure GraphInput (n : ℕ) where
  graph : SimpleGraph (Fin n)
  adjDec : DecidableRel graph.Adj
attribute [instance] GraphInput.adjDec

def vertices {n : ℕ} : Finset (Fin n) := Finset.univ

def graphCode {n : ℕ} (G : GraphInput n) : List ℕ :=
  n :: (List.finRange n).flatMap (fun u =>
    (List.finRange n).map (fun v => if G.graph.Adj u v then 1 else 0))

def degreeIn {n : ℕ} (G : GraphInput n) (X : Finset (Fin n)) (v : Fin n) : ℕ :=
  (X.filter (G.graph.Adj v)).card

def degree {n : ℕ} (G : GraphInput n) (v : Fin n) : ℕ := degreeIn G vertices v

def degreeSet {n : ℕ} (G : GraphInput n) (i : ℕ) : Finset (Fin n) :=
  vertices.filter (fun v => degree G v = i)

def properColoring {n k : ℕ} (G : GraphInput n) (f : Fin n → Fin k) : Prop :=
  ∀ u v, G.graph.Adj u v → f u ≠ f v

def colorable {n : ℕ} (G : GraphInput n) (k : ℕ) : Prop :=
  ∃ f : Fin n → Fin k, properColoring G f

def listColorable {n k : ℕ} (G : GraphInput n) (L : Fin n → Finset (Fin k)) : Prop :=
  ∃ f : Fin n → Fin k, properColoring G f ∧ ∀ v, f v ∈ L v

def listCode {n k : ℕ} (L : Fin n → Finset (Fin k)) : List ℕ :=
  k :: (List.finRange n).flatMap (fun v =>
    (L v).card :: ((L v).sort (· ≤ ·)).map Fin.val)

/-- A bounded finite flood fill, including the starting vertex. -/
def component {n : ℕ} (G : GraphInput n) (X : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  ((fun S : Finset (Fin n) => S ∪ X.filter (fun w => ∃ u ∈ S, G.graph.Adj u w))^[n]) {v}

def connected {n : ℕ} (G : GraphInput n) : Prop :=
  0 < n ∧ ∀ v, component G vertices v = vertices

/-- Distance at least three, including vertices in different components. -/
def twoPacking {n : ℕ} (G : GraphInput n) (X : Finset (Fin n)) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬ G.graph.Adj u v ∧
    ¬ ∃ w, G.graph.Adj u w ∧ G.graph.Adj w v

def vertexSetCode {n : ℕ} (X : Finset (Fin n)) : List ℕ :=
  X.card :: (X.sort (· ≤ ·)).map Fin.val

def maximumDegree {n : ℕ} (G : GraphInput n) : ℕ :=
  (List.finRange n).foldl (fun a v => max a (degree G v)) 0

def degreeThreeCycle {n : ℕ} (G : GraphInput n) : Prop :=
  ¬ (G.graph.induce {v | degree G v = 3}).IsAcyclic

end FasterExactColoring.ThreeColor


