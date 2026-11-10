-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_Graph
-- name    : FlowOptimalSeparators_MinorFree_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:05:27.250191+00:00
-- url     : https://prove2.me/theorems/7cb3ca01-ee5f-4669-ae2e-d74373a8f27a
-- title:
--   Finite graph, minor, metric, cluster, separator, and CSR conventions
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph with $n$ vertices. A separator $S$ is balanced when every component $K$ of $G-S$ satisfies
--   $$4|K|\le 3n.$$
--   Paths include both endpoints. Edge distances and distances between sets take values in $[0,\infty]$, with unreachable pairs and empty source sets at infinite distance. The internal boundary of $R$ consists of its vertices with a neighbour outside $R$. A cluster $K$ has more than $3n/4$ vertices and joins each pair inside $G[K]$ by a path whose full vertex-weight sum is at most $D$.
--
--   Ordinary minors reuse the published branch-set model; induced minors reuse its separately published adjacency-iff version. The once-subdivided clique has an original vertex for each clique vertex and a subdivision vertex for each unordered pair. CSR input permits every neighbour ordering, without duplicate neighbours, and counts each undirected edge once in $m$.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 7–8, 14, 22, Section 2; Theorem 7; Section 6

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_MISInducedMinor_InducedMinorModel

set_option autoImplicit false

open scoped ENNReal

namespace FlowOptimalSeparators.MinorFree

/-- Finite labelled graphs; labels are only an input representation. -/
abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

noncomputable def edges {n : ℕ} (G : Graph n) : Finset (Fin n × Fin n) :=
  by classical exact Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ := (edges G).card

/-- The ordinary branch-set notion, with no prohibition on extra adjacencies. -/
def ExcludesClique {n : ℕ} (G : Graph n) (h : ℕ) : Prop :=
  ¬ RobertsonSeymour1986.GM5.IsMinor (⊤ : Graph h) G

/-- The subdivision vertex is an unordered pair represented by its increasing ordering. -/
abbrev SubdivisionVertex (h : ℕ) := Fin h ⊕ {e : Fin h × Fin h // e.1 < e.2}

def subdivAdj {h : ℕ} : SubdivisionVertex h → SubdivisionVertex h → Prop
  | .inl i, .inr e => i = e.val.1 ∨ i = e.val.2
  | .inr e, .inl i => i = e.val.1 ∨ i = e.val.2
  | _, _ => False

def subdividedClique (h : ℕ) : SimpleGraph (SubdivisionVertex h) where
  Adj := subdivAdj
  symm := ⟨by intro a b hab; cases a <;> cases b <;> exact hab⟩
  loopless := ⟨by intro a; cases a <;> simp [subdivAdj]⟩

def InducedSubdivisionFree {n : ℕ} (G : Graph n) (h : ℕ) : Prop :=
  ¬ MISInducedMinor.IsInducedMinor (subdividedClique h) G

/-- Paths include both endpoints; the singleton is the zero-edge path. -/
def IsSimplePath {n : ℕ} (G : Graph n) (u v : Fin n) (P : List (Fin n)) : Prop :=
  P.head? = some u ∧ P.getLast? = some v ∧ P.Nodup ∧ P.IsChain G.Adj

/-- All lists with at most n vertices, including the empty list. -/
noncomputable def pathLists (n : ℕ) : Finset (List (Fin n)) :=
  (Finset.range (n + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → Fin n)).image List.ofFn

noncomputable def simplePaths {n : ℕ} (G : Graph n) (u v : Fin n) :
    Finset (List (Fin n)) :=
  by classical exact (pathLists n).filter (IsSimplePath G u v)

noncomputable def vertexWeight {n : ℕ} (w : Fin n → ℝ) (P : List (Fin n)) : ℝ :=
  (P.map w).sum

noncomputable def pathLength {n : ℕ} (ℓ : Fin n → Fin n → ℝ≥0∞)
    (P : List (Fin n)) : ℝ≥0∞ :=
  ((P.zip P.tail).map fun e => ℓ e.1 e.2).sum

/-- Complete-lattice infimum: unreachable distance is +infinity, never zero. -/
noncomputable def distance {n : ℕ} (G : Graph n) (ℓ : Fin n → Fin n → ℝ≥0∞)
    (u v : Fin n) : ℝ≥0∞ :=
  ⨅ P ∈ simplePaths G u v, pathLength ℓ P

noncomputable def setDistance {n : ℕ} (G : Graph n) (ℓ : Fin n → Fin n → ℝ≥0∞)
    (X Y : Finset (Fin n)) : ℝ≥0∞ :=
  ⨅ x ∈ X, ⨅ y ∈ Y, distance G ℓ x y

noncomputable def ball {n : ℕ} (G : Graph n) (ℓ : Fin n → Fin n → ℝ≥0∞)
    (X : Finset (Fin n)) (r : ℝ) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (fun v => (⨅ x ∈ X, distance G ℓ x v) ≤ ENNReal.ofReal r)

/-- Internal boundary, rather than the external neighbourhood. -/
noncomputable def boundary {n : ℕ} (G : Graph n) (R : Finset (Fin n)) : Finset (Fin n) :=
  by classical exact R.filter (fun u => ∃ v, v ∉ R ∧ G.Adj u v)

/-- Equivalent to bounding each component of G-S; connected subsets suffice. -/
def Balanced {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Prop :=
  ∀ K : Finset (Fin n), Disjoint K S → (G.induce (K : Set (Fin n))).Connected →
    4 * K.card ≤ 3 * n

noncomputable def weightSum {n : ℕ} (w : Fin n → ℝ) (X : Finset (Fin n)) : ℝ :=
  ∑ v ∈ X, w v

noncomputable def vertexMetric {n : ℕ} (w : Fin n → ℝ) (u v : Fin n) : ℝ≥0∞ :=
  ENNReal.ofReal ((w u + w v) / 2)

/-- Full vertex sums on paths in the induced cluster, including endpoints. -/
def Cluster {n : ℕ} (G : Graph n) (w : Fin n → ℝ) (D : ℝ)
    (K : Finset (Fin n)) : Prop :=
  3 * n < 4 * K.card ∧ ∀ u ∈ K, ∀ v ∈ K,
    ∃ P ∈ simplePaths G u v, (∀ x ∈ P, x ∈ K) ∧ vertexWeight w P ≤ D

/-- Input adjacency arrays may have any neighbour order and count every undirected edge twice. -/
structure AdjacencyInput {n : ℕ} (G : Graph n) where
  rows : Fin n → List (Fin n)
  nodup : ∀ u, (rows u).Nodup
  adjacent : ∀ u v, v ∈ rows u ↔ G.Adj u v

/-- CSR input: n,h,m, n+1 row offsets, then neighbour labels. No graph operation is a RAM primitive. -/
noncomputable def AdjacencyInput.encode {n : ℕ} {G : Graph n} (A : AdjacencyInput G)
    (h : ℕ) : List ℕ :=
  [n, h, edgeCount G] ++
    ((List.range (n + 1)).map fun i =>
      ((List.finRange n).take i |>.map fun u => (A.rows u).length).sum) ++
    (List.finRange n).flatMap (fun u => (A.rows u).map Fin.val)

end FlowOptimalSeparators.MinorFree


