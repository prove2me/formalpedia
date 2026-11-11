-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_BushyForest
-- name    : FasterExactColoring_ThreeColor_BushyForest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:54.378999+00:00
-- url     : https://prove2.me/theorems/301ed1af-d054-45b2-b770-2c36d639efff
-- title:
--   Bushy forests, preprocessing and computed structural parameters
-- statement:
--   A bushy forest is an acyclic subgraph, possibly noninduced, with every internal vertex of forest degree at least four and at least one internal vertex per tree. Its maximality means that internal vertices have no outside neighbors, leaves have at most two outside neighbors, and outside vertices have at most three outside neighbors. The modified condition requires each tree touching a residual degree-three vertex through a leaf to be a $K_{1,4}$; it does not preserve the old forest's vertex set.
--
--   Choose one internal root in each tree. Let $R$ be the leaves, $H=G-V(F)$, $S=N_G(R)\cap V(H)$, $T=V(H)\setminus S$, and $D=\{v\in S:\deg_H(v)=3\}$. Then $p,q,r,s,t,d$ count roots, other internal vertices, leaves, $S,T,D$. The value $c$ is the largest number of degree-three vertices in one component of $H$, with $c=0$ when $H$ is empty. A maximal matching $M$ of $G[R]$ has $m=|M|$; maximality is by inclusion, not maximum cardinality.
--
--   All eight parameters are computed from this data:
--   $$a=(p,q,r,s,t,d,c,m).$$
--   The preprocessing predicate records minimum ambient degree at least three, acyclicity of the subgraph induced by ambient degree-three vertices, and a modified maximal bushy forest. Root and matching validity are imposed only at the stage where they occur in the source. These conditions are local hypotheses of supporting results, never hypotheses of the main theorem.
--
--   This interface distinguishes ambient, forest and residual degrees and charges graph, forest, root and matching descriptions.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Section 4.2, pp. 5–6 (PDF pp. 7–8); Eqs. (2)–(5), pp. 6–8 (PDF pp. 8–10)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_GraphInput

namespace FasterExactColoring.ThreeColor

/-- Forest subgraphs need not be induced. Vertices outside verts are isolated. -/
structure ForestData (n : ℕ) where
  verts : Finset (Fin n)
  edges : GraphInput n

def ForestData.leaves {n : ℕ} (F : ForestData n) : Finset (Fin n) :=
  F.verts.filter (fun v => degree F.edges v = 1)

def ForestData.internal {n : ℕ} (F : ForestData n) : Finset (Fin n) :=
  F.verts \ F.leaves

def ForestData.bushy {n : ℕ} (F : ForestData n) (G : GraphInput n) : Prop :=
  F.edges.graph.IsAcyclic ∧
  (∀ u v, F.edges.graph.Adj u v → u ∈ F.verts ∧ v ∈ F.verts ∧ G.graph.Adj u v) ∧
  (∀ v ∈ F.internal, 4 ≤ degree F.edges v) ∧
  (∀ v ∈ F.verts, ∃ u ∈ F.internal, u ∈ component F.edges F.verts v)

def ForestData.outside {n : ℕ} (F : ForestData n) : Finset (Fin n) := vertices \ F.verts

def ForestData.maximal {n : ℕ} (F : ForestData n) (G : GraphInput n) : Prop :=
  F.bushy G ∧
  (∀ v ∈ F.internal, degreeIn G F.outside v = 0) ∧
  (∀ v ∈ F.leaves, degreeIn G F.outside v ≤ 2) ∧
  (∀ v ∈ F.outside, degreeIn G F.outside v ≤ 3)

def ForestData.modified {n : ℕ} (F : ForestData n) (G : GraphInput n) : Prop :=
  F.maximal G ∧ ∀ l ∈ F.leaves, ∀ v ∈ F.outside,
    G.graph.Adj l v → degreeIn G F.outside v = 3 →
    let K := component F.edges F.verts l
    K.card = 5 ∧ (K ∩ F.internal).card = 1

def ForestData.rooted {n : ℕ} (F : ForestData n) (roots : Finset (Fin n)) : Prop :=
  roots ⊆ F.internal ∧ ∀ v ∈ F.verts,
    ∃! a : Fin n, a ∈ roots ∧ a ∈ component F.edges F.verts v

def ForestData.S {n : ℕ} (F : ForestData n) (G : GraphInput n) : Finset (Fin n) :=
  F.outside.filter (fun v => ∃ l ∈ F.leaves, G.graph.Adj l v)

def ForestData.T {n : ℕ} (F : ForestData n) (G : GraphInput n) : Finset (Fin n) :=
  F.outside \ F.S G

def ForestData.D {n : ℕ} (F : ForestData n) (G : GraphInput n) : Finset (Fin n) :=
  (F.S G).filter (fun v => degreeIn G F.outside v = 3)

def ForestData.threeVertices {n : ℕ} (F : ForestData n) (G : GraphInput n) : Finset (Fin n) :=
  F.outside.filter (fun v => degreeIn G F.outside v = 3)

def ForestData.c {n : ℕ} (F : ForestData n) (G : GraphInput n) : ℕ :=
  (F.outside.sort (· ≤ ·)).foldl (fun a v =>
    max a ((component G F.outside v) ∩ F.threeVertices G).card) 0

abbrev Matching (n : ℕ) := Finset (Fin n × Fin n)

def matched {n : ℕ} (M : Matching n) : Finset (Fin n) := M.image Prod.fst ∪ M.image Prod.snd

def maximalMatching {n : ℕ} (G : GraphInput n) (R : Finset (Fin n)) (M : Matching n) : Prop :=
  (∀ e ∈ M, e.1 < e.2 ∧ e.1 ∈ R ∧ e.2 ∈ R ∧ G.graph.Adj e.1 e.2) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint ({e.1,e.2} : Finset (Fin n)) {f.1,f.2}) ∧
  (∀ u ∈ R, ∀ v ∈ R, G.graph.Adj u v → u ∈ matched M ∨ v ∈ matched M)

structure Counts where
  p : ℕ
  q : ℕ
  r : ℕ
  s : ℕ
  t : ℕ
  d : ℕ
  c : ℕ
  m : ℕ

def counts {n : ℕ} (G : GraphInput n) (F : ForestData n)
    (roots : Finset (Fin n)) (M : Matching n) : Counts :=
  ⟨roots.card, (F.internal \ roots).card, F.leaves.card,
    (F.S G).card, (F.T G).card, (F.D G).card, F.c G, M.card⟩

def forestPreprocessed {n : ℕ} (G : GraphInput n) (F : ForestData n) : Prop :=
  (∀ v, 3 ≤ degree G v) ∧ ¬ degreeThreeCycle G ∧ F.modified G

def preprocessed {n : ℕ} (G : GraphInput n) (F : ForestData n)
    (roots : Finset (Fin n)) (M : Matching n) : Prop :=
  forestPreprocessed G F ∧ F.rooted roots ∧ maximalMatching G F.leaves M

def ForestData.code {n : ℕ} (F : ForestData n) : List ℕ :=
  vertexSetCode F.verts ++ graphCode F.edges

def preprocessingCode {n : ℕ} (G : GraphInput n) (F : ForestData n)
    (roots : Finset (Fin n)) (M : Matching n) : List ℕ :=
  graphCode G ++ F.code ++ vertexSetCode roots ++
    [M.card] ++ ((List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u,v)))).flatMap (fun e => if e ∈ M then [e.1.val,e.2.val] else [])

end FasterExactColoring.ThreeColor


