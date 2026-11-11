-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Decompositions
-- name    : FasterExactColoring_ThreeColor_Decompositions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:57.200235+00:00
-- url     : https://prove2.me/theorems/ed199261-8edc-4d36-9d10-caf764538cc6
-- title:
--   Encoded tree and path decompositions with integer width
-- statement:
--   A supplied decomposition consists of a nonempty finite tree or path of finite vertex bags. Validity uses the published general tree-decomposition and path-decomposition predicates: bags cover vertices and edges, and the bags containing a given vertex form a connected subtree or interval. Data and validity are separate, so an algorithm must output the actual decomposition rather than an assumed width bound.
--
--   Width is integer-valued:
--   $$w=\max_i |B_i|-1.$$
--   A one-empty-bag decomposition of the empty graph therefore has width $-1$. Encodings include every bag and, for a tree, the adjacency matrix of its bag tree. Their complete descriptions contribute to input cost.
--
--   The degree-sequence bound is $n_3/6+n_4/3+(13/30)n_5+(23/45)n_6+n_{\ge7}$; the degree-excess bound is $\frac16\sum_v\max\{\deg_G(v)-2,0\}$. Counts and degrees are computed from the graph.
--
--   **Formalization Note** The time envelope uses $(\max\{1,b\})^{\max\{0,w\}}$. This agrees with the source's exponential factor on its ordinary domain and gives the constant-time boundary convention for empty graphs and the zero-color palette. It avoids the undefined expression $0^{-1}$ and a zero runtime allowance for trivial rejection cases.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Section 2, p. 3 (PDF p. 5); Lemmas 3.4–3.7, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_GraphInput
import Definitions.Def_GaussianSweep_IsPathDecomposition
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

namespace FasterExactColoring.ThreeColor

/-- Actual bag sequences; validity reuses the published source-independent predicate. -/
structure PathData (n : ℕ) where
  count : ℕ
  bag : Fin count → Finset (Fin n)

def PathData.valid {n : ℕ} (D : PathData n) (G : GraphInput n) : Prop :=
  GaussianSweep.IsPathDecomposition G.graph D.count D.bag

def bagWidth {n b : ℕ} (bags : Fin b → Finset (Fin n)) : ℤ :=
  ((List.finRange b).foldl (fun a i => max a (bags i).card) 0 : ℕ) - (1 : ℤ)

def PathData.width {n : ℕ} (D : PathData n) : ℤ := bagWidth D.bag

def PathData.code {n : ℕ} (D : PathData n) : List ℕ :=
  D.count :: (List.finRange D.count).flatMap (fun i => vertexSetCode (D.bag i))

structure TreeData (n : ℕ) where
  count : ℕ
  tree : GraphInput count
  bag : Fin count → Finset (Fin n)

def TreeData.valid {n : ℕ} (D : TreeData n) (G : GraphInput n) : Prop :=
  RobertsonSeymour1986.GM5.IsTreeDecomposition G.graph D.tree.graph D.bag

def TreeData.width {n : ℕ} (D : TreeData n) : ℤ := bagWidth D.bag

def TreeData.code {n : ℕ} (D : TreeData n) : List ℕ :=
  graphCode D.tree ++ (List.finRange D.count).flatMap (fun i => vertexSetCode (D.bag i))

noncomputable def degreeSequenceBound {n : ℕ} (G : GraphInput n) : ℝ :=
  (degreeSet G 3).card / 6 + (degreeSet G 4).card / 3 +
  (13/30 : ℝ)*(degreeSet G 5).card + (23/45 : ℝ)*(degreeSet G 6).card +
  (vertices.filter (fun v => 7 ≤ degree G v)).card

noncomputable def degreeExcessBound {n : ℕ} (G : GraphInput n) : ℝ :=
  (∑ v : Fin n, max ((degree G v : ℝ) - 2) 0) / 6

/-- A unit lower envelope handles empty graphs and the zero-color palette.
On positive width and positive palettes this is the printed exponential term. -/
noncomputable def widthFactor (base : ℕ) (width : ℤ) : ℝ :=
  (max 1 (base : ℝ)) ^ (max 0 (width : ℝ))

end FasterExactColoring.ThreeColor


