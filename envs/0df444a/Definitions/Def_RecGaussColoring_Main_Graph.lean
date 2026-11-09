-- Prove2me | Definitions.Def_RecGaussColoring_Main_Graph
-- name    : RecGaussColoring_Main_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:24.979698+00:00
-- url     : https://prove2.me/theorems/f60d8e93-e0af-429a-99eb-28051cfe33da
-- title:
--   Graph instances, encodings and coloring outputs
-- statement:
--   An input $I$ consists of a natural number $n$ and a simple undirected graph $G$ on $\{0,\ldots,n-1\}$. The input list records $n$ followed by all $n^2$ adjacency bits in row-major order. The domain of promised inputs is precisely $G$ colorable with three colors. A coloring output is a list of $n$ integers with unequal labels on adjacent vertices, and its color count is the number of distinct labels:
--   $$
--   \operatorname{GoodColoring}(G,o,B)\iff |o|=n,\quad
--   \forall ij\in E(G),\ o_i\ne o_j,\quad |\{o_i:i<n\}|\le B.
--   $$
--   Independent sets use characteristic lists of length $n$, and their neighborhood is the set of vertices adjacent to at least one member. The independent-set output requirement is $|S|\ge Cn^a$, with $C$ and $a$ supplied separately. Minimum and maximum degree are Mathlib's degrees, both zero on the empty graph.
--
--   This module connects finite graph mathematics with the shared integer RAM without restricting graph inputs or color labels.
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Theorems 1.1 and 1.5; Appendix B, pp. 25–26, p. 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Mathlib

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- A labelled input graph; no promise is bundled into the input type. -/
structure Graph3 where
  n : ℕ
  G : SimpleGraph (Fin n)

def graphSize (I : Graph3) : ℕ := I.n

def ThreeColorable (I : Graph3) : Prop := I.G.Colorable 3

/-- Row-major n×n adjacency matrix preceded by n. -/
def encGraph (I : Graph3) : List ℤ := by
  classical
  exact (I.n : ℤ) :: ((List.finRange I.n).flatMap fun i =>
    (List.finRange I.n).map fun j => if I.G.Adj i j then 1 else 0)

def maxDeg (I : Graph3) : ℕ := by classical exact I.G.maxDegree

def minDeg (I : Graph3) : ℕ := by classical exact I.G.minDegree

/-- There is one integer label per vertex; colors are counted without a range restriction. -/
def GoodColoring (I : Graph3) (out : List ℤ) (B : ℝ) : Prop :=
  out.length = I.n ∧
  (∀ i j : Fin I.n, I.G.Adj i j → out.getD i.val 0 ≠ out.getD j.val 0) ∧
  (out.toFinset.card : ℝ) ≤ B

def Independent (I : Graph3) (S : Finset (Fin I.n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ¬I.G.Adj i j

/-- Set-valued neighborhood in the ambient graph. -/
def neighbors (I : Graph3) (S : Finset (Fin I.n)) : Finset (Fin I.n) := by
  classical exact Finset.univ.filter fun j => ∃ i ∈ S, I.G.Adj i j

/-- An exact characteristic-vector decoder. A malformed list never decodes. -/
def DecodesSet (I : Graph3) (out : List ℤ) (S : Finset (Fin I.n)) : Prop :=
  out.length = I.n ∧ ∀ i : Fin I.n, out.getD i.val 0 = if i ∈ S then 1 else 0

/-- The independent-set routine uses the same payload as progress P1. -/
def GoodIndependent (C exponent : ℝ) (I : Graph3) (out : List ℤ) : Prop :=
  ∃ S : Finset (Fin I.n), DecodesSet I out S ∧ Independent I S ∧
    C * (I.n : ℝ) ^ exponent ≤ (S.card : ℝ)

end RecGaussColoring.Main


