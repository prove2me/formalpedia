-- Prove2me | Definitions.Def_MinCostArbPacking_Main_Supplement_Weighted
-- name    : MinCostArbPacking_Main_Supplement_Weighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:45:43.644734+00:00
-- url     : https://prove2.me/theorems/15599c40-821b-48ec-a867-700b497ad3f5
-- title:
--   Rootless weighted and indegree-bounded inputs, optimal outputs and exact time bounds
-- statement:
--   A rootless weighted input extends the published graph input with arbitrary real costs c(e). The bounded input additionally supplies a natural number b(v) at each vertex. Its feasible subsets satisfy
--
--   $$I\in\mathcal G^k,\qquad \deg_I^{\mathrm{in}}(v)\le b(v)\quad\text{for every }v.$$
--
--   The two output predicates require labels 0 for unselected edges and i+1 for forest i, with a disjoint decomposition into k forests. The selected set must have maximum cardinality among every feasible subset of the original edge set; among all subsets of that cardinality its total cost must be minimum. The undirected output omits only the indegree restrictions. Integer inputs are n,m,k, the endpoint arrays and, for the bounded problem, the bound vector. Real inputs are exactly the cost array; neither advice nor a decomposition is input.
--
--   The runtime functions preserve every term of Theorem 6.1 and (1.2), using L(x)=max{1,log₂ x}. A uniform dilation a makes the two O(m) flow dimensions explicit; the empty-edge branch makes no flow call. These interfaces reuse the published multigraph, interpreter and label decoders.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Theorems 1.2 and 6.1; Eqs. (1.1)–(1.2), p. 2,26–28

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false
noncomputable section
open Classical

namespace MinCostArbPacking.Main.Supplement

/-! Zhou, STOC 2027 submission #1416, Theorems 1.2 and 6.1, pp.2,26–28.
These inputs have no root or advice; output is one charged integer label per original edge. -/

/-- Rootless input: the published multigraph input, together with arbitrary real costs. -/
structure WeightedInput extends DigraphInput where
  c : Fin m → ℝ

/-- Only the costs occupy real input memory. -/
def WeightedInput.inR (X : WeightedInput) : List ℝ := (List.finRange X.m).map X.c

/-- Extra input of Theorem 6.1: a separate natural bound for every vertex. -/
structure BoundedInput extends WeightedInput where
  b : Fin n → ℕ

/-- Bounds follow the published header and the two endpoint arrays. -/
def BoundedInput.inI (X : BoundedInput) : List ℤ :=
  X.toDigraphInput.inI ++ (List.finRange X.n).map (fun v => (X.b v : ℤ))

/-- Feasibility constrains the selected set, not the whole graph. -/
def BoundedInput.Feasible (X : BoundedInput) (I : Finset (Fin X.m)) : Prop :=
  X.G.IndepK X.k I ∧ ∀ v, X.G.inDeg I v ≤ X.b v

/-- Unbounded undirected forest output: a decomposition and lexicographic optimality over all edges. -/
def WeightedOutput (X : WeightedInput) (o : ℕ → ℤ) : Prop :=
  labelsInRange X.k X.m o ∧ X.G.ForestDecomp X.k (decodeSet o) (decodeForests o) ∧
    ∀ J : Finset (Fin X.m), X.G.IndepK X.k J →
      J.card ≤ (decodeSet (m := X.m) o).card ∧
      (J.card = (decodeSet (m := X.m) o).card → cost X.c (decodeSet o) ≤ cost X.c J)

/-- Bounded directed forest output, with the same two optimization priorities and decomposition. -/
def BoundedOutput (X : BoundedInput) (o : ℕ → ℤ) : Prop :=
  labelsInRange X.k X.m o ∧ X.G.ForestDecomp X.k (decodeSet o) (decodeForests o) ∧
    X.Feasible (decodeSet o) ∧
    ∀ J : Finset (Fin X.m), X.Feasible J →
      J.card ≤ (decodeSet (m := X.m) o).card ∧
      (J.card = (decodeSet (m := X.m) o).card → cost X.c (decodeSet o) ≤ cost X.c J)

/-- The full three-term bound from Theorem 6.1. -/
def forestBound (X : DigraphInput) : ℝ :=
  (X.k : ℝ) * X.m * logL (X.k * X.n) +
    (X.k : ℝ) ^ 2 * X.n * logL X.n * logL (X.k * X.n) ^ 2 +
    (X.k : ℝ) ^ 4 * X.n * logL (X.k * X.n) ^ 2

/-- Equation (1.2); a is a uniform dilation of the network dimensions.
The empty-edge instance needs no flow call. The explicit n terms pay for isolated vertices. -/
def undirectedBound (MCF : ℕ → ℕ → ℝ) (a : ℕ) (X : DigraphInput) : ℝ :=
  (if X.m = 0 then 0 else (X.k : ℝ) * logL (X.k * X.n) * MCF (a * X.m) (a * X.m)) +
    (X.k : ℝ) ^ 3 * X.n * logL X.n * logL (X.k * X.n) ^ 3 +
    (X.k : ℝ) ^ 5 * X.n * logL (X.k * X.n) ^ 3

end MinCostArbPacking.Main.Supplement


