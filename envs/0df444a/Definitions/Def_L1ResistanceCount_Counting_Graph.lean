-- Prove2me | Definitions.Def_L1ResistanceCount_Counting_Graph
-- name    : L1ResistanceCount_Counting_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:57.690754+00:00
-- url     : https://prove2.me/theorems/2fcc6110-3229-4c73-99c1-af36b143075b
-- title:
--   Labelled graph adapter, independent tree sum, and sparse counting input
-- statement:
--   The graph type is an alias of the published positive-real-weight multigraph, with vertices labelled by $\{0,\ldots,n-1\}$ and edges by $\{0,\ldots,m-1\}$. It permits parallel labels. A set of edge labels is a spanning tree when it connects all vertices and has exactly $n-1$ edges. Define its total weighted spanning-tree sum independently of a determinant by
--
--   $$T(G)=\sum_{\tau\text{ spanning tree}}\prod_{e\in\tau}w_e.$$
--
--   The empty tree on a singleton has weight one; a disconnected graph has tree weight zero. Pair resistance uses the published Moore–Penrose inverse. The dynamic-range condition is the pairwise inequality $w_e\le n^a w_f$ for every edge pair, equivalent to $w_{\max}/w_{\min}\le n^a$ on a nontrivial connected graph. It is vacuous on the edgeless singleton.
--
--   The RAM input consists only of the graph's sparse edge list and the requested accuracy. Its initial memory contains no tree sum, determinant, optimizer, or oracle answer. The accuracy predicate reads the actual scalar output of a halting execution. The time expression makes the paper's polylogarithmic convention explicit.
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), §1 p.1, Theorem 1.1 and Definition 1.2 p.2, §2 pp.3–4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs
import Definitions.Def_L1ResistanceCount_Counting_ArithmeticRAM

open scoped BigOperators

namespace L1ResistanceCount.Counting

abbrev WeightedGraph (n m : ℕ) := EffResSparsify.Sampling.WGraph (Fin n) (Fin m)

/-- Connectedness of the selected labelled edges; parallel labels remain distinct. -/
def TreeEdges {n m : ℕ} (G : WeightedGraph n m) (t : Finset (Fin m)) : Prop :=
  t.card + 1 = n ∧
    (SimpleGraph.fromRel (fun u v => ∃ e ∈ t, G.head e = u ∧ G.tail e = v)).Connected

/-- The weighted spanning-tree sum, independent of any determinant or algorithm.
At one vertex the unique empty tree has product one. For disconnected graphs the
sum is zero; no success-conditioned output graph type is used. -/
noncomputable def treeWeight {n m : ℕ} (G : WeightedGraph n m) : ℝ := by
  classical
  exact ∑ t : Finset (Fin m), if TreeEdges G t then ∏ e ∈ t, G.w e else 0

abbrev laplacian {n m : ℕ} (G : WeightedGraph n m) := G.laplacian

noncomputable def pairResistance {n m : ℕ} (G : WeightedGraph n m) (s t : Fin n) : ℝ :=
  G.lapPinv s s - G.lapPinv s t - G.lapPinv t s + G.lapPinv t t

/-- Ratio bounds expressed without a minimum on the empty edge set. On a
nontrivial connected graph this is exactly wmax/wmin ≤ n^a; on a singleton it
is vacuous, preserving the exact empty-tree branch at every real scale. -/
def PolynomialWeightRange {n m : ℕ} (G : WeightedGraph n m) (a : ℝ) : Prop :=
  ∀ e f, G.w e ≤ Real.rpow (n : ℝ) a * G.w f

/-- Sparse edge-list input. n,m and endpoint labels are natural cells; ε and
positive weights are real cells. Initial tapes and all other cells are zero.
Program execution, not this mathematical serialization, pays to scan the input. -/
def graphInput {n m : ℕ} (G : WeightedGraph n m) (ε : ℝ) : MachineState where
  naturals := fun i =>
    if i = 0 then n else if i = 1 then m else
    let e := (i - 2) / 2
    if h : e < m then
      if (i - 2) % 2 = 0 then (G.head ⟨e,h⟩).val else (G.tail ⟨e,h⟩).val
    else 0
  reals := fun i => if i = 0 then ε else
    if h : i - 1 < m then G.w ⟨i - 1,h⟩ else 0

/-- The actual scalar output is real cell zero of a halting execution. -/
def AccurateCount {n m : ℕ} (G : WeightedGraph n m) (ε : ℝ) (out : MachineState) : Prop :=
  (1 - ε) * treeWeight G ≤ out.reals 0 ∧ out.reals 0 ≤ (1 + ε) * treeWeight G

/-- One explicit representative of the paper's Õ convention; C and q must be
quantified before all input instances. -/
noncomputable def countingTimeBound (C : ℝ) (q n m : ℕ) (ε : ℝ) : ℝ :=
  C * ((m : ℝ) + Real.rpow (n : ℝ) (3 / 2 : ℝ) / ε) *
    (1 + Real.log (2 + (n : ℝ) + (m : ℝ) + 1 / ε)) ^ q

end L1ResistanceCount.Counting


