-- Prove2me | Definitions.Def_FreeUniformSpanningForest
-- name    : FreeUniformSpanningForest
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.177336+00:00
-- url     : https://prove2.me/theorems/05887987-de11-4b30-ab2c-5f58544f15d5
-- statement:
--   This block sets up the Problem 336 framework for the free uniform spanning forest (FUSF) on countable graphs with vertex set ℕ. A GraphCode is a symmetric, loopless adjacency relation on ℕ (a Boolean matrix), an EdgeCode is a pair (u,v) with u<v, and an EdgeConfiguration is a Boolean assignment to all edges (a subgraph). Graph connectedness means any two vertices are joined by a chain of adjacencies, and local finiteness means each vertex has finitely many neighbours. A FactorRule Φ takes a graph, a real label for each vertex, and an edge, and returns a Boolean saying whether the edge is chosen; it is Borel if jointly measurable in these inputs, and equivariant if relabelling vertices by any permutation σ of ℕ (transporting the graph, labels and edge) leaves its output unchanged. For a finite subgraph code K (a vertex finset with an edge finset), TreeOn K T means T is a set of edges of K with |T|+1 = |vertices| that connects all vertices of K, i.e. a spanning tree; ustCylinder(K,A,B) is the fraction of spanning trees of K containing every edge of A and avoiding every edge of B, the uniform spanning tree cylinder probability. A finite connected subgraph of G is nonempty, uses only edges of G, and is connected, and a connected exhaustion is an increasing sequence of such subgraphs that eventually contains every edge of G. The measure uniform01 is Lebesgue measure on [0,1]; IsVertexIID P U says the vertex labels are measurable and independent, each uniform on [0,1]. HasFUSFLaw G P X says each edge indicator of the random configuration X is measurable and that, for every connected exhaustion and all finite edge sets A and B, the finite-volume cylinder probabilities ustCylinder(Hₙ,A,B) converge to the probability that X includes all edges of A and excludes all edges of B. Finally, WorksOnGraph Φ G is the defined proposition that, if G is connected and locally finite, then for every probability-space setup with i.i.d. uniform vertex labels, the configuration obtained by applying Φ to G and the labels has the FUSF law. No theorem asserting that such a rule exists is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FreeUniformSpanningForest.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FreeUniformSpanningForest.lean; bytes 16..4360
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem336

abbrev GraphCode :=
  {a : ℕ → ℕ → Bool //
    (∀ u, a u u = false) ∧ (∀ u v, a u v = a v u)}

abbrev EdgeCode := {p : ℕ × ℕ // p.1 < p.2}

abbrev EdgeConfiguration := EdgeCode → Bool

abbrev FactorRule := GraphCode → (ℕ → ℝ) → EdgeCode → Bool

abbrev FiniteSubgraphCode := Finset ℕ × Finset (ℕ × ℕ)

def Adj (G : GraphCode) (u v : ℕ) : Prop := G.1 u v = true

def GraphConnected (G : GraphCode) : Prop :=
  ∀ u v, Relation.ReflTransGen (fun x y => Adj G x y) u v

def GraphLocallyFinite (G : GraphCode) : Prop :=
  ∀ u, Set.Finite {v : ℕ | Adj G u v}

def mkEdge (u v : ℕ) (h : u ≠ v) : EdgeCode := by
  by_cases huv : u < v
  · exact ⟨(u, v), huv⟩
  · exact ⟨(v, u), lt_of_le_of_ne (Nat.le_of_not_gt huv) (Ne.symm h)⟩

def rawPair (u v : ℕ) : ℕ × ℕ :=
  if u < v then (u, v) else (v, u)

def relabelGraph (σ : Equiv ℕ ℕ) (G : GraphCode) : GraphCode :=
  ⟨fun u v => G.1 (σ.symm u) (σ.symm v), by
    constructor
    · intro u
      exact G.2.1 (σ.symm u)
    · intro u v
      exact G.2.2 (σ.symm u) (σ.symm v)⟩

def relabelLabels (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) : ℕ → ℝ :=
  fun u => U (σ.symm u)

def mapEdge (σ : Equiv ℕ ℕ) (e : EdgeCode) : EdgeCode :=
  mkEdge (σ e.1.1) (σ e.1.2) (by
    intro h
    apply Nat.ne_of_lt e.2
    exact σ.injective h)

def RuleBorel (Phi : FactorRule) : Prop :=
  Measurable
    (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) =>
      Phi q.1 q.2.1 q.2.2)

def RuleEquivariant (Phi : FactorRule) : Prop :=
  ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
    Phi (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) =
      Phi G U e

def TreeAdj (T : Finset (ℕ × ℕ)) (u v : ℕ) : Prop :=
  rawPair u v ∈ T

def SubgraphAdj (K : FiniteSubgraphCode) (u v : ℕ) : Prop :=
  u ∈ K.1 ∧ v ∈ K.1 ∧ rawPair u v ∈ K.2

def TreeOn (K : FiniteSubgraphCode)
    (T : Finset (ℕ × ℕ)) : Prop :=
  T ⊆ K.2 ∧
  T.card + 1 = K.1.card ∧
  ∀ u ∈ K.1, ∀ v ∈ K.1,
    Relation.ReflTransGen (TreeAdj T) u v

def spanningTrees (K : FiniteSubgraphCode) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact K.2.powerset.filter (TreeOn K)

def ustCylinder (K : FiniteSubgraphCode)
    (A B : Finset EdgeCode) : ℝ≥0∞ := by
  classical
  let all := spanningTrees K
  let good := all.filter (fun T =>
    (∀ e ∈ A, e.1 ∈ T) ∧ (∀ e ∈ B, e.1 ∉ T))
  exact (good.card : ℝ≥0∞) / (all.card : ℝ≥0∞)

def IsFiniteConnectedSubgraph
    (G : GraphCode) (K : FiniteSubgraphCode) : Prop :=
  K.1.Nonempty ∧
  (∀ p ∈ K.2,
    p.1 ∈ K.1 ∧ p.2 ∈ K.1 ∧ p.1 < p.2 ∧ Adj G p.1 p.2) ∧
  ∀ u ∈ K.1, ∀ v ∈ K.1,
    Relation.ReflTransGen (SubgraphAdj K) u v

def IsConnectedExhaustion
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode) : Prop :=
  (∀ n, IsFiniteConnectedSubgraph G (H n)) ∧
  (∀ n, (H n).1 ⊆ (H (n + 1)).1 ∧
    (H n).2 ⊆ (H (n + 1)).2) ∧
  (∀ u v, u < v → Adj G u v →
    ∃ n, (u, v) ∈ (H n).2)

def uniform01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def IsVertexIID {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (U : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Measurable (U i)) ∧
  ∀ (s : Finset ℕ) (A : ℕ → Set ℝ),
    (∀ i ∈ s, MeasurableSet (A i)) →
    P {ω | ∀ i ∈ s, U i ω ∈ A i} =
      Finset.prod s (fun i => uniform01 (A i))

def HasFUSFLaw {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (P : Measure Ω)
    (X : Ω → EdgeConfiguration) : Prop :=
  (∀ e, Measurable (fun ω => X ω e)) ∧
  ∀ (H : ℕ → FiniteSubgraphCode), IsConnectedExhaustion G H →
    ∀ (A B : Finset EdgeCode),
      Filter.Tendsto
        (fun n => ustCylinder (H n) A B)
        Filter.atTop
        (nhds (P {ω |
          (∀ e ∈ A, X ω e = true) ∧
          (∀ e ∈ B, X ω e = false)}))

def WorksOnGraph (Phi : FactorRule) (G : GraphCode) : Prop :=
  GraphConnected G → GraphLocallyFinite G →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (U : ℕ → Ω → ℝ),
    IsVertexIID P U →
    HasFUSFLaw G P
      (fun ω e => Phi G (fun v => U v ω) e)



end Problem336
end
end OAI


