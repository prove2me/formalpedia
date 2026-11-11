-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Graph
-- name    : InducedExpanderTest989_Structural_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:56:22.577203+00:00
-- url     : https://prove2.me/theorems/a1432ba8-f756-4c7a-856b-a1a6f5ebfb1d
-- title:
--   Bounded-degree graphs, adjacency lists and induced conductance
-- statement:
--   Let G be a simple undirected graph on n labeled vertices with degree bound d. An adjacency list lists every neighbor once in an initial segment of d slots and returns a null answer afterward; every ordering is allowed. For disjoint sets S,T, E(S,T) counts edges between them. For a nonempty U, the inner conductance is
--   $$\Phi_{\rm in}(G[U])=\min_{S\subseteq U,\ 0<|S|\le |U|/2}\frac{|E(S,U\setminus S)|}{d|S|},$$
--   with value 1 for a singleton. The class P_{α,ϕ} consists of graphs having some U with |U|≥αn and inner conductance at least ϕ. The lazy walk moves along each adjacent edge with probability 1/(2d) and holds with probability 1−deg(x)/(2d). Components meeting U and partition crossing edges supply the analysis vocabulary.
--
--   **Formalization Note** Vertices and slots use Fin n and Fin d, the null answer is none, and the empty set has inner conductance 0. Cut edges are counted from the first disjoint side to the second, while interpart edges are counted once using the label order. These definitions establish the source model; no sparse boundary is required.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.3 (PDF p.5), Definitions 1.1–1.2; §1.1 p.2; §3 p.13; §4.2.1 p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

/-- The graph is separate from its arbitrary valid adjacency-list ordering (§1.1). -/
abbrev Oracle (n d : ℕ) := Fin n → Fin d → Option (Fin n)

def IsAdjacencyList {n d : ℕ} (G : SimpleGraph (Fin n)) (O : Oracle n d) : Prop :=
  ∀ v, ∃ r : ℕ, r ≤ d ∧
    (∀ i, (O v i).isSome ↔ i.val < r) ∧
    (∀ i j w, O v i = some w → O v j = some w → i = j) ∧
    (∀ w, G.Adj v w ↔ ∃ i, O v i = some w)

/-- Ordered from S to T; when disjoint this counts each undirected cut edge once. -/
def cutEdges {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) : ℕ := by
  classical
  exact ((S ×ˢ T).filter fun xy => G.Adj xy.1 xy.2).card

/-- Empty-set convention 0; singleton convention 1; all other minima are finite. -/
def innerConductance {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) : ℝ := by
  classical
  exact if U.card = 0 then 0 else if U.card = 1 then 1 else
    sInf {r : ℝ | ∃ S : Finset (Fin n), S ⊆ U ∧ 0 < S.card ∧
      2 * S.card ≤ U.card ∧ r = (cutEdges G S (U \ S) : ℝ) / (d * (S.card : ℝ))}

def HasCore {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (α ϕ : ℝ) : Prop :=
  ∃ U : Finset (Fin n), α * n ≤ (U.card : ℝ) ∧ ϕ ≤ innerConductance d G U

def DegreeBound {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ d

/-- The walk of §3: fixed-bound normalization, including holding probability. -/
def graphWalk {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun x y => if x = y then 1 - (G.neighborSet x).ncard / (2 * (d : ℝ))
    else if G.Adj x y then 1 / (2 * (d : ℝ)) else 0

/-- Components meeting U; under the trace preamble this is the single C_U. -/
def coreComponent {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun z => ∃ x ∈ U, G.Reachable x z

/-- A partition is encoded by a label for every vertex; unused labels are harmless. -/
def part {n s : ℕ} (C : Fin n → Fin s) (i : Fin s) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => C x = i

def crossEdges {n s : ℕ} (G : SimpleGraph (Fin n)) (C : Fin n → Fin s) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n × Fin n)).filter
    fun xy => xy.1 < xy.2 ∧ G.Adj xy.1 xy.2 ∧ C xy.1 ≠ C xy.2).card

def partitionLevels (α₀ : ℝ) : ℕ := ⌊Real.log (1 / α₀) / Real.log 2⌋₊ + 1

end InducedExpanderTest989.Structural


