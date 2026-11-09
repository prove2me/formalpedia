-- Prove2me | Definitions.Def_GirthFiltering_RandomFiltering_CycleModel
-- name    : GirthFiltering_RandomFiltering_CycleModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:25.56611+00:00
-- url     : https://prove2.me/theorems/6484215e-bd2e-4fd8-b8b9-79481e2107ff
-- title:
--   Weighted cycles, extended girth, and exponential filtering
-- statement:
--   Let $G$ be a finite network with $n$ vertices, $m$ separately identified edges, endpoint maps, and real edge weights $\ell(e)$. The reused carrier permits loops and parallel edges. Admissible input is undirected, has nonnegative weights, and has no isolated vertices; it need not be connected. A cycle consists of a positive number of distinct edges and vertices, with successive incidences closing cyclically. Its weight is the sum of its edge weights. Define
--
--   $$
--   g(G)=\inf_{C\text{ a cycle}}\sum_{e\in C}\ell(e),\qquad
--   T(G,X)=\sup_{C\text{ a cycle}}\min_{e\in C}X_e.
--   $$
--
--   Girth is $+\infty$ for a forest, and its threshold is $-\infty$. The survival event is that at least one complete cycle has all labels at least $t$. For positive weights the joint label law is the finite product of independent exponential measures of rates $\ell(e)$. For nonnegative input, zero edges have unused deterministic zero coordinates; zero-edge contraction is specified by extending their threshold labels to $+\infty$.
--
--   These definitions supply actual weighted-cycle semantics and continuous laws. They do not assume an estimator or a probability bound. The imported network's connectivity and real-valued distance functions are unused; neither adds a condition to this carrier.
--
--   **Formalization Note** Vertex and edge indices are finite types. Girth uses extended nonnegative reals, and bottlenecks and thresholds use extended reals. Their complete-lattice extrema have the specified empty-family values; no real empty supremum is used.
-- source:
--   Yablon, Approximating the Girth of an Undirected, Weighted Graph for Larger Approximation Factors, STOC 2027 submission #59 (2026), pinned PDF sha256 cf63df259cbd099089184755e2c32f0d51f00dea322509f35766f4a91a4e021f, pp. 2–3, Section 1.2; p. 3, Section 2, displayed formula T = sup{t | Ht has a cycle}; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/59.pdf

import Mathlib
import Definitions.Def_VehicleRoutingSurvey_Routing_Network
open scoped ENNReal

namespace GirthFiltering.RandomFiltering

abbrev WeightedGraph := VehicleRoutingSurvey.Routing.Network

def Admissible (G : WeightedGraph) : Prop :=
  VehicleRoutingSurvey.Routing.Undirected G ∧
  VehicleRoutingSurvey.Routing.Nonnegative G ∧
  ∀ v : Fin G.n, ∃ e : Fin G.q, G.tail e = v ∨ G.head e = v

/-- An edge-labeled simple cycle, with a cyclic list of vertices.
Loops and two distinct parallel edges give cycles of lengths one and two. -/
structure Cycle (G : WeightedGraph) where
  length : ℕ
  positive : 0 < length
  vertex : Fin length → Fin G.n
  edge : Fin length → Fin G.q
  vertices_distinct : Function.Injective vertex
  edges_distinct : Function.Injective edge
  incident : ∀ i : Fin length,
    let j : Fin length := ⟨(i.val + 1) % length, Nat.mod_lt _ positive⟩
    (G.tail (edge i) = vertex i ∧ G.head (edge i) = vertex j) ∨
    (G.head (edge i) = vertex i ∧ G.tail (edge i) = vertex j)

def cycleWeight {G : WeightedGraph} (C : Cycle G) : ℝ :=
  ∑ i : Fin C.length, G.weight (C.edge i)

/-- Complete-lattice infimum: the empty cycle family has value +infinity. -/
noncomputable def girth (G : WeightedGraph) : ℝ≥0∞ :=
  ⨅ C : Cycle G, ENNReal.ofReal (cycleWeight C)

def HasCycle (G : WeightedGraph) : Prop := Nonempty (Cycle G)

def PositiveWeights (G : WeightedGraph) : Prop := ∀ e, 0 < G.weight e

/-- The event that the filtering graph retains at least one whole cycle. -/
def Survives (G : WeightedGraph) (X : Fin G.q → ℝ) (t : ℝ) : Prop :=
  ∃ C : Cycle G, ∀ i : Fin C.length, t ≤ X (C.edge i)

/-- The source's supremum over filtering levels, in a type representing -infinity. -/
noncomputable def filterThreshold (G : WeightedGraph) (X : Fin G.q → ℝ) : EReal :=
  sSup {u : EReal | ∃ t : ℝ, Survives G X t ∧ u = (t : EReal)}

noncomputable def bottleneck {G : WeightedGraph} (C : Cycle G)
    (X : Fin G.q → EReal) : EReal :=
  ⨅ i : Fin C.length, X (C.edge i)

/-- The empty cycle family has value -infinity, without totalizing a real supremum. -/
noncomputable def criticalThreshold (G : WeightedGraph) (X : Fin G.q → EReal) : EReal :=
  ⨆ C : Cycle G, bottleneck C X

/-- Actual independent continuous rate-weight exponential labels. -/
noncomputable def labelLaw (G : WeightedGraph) : MeasureTheory.Measure (Fin G.q → ℝ) :=
  MeasureTheory.Measure.pi (fun e => ProbabilityTheory.expMeasure (G.weight e))

/-- Zero edges are not sampled; the dirac coordinates are unused by the program. -/
noncomputable def inputLabelLaw (G : WeightedGraph) :
    MeasureTheory.Measure (Fin G.q → ℝ) := by
  classical
  exact MeasureTheory.Measure.pi (fun e =>
    if 0 < G.weight e then ProbabilityTheory.expMeasure (G.weight e)
    else MeasureTheory.Measure.dirac 0)

/-- Contracting a zero-edge forest is equivalent to giving those edges infinite labels. -/
noncomputable def zeroExtendedLabels (G : WeightedGraph) (X : Fin G.q → ℝ) :
    Fin G.q → EReal := by
  classical
  exact fun e => if G.weight e = 0 then ⊤ else (X e : EReal)

end GirthFiltering.RandomFiltering


