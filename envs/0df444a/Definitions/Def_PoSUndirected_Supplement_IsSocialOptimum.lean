-- Prove2me | Definitions.Def_PoSUndirected_Supplement_IsSocialOptimum
-- name    : PoSUndirected_Supplement_IsSocialOptimum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:29:20.299695+00:00
-- url     : https://prove2.me/theorems/01a1377d-310d-490f-8083-db3dbad0e4ef
-- title:
--   Optima, cheapest equilibria, strict and approximate equilibria, feasible forests and ordinary price of stability
-- statement:
--   For a finite undirected network-design game, this interface defines the graph and profile notions used by the supplement: looplessness, physical connectivity, demand-feasible forests and their unique-path profiles, social cost, socially optimal profiles, cheapest weak equilibria, strict equilibria, multiplicative approximate equilibria, global Rosenthal-potential minima, host bridges and minimum spanning trees.
--
--   The relation `OrdinaryPoSValue(G,c,q)` says that a socially optimal profile and a cheapest equilibrium attain positive costs $\mathrm{OPT}>0$ and $C(N)$ with $q=C(N)/\mathrm{OPT}$. Requiring the positive optimum explicitly prevents division by zero from assigning a spurious ordinary price of stability.
--
--   This layer is shared by all six supplement theorems.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §2, pp.2–3 (PDF pp.4–5)

import Mathlib
import Definitions.Def_PoSUndirected_ndGame

open CongestionPoA.AsymSum PriceOfStability.Harmonic

set_option autoImplicit false

namespace PoSUndirected.Supplement

variable {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype ι] [DecidableEq ι]

/-!
# Common finite-game and graph predicates for the supplement

Tsoufis, *The Price of Stability in Undirected Network Design: Lower Bounds and Structural
Guarantees* (preprint, sha256 c095d811…), §2, pp.2–3 (PDF pp.4–5).

All social costs below use the paper's constant physical edge cost, even though the published
`designCost` interface permits a cost depending on the load.  The predicates are relational so no
`sInf`/division default can manufacture an optimum or an ordinary price of stability.
-/

/-- The physical multigraph is loopless: no edge has the same endpoint twice. -/
def IsLoopless (ends : E → Sym2 V) : Prop :=
  ∀ (e : E) (v : V), ends e ≠ s(v, v)

/-- The edge set supporting a profile. -/
def profileSupport (P : ι → Finset E) : Finset E :=
  Finset.univ.biUnion P

/-- The vertices incident with an edge of `A`. -/
def incidentVertices (ends : E → Sym2 V) (A : Finset E) : Finset V :=
  Finset.univ.filter fun v ↦ ∃ e ∈ A, v ∈ ends e

/-- The finite host is connected by physical simple paths. -/
def IsConnectedHost (ends : E → Sym2 V) : Prop :=
  ∀ u v : V, ∃ P : Finset E, IsSimplePathEdges ends u v P

/-- `F` is a demand-feasible forest: it is acyclic and contains a path for every demand pair. -/
def IsFeasibleForest (ends : E → Sym2 V) (s t : ι → V) (F : Finset E) : Prop :=
  IsAcyclicEdges ends F ∧ ∀ i : ι, ∃ P ⊆ F, IsSimplePathEdges ends (s i) (t i) P

/-- `P` is the unique-path profile induced by the feasible forest `F` (uniqueness follows from
acyclicity): every player's path is legal and lies in `F`. -/
def IsForestProfile (ends : E → Sym2 V) (s t : ι → V) (F : Finset E)
    (P : ι → Finset E) : Prop :=
  IsFeasibleForest ends s t F ∧ IsProfile (ndGame ends (fun _ ↦ 0) s t) P ∧ ∀ i, P i ⊆ F

/-- Social cost for constant real physical edge costs. -/
noncomputable def socialCost (c : E → ℝ) (P : ι → Finset E) : ℝ :=
  designCost (fun e _ ↦ c e) P

/-- A socially optimal profile: a legal profile of minimum physical support cost. -/
def IsSocialOptimum (G : CongestionGame ι E) (c : E → ℝ) (P : ι → Finset E) : Prop :=
  IsProfile G P ∧ ∀ Q : ι → Finset E, IsProfile G Q → socialCost c P ≤ socialCost c Q

/-- A cheapest weak equilibrium, so its cost is the numerator of ordinary price of stability. -/
def IsCheapestEquilibrium (G : CongestionGame ι E) (c : E → ℝ)
    (P : ι → Finset E) : Prop :=
  IsPureNash G P ∧ ∀ Q : ι → Finset E, IsPureNash G Q → socialCost c P ≤ socialCost c Q

/-- Strict equilibrium: every different unilateral strategy costs strictly more. -/
def IsStrictEquilibrium (G : CongestionGame ι E) (P : ι → Finset E) : Prop :=
  IsProfile G P ∧ ∀ (i : ι) (S : Finset E), S ∈ G.strategies i → S ≠ P i →
    cost G P i < cost G (Function.update P i S) i

/-- Multiplicative `α`-approximate equilibrium, with `α ≥ 1` as in §5. -/
def IsApproxEquilibrium (G : CongestionGame ι E) (α : ℝ) (P : ι → Finset E) : Prop :=
  1 ≤ α ∧ IsProfile G P ∧ ∀ (i : ι) (S : Finset E), S ∈ G.strategies i →
    cost G P i ≤ α * cost G (Function.update P i S) i

/-- A global minimum of Rosenthal's harmonic potential among legal profiles. -/
def IsGlobalPotentialMinimum (G : CongestionGame ι E) (P : ι → Finset E) : Prop :=
  IsProfile G P ∧ ∀ Q : ι → Finset E, IsProfile G Q → potential G P ≤ potential G Q

/-- `q` is the ordinary price of stability of a finite game: an optimum and a cheapest equilibrium
attain the denominator and numerator, the optimum is positive, and `q` is their quotient. -/
def OrdinaryPoSValue (G : CongestionGame ι E) (c : E → ℝ) (q : ℝ) : Prop :=
  ∃ (O N : ι → Finset E), IsSocialOptimum G c O ∧ IsCheapestEquilibrium G c N ∧
    0 < socialCost c O ∧ q = socialCost c N / socialCost c O

/-- An edge is a bridge of the full physical host iff it lies on no physical cycle. -/
def IsHostBridge (ends : E → Sym2 V) (e : E) : Prop :=
  ∀ C : Finset E, IsCycleEdges ends C → e ∉ C

/-- A minimum spanning tree for the positive physical cost function `c`. -/
def IsMinimumSpanningTree (ends : E → Sym2 V) (c : E → ℝ) (T : Finset E) : Prop :=
  IsSpanningTree ends T ∧ ∀ T' : Finset E, IsSpanningTree ends T' →
    ∑ e ∈ T, c e ≤ ∑ e ∈ T', c e

/-- A forest contained in at least one physical minimum spanning tree. -/
def IsForestInMinimumSpanningTree (ends : E → Sym2 V) (c : E → ℝ) (F : Finset E) : Prop :=
  IsAcyclicEdges ends F ∧ ∃ T : Finset E, IsMinimumSpanningTree ends c T ∧ F ⊆ T

end PoSUndirected.Supplement


