-- Prove2me | Definitions.Def_DirectedTreeCovers_Strong_Construction
-- name    : DirectedTreeCovers_Strong_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:29.014665+00:00
-- url     : https://prove2.me/theorems/7d25bbb7-bee3-4bd8-8548-c12f8294ec20
-- title:
--   Algorithm 3 radii, tree collection and expanded bunches
-- statement:
--   Start with $R_k=R_{k+1}=\infty$ and process levels $i=k-1,\ldots,0$. For every center $w$, compute $ES(w,R_{i+1})$ from the larger strict pair, then run incoming and outgoing shortest-path searches in the induced subgraph on that expanded set. Omit empty search slots. Update
--
--   $$R_i(v)=\min\left\{\frac{i}{i+1}R_{i+1}(v),\ \min_{w\in A_i\setminus A_{i+1}}r_{ET(w,i+1)}(v,w)\right\}.$$
--
--   The empty minimum and every missing-direction roundtrip are infinity. The output collection consists of all constructed pairs. Define
--
--   $$EB_i(v)=\{w\in A_i\setminus A_{i+1}:v\in ES(w,R_{i+1})\},\qquad EB(v)=\bigcup_{i=0}^{k-1}EB_i(v).$$
--
--   All state, radii, pairs and bunches are computed by the descending fold, with no correctness fields. A partial pivot is defined only when an actual center realizes a finite updated radius. The expected bunch size is its finite sum over atoms of the independent hierarchy law. These objects are the subjects of Lemmas 5.1 and 5.2.
--
--   **Formalization Note** The shrinking coefficient uses real division and extended multiplication. The term $0\cdot\infty$ alone gives no pivot. The two search supports can differ, and membership in an expanded cluster is distinct from membership in a resulting pair.
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, §§5.1–5.3 and Algorithm 3, printed pp.16–18 (PDF pp.17–19)

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Clusters
import Definitions.Def_DirectedTreeCovers_Strong_Hierarchy

noncomputable section

namespace DirectedTreeCovers.Strong

open scoped Classical
open EulerSparsify MeasureTheory
variable {V E : Type} [Fintype V] [Fintype E]

/-- Computed state before a descending level: R_(i+1), R_(i+2), pairs already
constructed, and the union of higher expanded bunches. No correctness fields. -/
structure ConstructionState (V E : Type) where
  radiusNext : V → ENNReal
  radiusAfter : V → ENNReal
  pairs : List (TreePair V E)
  bunch : V → Finset V

def initialState : ConstructionState V E := ⟨fun _ => ⊤, fun _ => ⊤, [], fun _ => ∅⟩

def expandedPair (G : DiGraph V E) (s : ConstructionState V E) (w : V) :
    Option (TreePair V E) := searchPair G (expandedCluster G s.radiusAfter s.radiusNext w) w

/-- Exact real shrinking coefficient, and complete-lattice infimum of center values;
the empty inner minimum is infinity. Algorithm 3 line 11. -/
def updatedRadius (G : DiGraph V E) (k : ℕ) (ω : Coins V k)
    (i : ℕ) (s : ConstructionState V E) (v : V) : ENNReal :=
  min (ENNReal.ofReal ((i : ℝ) / (i + 1 : ℝ)) * s.radiusNext v)
    (⨅ (w : V) (_ : w ∈ centers k ω i), optionRoundtrip G (expandedPair G s w) v w)

/-- A partial pivot: only an actual finite-radius realizing center qualifies.
In particular the shrinking term 0 * infinity alone supplies no pivot at i = 0. -/
def levelPivot (G : DiGraph V E) (k : ℕ) (ω : Coins V k) (i : ℕ)
    (s : ConstructionState V E) (v : V) : Option V :=
  ((centers k ω i).filter fun w => updatedRadius G k ω i s v ≠ ⊤ ∧
    optionRoundtrip G (expandedPair G s w) v w = updatedRadius G k ω i s v).toList.head?

/-- One descending level of the actual Algorithm 3, with no second pruning of ES.
Missing-root searches return empty slots, omitted by filterMap. -/
def constructionStep (G : DiGraph V E) (k : ℕ) (ω : Coins V k)
    (s : ConstructionState V E) (i : ℕ) : ConstructionState V E where
  radiusNext := updatedRadius G k ω i s
  radiusAfter := s.radiusNext
  pairs := s.pairs ++ (centers k ω i).toList.filterMap (expandedPair G s)
  bunch := fun v => s.bunch v ∪ (centers k ω i).filter
    (fun w => v ∈ expandedCluster G s.radiusAfter s.radiusNext w)

/-- Full descending fold; all outputs are functions of the graph and the independent coins. -/
def construction (G : DiGraph V E) (k : ℕ) (ω : Coins V k) : ConstructionState V E :=
  (List.range k).reverse.foldl (constructionStep G k ω) initialState

/-- The source radius R_j, available without assuming any monotonicity or nesting. -/
def radiusAt (G : DiGraph V E) (k : ℕ) (ω : Coins V k) (j : ℕ) : V → ENNReal :=
  (((List.range k).reverse.filter fun i => j ≤ i).foldl
    (constructionStep G k ω) initialState).radiusNext

def algorithmCover (G : DiGraph V E) (k : ℕ) (ω : Coins V k) : List (TreePair V E) :=
  (construction G k ω).pairs

/-- EB(v) is the union of actual expanded-cluster center sets, not an overlap certificate. -/
def expandedBunch (G : DiGraph V E) (k : ℕ) (ω : Coins V k) (v : V) : Finset V :=
  (construction G k ω).bunch v

/-- Finite expectation avoids any nonintegrable-Bochner default. The law is a mass-one
Bernoulli product and every singleton is measurable. -/
def expectedBunch (G : DiGraph V E) (k : ℕ) (v : V) : ℝ :=
  ∑ ω : Coins V k, (hierarchyLaw V k {ω}).toReal * ((expandedBunch G k ω v).card : ℝ)

end DirectedTreeCovers.Strong


