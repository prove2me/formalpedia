-- Prove2me | Definitions.Def_DirectedTreeCovers_Strong_Supplement_Roundtrip
-- name    : DirectedTreeCovers_Strong_Supplement_Roundtrip
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:53:50.484179+00:00
-- url     : https://prove2.me/theorems/848f5ec0-63e8-4e5d-b18f-36095c329b01
-- title:
--   Algorithm 2 strict-cluster roundtrip construction
-- statement:
--   Start with radius infinity and process the independently sampled levels in descending order. Each center runs the published shortest-path searches in its strict cluster; empty-root slots are omitted. The next radius is the minimum of the current radius and all actual center roundtrips, with no shrinking factor. Level bunches count roots whose strict clusters contain the vertex, and their total is their union. A roundtrip cover uses one pair for both directions and retains the extended-distance inequality on every pair. The same pair must contain both endpoints whenever their graph roundtrip is finite.
--
--   These computed states and predicates supply the actual Algorithm 2 objects for Lemmas 4.1–4.2, without assuming any stretch, nesting or overlap conclusion. Zero weights use the published minimum-hop shortest trees.
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), §§4.1–4.3, Algorithms 1–2, printed pp.12–15 (PDF pp.13–16); §2 SCC convention, printed p.6 (PDF p.7).

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Clusters
import Definitions.Def_DirectedTreeCovers_Strong_Hierarchy

noncomputable section

namespace DirectedTreeCovers.Strong.Supplement

open scoped Classical
open EulerSparsify MeasureTheory

variable {V E : Type} [Fintype V] [Fintype E]

/-- Algorithm 2 (printed pp.12–13 / PDF pp.13–14): a descending state,
with no shrinking term, no nesting assumptions, and no correctness fields. -/
structure RoundtripState (V E : Type) where
  radius : V → ENNReal
  pairs : List (TreePair V E)
  bunch : V → Finset V

def roundtripInitial : RoundtripState V E :=
  ⟨fun _ => ⊤, [], fun _ => ∅⟩

/-- Actual two shortest-path searches in the published strict cluster. Missing-root
slots are absent, including the empty cluster when the root has radius zero. -/
def strictPair (G : DiGraph V E) (s : RoundtripState V E) (w : V) :
    Option (TreePair V E) :=
  searchPair G (strictCluster G s.radius w) w

/-- Algorithm 2 line 12; the minimum over no centers is infinity. -/
def roundtripUpdate (G : DiGraph V E) (k : ℕ) (ω : Coins V k)
    (i : ℕ) (s : RoundtripState V E) (v : V) : ENNReal :=
  min (s.radius v)
    (⨅ (w : V) (_ : w ∈ centers k ω i), optionRoundtrip G (strictPair G s w) v w)

def roundtripStep (G : DiGraph V E) (k : ℕ) (ω : Coins V k)
    (s : RoundtripState V E) (i : ℕ) : RoundtripState V E where
  radius := roundtripUpdate G k ω i s
  pairs := s.pairs ++ (centers k ω i).toList.filterMap (strictPair G s)
  bunch := fun v => s.bunch v ∪
    (centers k ω i).filter (fun w => v ∈ strictCluster G s.radius w)

/-- State immediately before processing level i. Higher levels have actually run. -/
def roundtripBefore (G : DiGraph V E) (k : ℕ) (ω : Coins V k)
    (i : ℕ) : RoundtripState V E :=
  ((List.range k).reverse.filter (fun j => i < j)).foldl
    (roundtripStep G k ω) roundtripInitial

def roundtripConstruction (G : DiGraph V E) (k : ℕ) (ω : Coins V k) :
    RoundtripState V E :=
  (List.range k).reverse.foldl (roundtripStep G k ω) roundtripInitial

def strictBunchAt (G : DiGraph V E) (k : ℕ) (ω : Coins V k)
    (i : ℕ) (v : V) : Finset V :=
  (centers k ω i).filter
    (fun w => v ∈ strictCluster G (roundtripBefore G k ω i).radius w)

def strictBunch (G : DiGraph V E) (k : ℕ) (ω : Coins V k) (v : V) : Finset V :=
  (roundtripConstruction G k ω).bunch v

/-- Finite expectation under the published mass-one independent hierarchy.
No nonintegrable real integral or conversion of an infinite expectation is used. -/
def hierarchyMean (k : ℕ) (f : Coins V k → ℕ) : ℝ :=
  ∑ ω : Coins V k, (hierarchyLaw V k {ω}).toReal * (f ω : ℝ)

/-- One and the same pair supplies both directional routes. On infinite-roundtrip
queries the displayed inequality is retained; endpoint membership is required on
finite queries, following the source's SCC convention (§2, printed p.6 / PDF p.7). -/
def RoundtripCover (G : DiGraph V E) (stretch : ℕ) (ts : List (TreePair V E)) : Prop :=
  (∀ T ∈ ts, IsTreePair G T) ∧ ∀ u v, ∃ T ∈ ts,
    pairRoundtrip G T u v ≤ (stretch : ENNReal) * roundtrip G u v ∧
    (roundtrip G u v ≠ ⊤ → u ∈ pairSupport T ∧ v ∈ pairSupport T)

end DirectedTreeCovers.Strong.Supplement


