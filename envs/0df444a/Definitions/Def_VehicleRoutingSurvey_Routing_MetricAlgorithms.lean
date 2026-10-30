-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms
-- name    : VehicleRoutingSurvey_Routing_MetricAlgorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:09:02.755995+00:00
-- url     : https://prove2.me/theorems/68c09555-2c78-4773-b532-316babf8ae10
-- title:
--   Nearest addition, nearest merger and metric tree heuristics
-- statement:
--   Nearest addition inserts a closest outside vertex next to an endpoint of a shortest edge crossing the current tour. Nearest merger starts with singleton tours, selects two subtours linked by a shortest intertour edge, and splices them at a minimum-cost pair of deleted edges; a singleton uses minimum-cost insertion. Double-tree and Christofides run predicates use the published minimum spanning tree, odd matching and first-visit shortcut definitions. All admissible starts, ties and Euler orders are retained. These metric-tour procedures are separate from rural postman service preservation.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), Table 3, p. 5; algorithms A06–A07 as in [32], Rosenkrantz–Stearns–Lewis (1977), §6, pp. 577–579, https://paperzz.com/doc/7007820/document

import Definitions.Def_SupplyChainTheory_tsp
import Definitions.Def_TSPHeuristics_Shared_Insertion

open Classical

namespace VehicleRoutingSurvey.Routing

/-- Nearest addition, Rosenkrantz--Stearns--Lewis §6: insert adjacent to
an endpoint of a shortest edge crossing the current subtour. -/
def NearestAdditionRun {n : ℕ} (d : Fin n → Fin n → ℝ)
    (T : ℕ → List (Fin n)) : Prop :=
  (∃ a, T 0 = [a]) ∧ ∀ k, k + 1 < n →
    ∃ a b p, a ∉ T k ∧ b ∈ T k ∧
      (∀ x ∈ T k, ∀ y, y ∉ T k → d b a ≤ d x y) ∧
      p < (T k).length ∧
      ((T k)[p]? = some b ∨ ((T k).rotate 1)[p]? = some b) ∧
      T (k + 1) = (T k).insertIdx (p + 1) a

/-- Two cyclic lists spliced after deleting one edge of each, in either orientation. -/
def SpliceCandidate {α : Type} (u v w : List α) : Prop :=
  ∃ i j : ℕ, ∃ reverse : Bool,
    i < u.length ∧ j < v.length ∧
      w = u.rotate i ++ (if reverse then v.reverse else v).rotate j

def MinimumMerge {n : ℕ} (d : Fin n → Fin n → ℝ)
    (u v w : List (Fin n)) : Prop :=
  (∃ a, u = [a] ∧ TSPHeuristics.Shared.IsInsertion d v a w) ∨
  (∃ a, v = [a] ∧ TSPHeuristics.Shared.IsInsertion d u a w) ∨
  (2 ≤ u.length ∧ 2 ≤ v.length ∧ SpliceCandidate u v w ∧
    ∀ z, SpliceCandidate u v z →
      TSPHeuristics.Shared.cycleLength d w ≤ TSPHeuristics.Shared.cycleLength d z)

def NearestMergeStep {n : ℕ} (d : Fin n → Fin n → ℝ)
    (S S' : List (List (Fin n))) : Prop :=
  ∃ u v rest w a b, S.Perm (u :: v :: rest) ∧ S'.Perm (w :: rest) ∧
    a ∈ u ∧ b ∈ v ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ x ∈ p, ∀ y ∈ q, d a b ≤ d x y) ∧
    MinimumMerge d u v w

def NearestMergerRun {n : ℕ} (d : Fin n → Fin n → ℝ) (tour : List (Fin n)) : Prop :=
  ∃ S : ℕ → List (List (Fin n)),
    S 0 = (List.finRange n).map (fun v => [v]) ∧
    (∀ k, k + 1 < n → NearestMergeStep d (S k) (S (k + 1))) ∧ S (n - 1) = [tour]

def DoubleTreeRun {n : ℕ} (c : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (T : SimpleGraph (Fin n)), SupplyChainTheory.IsMST c T ∧
    ∃ (v : Fin n) (W : T.Walk v v),
      (∀ e ∈ T.edgeSet, W.edges.count e = 2) ∧ SupplyChainTheory.IsShortcut W.support τ

def ChristofidesRun {n : ℕ} (c : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (T : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))),
    SupplyChainTheory.IsMST c T ∧
    SupplyChainTheory.IsMinMatchingOn c (SupplyChainTheory.oddNodes T) M ∧
    ∃ (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v),
      (W.edges : Multiset (Sym2 (Fin n))) = T.edgeFinset.val + M.val ∧
      SupplyChainTheory.IsShortcut W.support τ

end VehicleRoutingSurvey.Routing


