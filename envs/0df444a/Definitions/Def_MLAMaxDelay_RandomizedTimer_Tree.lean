-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Tree
-- name    : MLAMaxDelay_RandomizedTimer_Tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:12:04.169754+00:00
-- url     : https://prove2.me/theorems/56a3c2ff-f276-4a9b-8948-ac48a1aeddd0
-- title:
--   Finite rooted trees and nonnegative edge weights
-- statement:
--   A finite rooted tree uses the published parent-map model: its root $\rho$ is fixed by the parent map and every vertex reaches the root after finitely many parent steps. Every nonroot vertex names its edge to its parent. Its edge weight is real and nonnegative, and at least one edge is positive. A rooted service is a vertex set containing the root and closed under parents. Its weight is
--   $$w(S)=\sum_{v\in S\setminus\{\rho\}}w_v.$$
--   The root pseudo-edge carries no charge. This definition imposes no depth or branching bound and permits zero edges. The unweighted tree is separate from the request/service model.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 4, Section 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree

namespace MLAMaxDelay.RandomizedTimer

/-- Section 2, p. 4. The generic rooted tree is the published parent-map model:
root fixed by parent, every vertex eventually reaching it. Every finite rooted
tree is represented, with no depth or branching bound. Each non-root vertex
names its edge to its parent. Unlike the published positive-weight HST tree,
this wrapper permits zero edges. -/
structure WeightedTree (V : Type) [Fintype V] [DecidableEq V]
    extends HarelTarjan.Compressed.RootedTree V where
  weight : V → ℝ
  nonneg : ∀ v, v ≠ root → 0 ≤ weight v
  positive_edge : ∃ v, v ≠ root ∧ 0 < weight v

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Exactly the connected subtrees containing the root. -/
def RootedService (T : HarelTarjan.Compressed.RootedTree V) (S : Finset V) : Prop :=
  T.root ∈ S ∧ ∀ v ∈ S, T.parent v ∈ S

noncomputable def spatialWeight (T : WeightedTree V) (S : Finset V) : ℝ :=
  ∑ v ∈ S.erase T.root, T.weight v

end MLAMaxDelay.RandomizedTimer


