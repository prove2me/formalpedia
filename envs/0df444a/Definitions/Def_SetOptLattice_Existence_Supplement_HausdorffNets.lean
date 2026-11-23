-- Prove2me | Definitions.Def_SetOptLattice_Existence_Supplement_HausdorffNets
-- name    : SetOptLattice_Existence_Supplement_HausdorffNets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:56:40.304898+00:00
-- url     : https://prove2.me/theorems/f8e9cd02-e417-45f7-b59d-92df6a6e05b7
-- title:
--   Hausdorff convergence of arbitrary set-valued nets and subnet limits
-- statement:
--   Let $X$ be a topological additive group. For a filter $l$ on any index set $I$, a family $A:I\to\mathcal P(X)$ converges to $N\subseteq X$ when
--   $$\forall U\in\mathcal N_X(0),\quad\text{eventually}_{i\to l}\quad A_i\subseteq N+U\ \text{and}\ N\subseteq A_i+U.$$
--   For directed nets $l$ is the tail filter. For positive tolerances it is $\mathcal N_{\mathbb R}(0)\vert_{(0,\infty)}$, giving exactly the published convergence predicate. No metric, boundedness or closedness of the sets is required.
--
--   A net is represented by its image tail filter $F$ on $\mathcal P(X)$. Having a convergent subnet with a limit in a family $S$ means that some $N\in S$ and a nontrivial filter $G\le F$ satisfy this convergence. Every nontrivial filter has a directed-net realization, and a nontrivial refinement of an image tail filter can be lifted to a genuinely cofinal reindexing of the original net. Thus this representation includes arbitrary directed nets of any cardinality. The family predicate requires this subnet property for every nontrivial $F$ with $S\in F$. Eventual membership in $S$ is equivalent to restricting a representing net to a tail in $S$.
--
--   These general convergence objects are independent of the optimization model. Sets with the same closure may share limits; uniqueness of a limit set is not asserted.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 24, proof of Theorem 4.3 (upper and lower Hausdorff convergence); pp. 26–27, Definitions 4.8–4.9 and Theorem 4.12(2)

import Mathlib

namespace SetOptLattice.Existence.Supplement

open Set Filter Topology
open scoped Pointwise

/-- Two-sided Hausdorff convergence along any filter. For a directed net use `atTop`;
for the published positive-tolerance convention use `𝓝[>] (0 : ℝ)`. -/
def HausdorffAlong {X ι : Type*} [TopologicalSpace X] [AddZeroClass X]
    (l : Filter ι) (A : ι → Set X) (N : Set X) : Prop :=
  ∀ U ∈ 𝓝 (0 : X), ∀ᶠ i in l, A i ⊆ N + U ∧ N ⊆ A i + U

/-- The index-free subnet condition. `F` is a net's image tail filter on `Set X`.
A nontrivial refinement `G ≤ F` converging to `N ∈ S` is equivalent to a genuine
cofinal subnet converging to N. This uses arbitrary directed indices, not sequences.
Nontriviality of F is required by callers; nontriviality of G is explicit here. -/
def HasHausdorffSubnetIn {X : Type*} [TopologicalSpace X] [AddZeroClass X]
    (F : Filter (Set X)) (S : Set (Set X)) : Prop :=
  ∃ N ∈ S, ∃ G : Filter (Set X), G.NeBot ∧ G ≤ F ∧ HausdorffAlong G id N

/-- Every net with values in S has a convergent cofinal subnet with limit in S.
Every nontrivial filter has a directed-net realization. Eventual membership in S
is equivalent here to a net wholly in S after restricting to a tail. -/
def HausdorffNetCompact {X : Type*} [TopologicalSpace X] [AddZeroClass X]
    (S : Set (Set X)) : Prop :=
  ∀ F : Filter (Set X), F.NeBot → S ∈ F → HasHausdorffSubnetIn F S

end SetOptLattice.Existence.Supplement


