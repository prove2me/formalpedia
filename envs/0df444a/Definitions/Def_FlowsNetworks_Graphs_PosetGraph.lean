-- Prove2me | Definitions.Def_FlowsNetworks_Graphs_PosetGraph
-- name    : FlowsNetworks_Graphs_PosetGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:03.085059+00:00
-- url     : https://prove2.me/theorems/ca338ea9-8f34-4f7b-81a6-5ba3a612c05d
-- title:
--   Chains, decompositions and unrelated elements of $P$; independent arcs and covers of the bipartite graph $[S, T; \mathcal A]$ built from $P$
-- statement:
--   Following Chapter II, §8 of Ford and Fulkerson's *Flows in Networks*. Let $P = \{1, \dots, n\}$ carry a relation $\succ$ (in the theorems, a partial order).
--
--   1. A **chain** in $P$ is a set of one or more elements that can be listed as distinct $i_1, i_2, \dots, i_k$ with
--   $$i_1 \succ i_2 \succ \cdots \succ i_k. \tag{8.1}$$
--   2. A **decomposition** $\Delta$ of $P$ is a partition of $P$ into chains; $|\Delta|$ is the number of chains.
--   3. A set $U \subseteq P$ is **mutually unrelated** if for any two distinct $i, j \in U$ neither $i \succ j$ nor $j \succ i$.
--   4. The **bipartite graph** $G = [S, T; \mathcal A]$ of $P$ has nodes $S = \{x_1, \dots, x_n\}$ and $T = \{y_1, \dots, y_n\}$ and arcs $(x_i, y_j) \in \mathcal A$ if and only if $i \succ j$.
--   5. A set $\mathcal J \subseteq \mathcal A$ of arcs is **independent** if its arcs are pairwise node disjoint: two distinct arcs $(x_i, y_j), (x_k, y_l) \in \mathcal J$ have $i \ne k$ and $j \ne l$.
--   6. A set $X \subseteq S \cup T$ of nodes is a **cover** if every arc $(x_i, y_j) \in \mathcal A$ has $x_i \in X$ or $y_j \in X$. A cover is **proper** if no proper subset of it is a cover.
--
--   **Formalization Note** $P$ is `Fin n` (elements $0, \dots, n-1$ instead of $1, \dots, n$) and $\succ$ is a relation `r : Fin n → Fin n → Prop`; the partial-order hypothesis is stated in each theorem, not here. The nodes of $G$ are `Fin n ⊕ Fin n` (`Sum.inl i` $= x_i$, `Sum.inr j` $= y_j$), and an arc $(x_i, y_j)$ is recorded by its index pair $(i, j)$. A decomposition is a `Finpartition` of the whole of `Fin n` (parts are nonempty) whose parts are chains. For a partial order, (8.1) with consecutive relations is the book's chain, transitivity giving the remaining relations.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, pp. 44–46 (§8: chain (8.1), decomposition, unrelated elements, the bipartite graph of P, proper cover); p. 34 (§4: independent sets and covers)

import Mathlib

namespace FlowsNetworks.Graphs

/-! Chapter II, §8 of Ford–Fulkerson, *Flows in Networks*: a finite set `P = {1, …, n}` (here
`Fin n`) with a relation `i ≻ j` (here `r i j`), and the bipartite graph `G = [S, T; 𝒜]` with
`S = {x₁, …, x_n}`, `T = {y₁, …, y_n}` and `(x_i, y_j) ∈ 𝒜` iff `i ≻ j`. The nodes of `G` are
`Fin n ⊕ Fin n`: `Sum.inl i` is `x_i ∈ S` and `Sum.inr j` is `y_j ∈ T`; the arc `(x_i, y_j)` is
recorded by its index pair `(i, j)`. The definitions take an arbitrary relation; the partial-order
hypothesis is stated in each theorem. -/

/-- A chain (8.1) of `P` (p. 44–45): a set of one or more elements that can be listed as
`i₁, i₂, …, i_k` (distinct) with `i₁ ≻ i₂ ≻ ⋯ ≻ i_k`, i.e. `r i_m i_{m+1}` for consecutive
elements. -/
def IsChainOf {n : ℕ} (r : Fin n → Fin n → Prop) (C : Finset (Fin n)) : Prop :=
  ∃ l : List (Fin n), l ≠ [] ∧ l.Nodup ∧ (∀ a, a ∈ C ↔ a ∈ l) ∧
    ∀ (m : ℕ) (h : m + 1 < l.length), r l[m] l[m + 1]

/-- A decomposition of `P` (p. 45): a partition of `P` into chains. The number of chains is
`Δ.parts.card`; parts of a `Finpartition` are nonempty. -/
def IsDecomposition {n : ℕ} (r : Fin n → Fin n → Prop)
    (Δ : Finpartition (Finset.univ : Finset (Fin n))) : Prop :=
  ∀ C ∈ Δ.parts, IsChainOf r C

/-- A set `U ⊆ P` of mutually unrelated elements (p. 45): two distinct members `i, j` of `U` are
unrelated, i.e. neither `i ≻ j` nor `j ≻ i`. -/
def MutuallyUnrelated {n : ℕ} (r : Fin n → Fin n → Prop) (U : Finset (Fin n)) : Prop :=
  ∀ i ∈ U, ∀ j ∈ U, i ≠ j → ¬ r i j ∧ ¬ r j i

/-- An independent set `𝒥 ⊆ 𝒜` of arcs of the bipartite graph `G` built from `P` (p. 46; p. 34:
pairwise node disjoint arcs). The arc `(x_i, y_j)` is recorded as `(i, j)`: every member is an arc
(`i ≻ j`), and two distinct arcs `(x_i, y_j)`, `(x_k, y_l)` share no node, i.e. `i ≠ k` and
`j ≠ l`. -/
def IsIndependentArcs {n : ℕ} (r : Fin n → Fin n → Prop) (J : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ J, r p.1 p.2) ∧ ∀ p ∈ J, ∀ q ∈ J, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2

/-- A covering set of nodes `X ⊆ S ∪ T` of the bipartite graph `G` built from `P` (p. 46; p. 34):
every arc `(x_i, y_j)` (i.e. every pair with `i ≻ j`) has `x_i ∈ X` or `y_j ∈ X`. -/
def IsCover {n : ℕ} (r : Fin n → Fin n → Prop) (X : Finset (Fin n ⊕ Fin n)) : Prop :=
  ∀ i j, r i j → Sum.inl i ∈ X ∨ Sum.inr j ∈ X

/-- A proper cover (p. 46): a covering set of nodes no proper subset of which is itself a cover. -/
def IsProperCover {n : ℕ} (r : Fin n → Fin n → Prop) (X : Finset (Fin n ⊕ Fin n)) : Prop :=
  IsCover r X ∧ ∀ Y : Finset (Fin n ⊕ Fin n), Y ⊂ X → ¬ IsCover r Y

end FlowsNetworks.Graphs


