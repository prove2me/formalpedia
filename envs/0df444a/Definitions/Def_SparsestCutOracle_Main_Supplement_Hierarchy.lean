-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Supplement_Hierarchy
-- name    : SparsestCutOracle_Main_Supplement_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:46:53.417084+00:00
-- url     : https://prove2.me/theorems/334576e1-ac57-4434-9f23-2b2eb2251f03
-- title:
--   Complete hierarchies and subcluster congestion contracts
-- statement:
--   Let $G$ be a finite capacitated graph on $n$ labeled vertices. A hierarchy $P=(P_1,\ldots,P_L)$ is a nonempty sequence of distinct full-vertex partitions, beginning with $\{V\}$, with every subsequent partition refining its predecessor. It is complete when $P_L$ consists of the singletons. Nodes are tagged by their level, allowing a set to persist across levels. A node's parent is the unique containing block at the preceding level, with the root its own parent. Set $f_P(V)=1$ at the root and $f_P(X)=\log_2(|\operatorname{par}_P(X)|/|X|)$ otherwise. For an edge $e$, $X_e^{(i)}$ is its smaller endpoint block at level $i$, with ties resolved by its listed orientation.
--
--   A level-$i$ cluster $X$ is subcluster routable at parameter $\gamma>0$ when every signed zero-sum demand supported on $X$ with $|d(v)|\le\deg_{\partial P_{i+1}}(v)$ for $v\in X$ routes inside $G[X]$ with edge bounds
--   $$
--   \operatorname{con}_e=\frac{\log_2\log_2 n\,(1+f_P(X))}{\gamma}+11f_P(X_e^{(i+1)})\quad(e\in G[X]),
--   $$
--   and zero elsewhere. These degrees use the whole next partition, including edges leaving $X$.
--
--   The hierarchy is an $\alpha$-congestion approximator when $\alpha\ge1$ and every zero-sum demand satisfying
--   $$
--   |d(X)|\le\operatorname{cap}(X,V\setminus X)\quad\text{for every block at every level}
--   $$
--   routes in $G$ with scalar congestion $\alpha$. This follows the per-cluster cut tests in the proof of Theorem 9, rather than the inconsistent multilevel union-degree notation on page 44. All combinatorial logarithms here have base two. These definitions retain the full hierarchy and the edge-dependent routing premise.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 44–47, §8.2.1–8.2.2 and Theorem 9

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Supplement_Routing

namespace SparsestCutOracle.Main.Supplement

/-- Level tags are the list positions, so a persistent cluster has distinct nodes. -/
abbrev Hierarchy (n : ℕ) := List (Partition n)

def level {n : ℕ} (P : Hierarchy n) (i : ℕ) : Partition n := P.getD i ∅

def Refines {n : ℕ} (Q P : Partition n) : Prop := ∀ X ∈ Q, ∃ Y ∈ P, X ⊆ Y

def IsHierarchy {n : ℕ} (P : Hierarchy n) : Prop :=
  P ≠ [] ∧ P.Nodup ∧ level P 0 = {Finset.univ} ∧
  (∀ i < P.length, IsPartition Finset.univ (level P i)) ∧
  (∀ i, i + 1 < P.length → Refines (level P (i + 1)) (level P i))

def Complete {n : ℕ} (P : Hierarchy n) : Prop :=
  IsHierarchy P ∧ level P (P.length - 1) = Finset.univ.image (fun v : Fin n => {v})

noncomputable def clusterAt {n : ℕ} (P : Hierarchy n) (i : ℕ) (v : Fin n) : VertexSet n :=
  if h : ∃ X ∈ level P i, v ∈ X then Classical.choose h else ∅

noncomputable def parent {n : ℕ} (P : Hierarchy n) (i : ℕ) (X : VertexSet n) : VertexSet n :=
  if i = 0 then Finset.univ else
    if h : ∃ Y ∈ level P (i - 1), X ⊆ Y then Classical.choose h else ∅

/-- All cardinality ratios and the combinatorial logarithms of §8.2 use base two. -/
noncomputable def fP {n : ℕ} (P : Hierarchy n) (i : ℕ) (X : VertexSet n) : ℝ :=
  if i = 0 then 1 else Real.logb 2 ((parent P i X).card / (X.card : ℝ))

/-- Ties choose the first listed endpoint. For an internal edge the two candidates
have the same parent, hence equal fP when their cardinalities agree. -/
noncomputable def edgeCluster {n : ℕ} (P : Hierarchy n) (i : ℕ) (e : Edge n) : VertexSet n :=
  let U := clusterAt P i e.u
  let V := clusterAt P i e.v
  if U.card ≤ V.card then U else V

noncomputable def subclusterCongestion {n : ℕ} (G : Graph n) (P : Hierarchy n)
    (γ : ℝ) (i : ℕ) (X : VertexSet n) (j : Fin G.length) : ℝ :=
  if G[j.val].u ∈ X ∧ G[j.val].v ∈ X then
    Real.logb 2 (Real.logb 2 n) * (1 + fP P i X) / γ +
      11 * fP P (i + 1) (edgeCluster P (i + 1) G[j.val])
  else 0

/-- The degree is that of the WHOLE next partition boundary, restricted to X.
Singleton clusters impose only the zero demand, so including them changes nothing. -/
def SubclusterRoutable {n : ℕ} (G : Graph n) (P : Hierarchy n) (γ : ℝ) : Prop :=
  ∀ i, i + 1 < P.length → ∀ X ∈ level P i, ∀ d : Fin n → ℝ,
    DemandOn X d → (∀ v ∈ X, |d v| ≤ boundaryDegree G (level P (i + 1)) v) →
    RoutesOn G X d (subclusterCongestion G P γ i X)

/-- The per-cluster cut tests in the first paragraph of the proof of Theorem 9.
In particular |sum d| is used, not sum |d|. -/
def HierarchyDemand {n : ℕ} (G : Graph n) (P : Hierarchy n) (d : Fin n → ℝ) : Prop :=
  mass d Finset.univ = 0 ∧
    ∀ i < P.length, ∀ X ∈ level P i, |mass d X| ≤ cut G.toWGraph X Xᶜ

def CongestionApproximator {n : ℕ} (G : Graph n) (P : Hierarchy n) (α : ℝ) : Prop :=
  1 ≤ α ∧ ∀ d : Fin n → ℝ, HierarchyDemand G P d →
    RoutesOn G Finset.univ d (fun _ => α)

end SparsestCutOracle.Main.Supplement


