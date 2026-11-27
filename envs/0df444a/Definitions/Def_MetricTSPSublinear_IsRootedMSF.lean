-- Prove2me | Definitions.Def_MetricTSPSublinear_IsRootedMSF
-- name    : MetricTSPSublinear_IsRootedMSF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:28:07.3358+00:00
-- url     : https://prove2.me/theorems/015910bd-fd2f-4aef-91c6-aa875cca1832
-- title:
--   Rooted minimum spanning forest
-- statement:
--   Let $d$ be a metric on $V=\{0,\dots,n-1\}$ and $R\subseteq V$ a set of roots. A **rooted spanning forest** for $R$ is a set $F$ of pairs of points that contains no circuit and in which every point $v$ is connected (by a path using edges of $F$) to exactly one root $r\in R$. A **rooted minimum spanning forest** (rooted MSF) is a rooted spanning forest of least total weight $\sum_{e\in F}d(e)$.
--
--   1. `reachIn F u v`: $v$ is reachable from $u$ along edges of $F$.
--   2. `IsRootedSpanningForest R F`: $F$ is a forest of the complete graph and every point reaches exactly one root.
--   3. `IsRootedMSF d R F`: $F$ is a rooted spanning forest of minimum weight.
--
--   In the sublinear metric TSP algorithm the rooted MSF $F_{\mathrm{root}}$ for a sampled root set $S_{\mathrm{root}}$ is split into small MST fragments, which the algorithm recovers locally by Prim's algorithm and depth-first search.
--
--   **Formalization Note** Forests and paths are those of the published complete multigraph `DoublingMST.completeGraph n` (`CombOpt.SpanningTree`), so loops and repeated edges are excluded by the forest condition.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §3, p.10 (PDF p.12): 'we define the rooted minimum spanning forest (rooted MSF), as a forest with minimum weight, such that each component includes exactly one root from S'; §5.1 p.15 (F_root).

import Mathlib
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_CombOpt_SpanningTree_Graph_IsForest
import Definitions.Def_DoublingMST_treeWeight

namespace MetricTSPSublinear

variable {n : ℕ}


/-- `v` is reachable from `u` using only edges of `F`. -/
def reachIn (F : Finset (Sym2 (Fin n))) (u v : Fin n) : Prop :=
  ∃ p : (DoublingMST.completeGraph n).Walk u v, ∀ e ∈ p.edges, e ∈ F

/-- `F` is a forest each of whose components contains exactly one root of `R`. -/
def IsRootedSpanningForest (R : Finset (Fin n)) (F : Finset (Sym2 (Fin n))) : Prop :=
  (DoublingMST.completeGraph n).IsForest F ∧ ∀ v, ∃! r, r ∈ R ∧ reachIn F v r

/-- A rooted minimum spanning forest. -/
def IsRootedMSF (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (F : Finset (Sym2 (Fin n))) : Prop :=
  IsRootedSpanningForest R F ∧
    ∀ F', IsRootedSpanningForest R F' → DoublingMST.treeWeight d F ≤ DoublingMST.treeWeight d F'


end MetricTSPSublinear


