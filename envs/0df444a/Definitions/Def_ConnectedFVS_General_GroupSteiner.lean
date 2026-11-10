-- Prove2me | Definitions.Def_ConnectedFVS_General_GroupSteiner
-- name    : ConnectedFVS_General_GroupSteiner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:17:46.94891+00:00
-- url     : https://prove2.me/theorems/0305bdea-3bd2-4e08-bd30-dff94c978a8d
-- title:
--   Group Steiner Tree instances and feasibility
-- statement:
--   An instance consists of a finite simple undirected graph $G$, a family of $l$ pairwise disjoint vertex subsets $S_i$, and an integer vertex budget $p$. It is feasible exactly when some set $F$ of at most $p$ vertices supports a nonempty tree subgraph of $G$ that meets every $S_i$. The tree need not be induced and may meet a group more than once. Empty groups, zero groups, empty input graphs and all integer budgets are admitted. Negative and zero budgets are no-instances under the nonempty-tree convention. The parameter is $l$, not $p$.
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), §3.1, PDF p. 4, GST problem box

import Definitions.Def_ConnectedFVS_General_FiniteGraphs

namespace ConnectedFVS.General

structure GSTInstance where
  G : FiniteUGraph
  groups : ℕ
  group : Fin groups → Finset (Fin G.n)
  disjoint : ∀ i j, i ≠ j → Disjoint (group i) (group j)
  budget : ℤ

/-- A nonempty tree subgraph, not necessarily induced, meeting every group. -/
def GSTInstance.Yes (I : GSTInstance) : Prop :=
  ∃ F : Finset (Fin I.G.n), (F.card : ℤ) ≤ I.budget ∧
    (∃ T : SimpleGraph {v // v ∈ F},
      T ≤ I.G.graph.induce (F : Set (Fin I.G.n)) ∧ T.IsTree) ∧
    ∀ i, ∃ v ∈ F, v ∈ I.group i

end ConnectedFVS.General


