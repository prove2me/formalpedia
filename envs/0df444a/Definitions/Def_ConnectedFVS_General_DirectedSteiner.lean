-- Prove2me | Definitions.Def_ConnectedFVS_General_DirectedSteiner
-- name    : ConnectedFVS_General_DirectedSteiner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:17:46.840303+00:00
-- url     : https://prove2.me/theorems/9f23cb15-2094-4863-ad66-998bfbfb0f60
-- title:
--   Directed Steiner Out-Tree instances and feasibility
-- statement:
--   An instance consists of a finite directed graph $D$, a distinguished vertex $r$, a terminal set $S$ and an integer vertex budget $p$. Feasibility means existence of a selected vertex set $F$ containing $r$ and all terminals, with $|F|\le p$, and a subrelation of the ambient arcs supported on $F$. The root has no incoming arc, each other selected vertex has exactly one predecessor, every selected vertex is reachable from $r$ along selected arcs, and the underlying undirected graph of the selected arcs is a tree. Thus the selected out-tree is nonempty. The ambient graph may have directed cycles, and terminals may include the root or be empty. Negative and zero budgets are no-instances. The parameter is $|S|$.
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), §2–§3.1, PDF pp. 3–4

import Definitions.Def_ConnectedFVS_General_FiniteGraphs

namespace ConnectedFVS.General

structure DSOTInstance where
  D : FiniteDGraph
  root : Fin D.n
  terminals : Finset (Fin D.n)
  budget : ℤ

/-- An oriented nonempty tree on a selected vertex set, with the specified root.
Its arcs are a subset of the ambient arcs; its underlying undirected graph is a tree.
All terminals are included, with no restriction on whether the root is a terminal. -/
def DSOTInstance.Yes (I : DSOTInstance) : Prop :=
  ∃ F : Finset (Fin I.D.n), (F.card : ℤ) ≤ I.budget ∧ I.root ∈ F ∧ I.terminals ⊆ F ∧
    ∃ R : Fin I.D.n → Fin I.D.n → Prop,
      (∀ u v, R u v → u ∈ F ∧ v ∈ F ∧ I.D.arc u v = true) ∧
      (∀ u, ¬ R u I.root) ∧
      (∀ v ∈ F, v ≠ I.root → ∃! u, R u v) ∧
      (∀ v ∈ F, Relation.ReflTransGen R I.root v) ∧
      (∃ T : SimpleGraph {v // v ∈ F}, T.IsTree ∧
        ∀ u v, T.Adj u v ↔ R u.val v.val ∨ R v.val u.val)

end ConnectedFVS.General


