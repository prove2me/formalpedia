-- Prove2me | Definitions.Def_ConnectedFVS_General_CFVS
-- name    : ConnectedFVS_General_CFVS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:17:45.880707+00:00
-- url     : https://prove2.me/theorems/3853bf7f-56c9-4ace-92a4-e0f48aa7ace8
-- title:
--   Connected feedback vertex set instances and feasibility
-- statement:
--   An instance consists of a finite simple undirected graph $G$ and natural budget $k$, including zero. A feedback vertex set $F$ is a vertex subset such that the induced graph on $V(G)\setminus F$ has no undirected cycles. The instance is feasible exactly when some $F$ has $|F|\le k$, is a feedback vertex set, and its induced graph $G[F]$ is connected. Connected means nonempty and path connected. Connectivity cannot use vertices outside $F$. No connectedness assumption is imposed on $G$.
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), §1 and §3, PDF pp. 1, 3

import Definitions.Def_ConnectedFVS_General_FiniteGraphs

namespace ConnectedFVS.General

structure CFVSInstance where
  G : FiniteUGraph
  k : ℕ

def IsFeedbackSet (G : FiniteUGraph) (F : Finset (Fin G.n)) : Prop :=
  (G.graph.induce {v | v ∉ F}).IsAcyclic

/-- Connectivity concerns only the induced graph on F and includes nonemptiness. -/
def CFVSInstance.Yes (I : CFVSInstance) : Prop :=
  ∃ F : Finset (Fin I.G.n), F.card ≤ I.k ∧ IsFeedbackSet I.G F ∧
    (I.G.graph.induce (F : Set (Fin I.G.n))).Connected

end ConnectedFVS.General


