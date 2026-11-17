-- Prove2me | Definitions.Def_AsymSpecConn_Supplement_graphGenerator
-- name    : AsymSpecConn_Supplement_graphGenerator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:21:16.679304+00:00
-- url     : https://prove2.me/theorems/179eebe9-da87-40c4-966e-3e32af08b851
-- title:
--   Edge tensor generators and vertex-incidence vectors of a graph
-- statement:
--   Let $H$ be a finite simple graph on vertices $[k]$. For each edge $e=\{u,v\}$, its **edge tensor generator** $b_e$ is the two-dimensional unit tensor on legs $u$ and $v$, with one-dimensional factors on every other leg. For a vertex $w$, its **incidence vector** $\chi_w\in\{0,1\}^{E(H)}$ has coordinate $1$ precisely on edges incident with $w$.
--
--   The ordered endpoint representation indexes each unoriented edge exactly once. Isolated vertices remain present and have incidence vector zero.
--
--   These are the graph tensors and convex-hull centers in Definition 4.11 and Theorem 4.12.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Definition 4.11 and Theorem 4.12 p.36

import Mathlib
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_mme_tensor_quotient

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn.Supplement

universe u

/-- The unoriented edges of a finite simple graph, represented by their uniquely ordered endpoints. -/
abbrev GraphEdge {k : ℕ} (H : SimpleGraph (Fin k)) :=
  {e : Fin k × Fin k // e.1 < e.2 ∧ H.Adj e.1 e.2}

/-- The finite edge index type, obtained classically so theorem statements do not carry a
computability hypothesis on graph adjacency. -/
noncomputable instance graphEdgeFintype {k : ℕ} (H : SimpleGraph (Fin k)) :
    Fintype (GraphEdge H) := Fintype.ofFinite _

/-- The generator `b_e` of Definition 4.11 (p.36): the two-dimensional unit tensor on edge
`e`, with one-dimensional factors on all other legs. This is the published edge tensor
`GraphTensorCP.edgeTensor`. -/
noncomputable def graphGenerator (K : Type u) [Field K] {k : ℕ} (H : SimpleGraph (Fin k))
    (e : GraphEdge H) : MME.TensorQ K k :=
  MME.TensorQ.toQ (GraphTensorCP.edgeTensor K e.1.1 e.1.2 2)

/-- The vertex-incidence vector `chi_w ∈ {0,1}^E` of p.36. Isolated vertices give the zero
vector; they are deliberately retained in Theorem 4.12. -/
def incidenceVector {k : ℕ} (H : SimpleGraph (Fin k)) (w : Fin k) : GraphEdge H → ℝ :=
  fun e => if w = e.1.1 ∨ w = e.1.2 then 1 else 0

end AsymSpecConn.Supplement


