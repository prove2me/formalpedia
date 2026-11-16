-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_RerouteStep
-- name    : AgnosticTNS_Supplement_RerouteStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:34:56.746708+00:00
-- url     : https://prove2.me/theorems/452faa6c-4dde-43bf-88e2-b34f78aed9c8
-- title:
--   Single-edge rerouting step on weighted graphs
-- statement:
--   A **single-edge rerouting step** turns a weighted graph $(G,w)$ into $(G',w')$ by choosing an edge $\{x,y\}$ of $G$ and a vertex $z\notin\{x,y\}$ and applying (6.7)–(6.8). Theorem 6.11 counts how many such steps transform a graph into a path.
--
--   **Formalization Note** A weighted graph is a pair of a simple graph on $[n]$ and a function from its edges to $\mathbb N$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.8, p.49; Theorem 6.11 (6.18), p.52

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_rerouteWeight

namespace AgnosticTNS.Supplement

/-- **A single-edge rerouting step**, Theorem 6.8, p.49, as counted in Theorem 6.11 (6.18), p.52
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): a weighted graph `(G, w)` becomes `(G′, w′)` by rerouting an edge
`{x, y} ∈ E` through a vertex `z ∉ {x, y}` (Eqs. (6.7)–(6.8)).

**Formalization Note** A weighted graph is a pair `⟨G, w⟩` with `w : G.edgeSet → ℕ`. -/
def RerouteStep {n : ℕ} (A B : Σ G : SimpleGraph (Fin n), G.edgeSet → ℕ) : Prop :=
  ∃ x y z : Fin n, A.1.Adj x y ∧ z ≠ x ∧ z ≠ y ∧
    B = ⟨rerouteGraph A.1 x y z, rerouteWeight A.1 A.2 x y z⟩

end AgnosticTNS.Supplement


