-- Prove2me | Definitions.Def_TermCycDich_IsVital
-- name    : TermCycDich_IsVital
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:17.122008+00:00
-- url     : https://prove2.me/theorems/fb9ee9fe-74c0-47a8-81fc-9b5af6fc66ba
-- title:
--   Vital instance
-- statement:
--   An instance $(G,R)$ of Terminal Cyclability is **vital** if it has a unique $R$-cycle $S$ and $V(S)=V(G)$.
--
--   Theorem 1.3 bounds the treewidth of vital instances.
--
--   **Formalization Note** Uniqueness is uniqueness of the cycle as a subgraph: every $R$-cycle has the same edge set as $S$ (the closed walks tracing one cycle differ by base point and direction).
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1.1, p.10 (PDF 12)

import Mathlib
import Definitions.Def_TermCycDich_IsRCycle

namespace TermCycDich

/-- The instance `(G, R)` is **vital**: it has a unique `R`-cycle `S`, and `S` passes through
every vertex of `G`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1.1, p.10 (PDF 12): "An instance (G, R) is vital if it has a unique R-cycle S and
V(S) = V(G)."

**Formalization Note** A cycle is a subgraph; the closed walks representing one cycle differ by
base point and direction but have the same edge set, and a cycle is determined by its edge set.
So uniqueness is: every `R`-cycle `q` has the same edge set as `S`. (Uniqueness of the walk would
never hold.) `V(S) = V(G)` is "every vertex lies on the walk". -/
def IsVital {V : Type} (G : SimpleGraph V) (R : Set V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), IsRCycle G R p ∧ (∀ v : V, v ∈ p.support) ∧
    ∀ (u' : V) (q : G.Walk u' u'), IsRCycle G R q → {e | e ∈ q.edges} = {e | e ∈ p.edges}

end TermCycDich


