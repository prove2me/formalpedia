-- Prove2me | Definitions.Def_TermCycDich_IsIrrelevant
-- name    : TermCycDich_IsIrrelevant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:10.783184+00:00
-- url     : https://prove2.me/theorems/d0942c62-4527-485b-8708-d2b81e5f3fbc
-- title:
--   Irrelevant vertex set
-- statement:
--   For an instance $(G,R)$ of Terminal Cyclability, a set $X\subseteq V(G)\setminus R$ is **irrelevant** if $(G-X, R)$ is a yes-instance if and only if $(G,R)$ is a yes-instance.
--
--   Deleting an irrelevant set produces an equivalent smaller instance; this is the reduction step of Theorem 1.2.
--
--   **Formalization Note** $G-X$ is the subgraph induced on $V(G)\setminus X$, with $R$ viewed as a subset of it.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1.1, p.4 (PDF 6)

import Mathlib
import Definitions.Def_TermCycDich_HasRCycle

namespace TermCycDich

/-- A set `X` of vertices is **irrelevant** for the instance `(G, R)`: `X` contains no red vertex,
and `(G − X, R)` is a yes-instance if and only if `(G, R)` is.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1.1, p.4 (PDF 6): "For Terminal Cyclability, a set X ⊆ V(G) \ R is irrelevant if
(G − X, R) is a yes-instance if and only if (G, R) is a yes-instance."

**Formalization Note** `G − X` is the induced subgraph `G.induce Xᶜ` on the subtype `↥Xᶜ`, and
`R` is pulled back to that subtype (`R ⊆ Xᶜ` since `X ∩ R = ∅`). -/
def IsIrrelevant {V : Type} (G : SimpleGraph V) (R : Set V) (X : Set V) : Prop :=
  Disjoint X R ∧
    (HasRCycle (G.induce Xᶜ) {v : ↥Xᶜ | (v : V) ∈ R} ↔ HasRCycle G R)

end TermCycDich


