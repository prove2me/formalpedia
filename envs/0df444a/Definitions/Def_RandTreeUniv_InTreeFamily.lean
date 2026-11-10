-- Prove2me | Definitions.Def_RandTreeUniv_InTreeFamily
-- name    : RandTreeUniv_InTreeFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:12.980763+00:00
-- url     : https://prove2.me/theorems/390da62d-c879-411f-a7d3-77a4e7054307
-- title:
--   The family $\mathcal T_{n,\Delta}$ of trees with maximum degree at most $\Delta$
-- statement:
--   For a positive integer $\Delta$, $\mathcal T_{n,\Delta}$ is the set of all $n$-vertex trees with maximum degree at most $\Delta$. A graph $T$ belongs to it when $T$ is a tree (connected and acyclic) and every vertex has degree at most $\Delta$.
--
--   This is the family whose universality is the goal of the mission.
--
--   **Formalization Note** The predicate is stated for graphs on any finite vertex type; for $n$-vertex trees the vertex type is $\{0,\dots,n-1\}$, and every $n$-vertex tree is isomorphic to one there.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §1.1, p.1 (PDF 2)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `T ∈ T_{n,∆}`: `T` is a tree with maximum degree at most `∆` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §1.1, p.1 (PDF 2):
"define `T_{n,∆}` to be the set of all `n`-vertex trees with maximum degree at most `∆`").

**Formalization Note** For trees on `n` vertices take `V = Fin n`; every `n`-vertex tree is
isomorphic to one on `Fin n`, and containment of copies is invariant under isomorphism. -/
def InTreeFamily {V : Type*} [Fintype V] (Δ : ℕ) (T : SimpleGraph V) : Prop :=
  T.IsTree ∧ ∀ v, T.degree v ≤ Δ

end RandTreeUniv


