-- Prove2me | Definitions.Def_AFIsingKS_toGraph
-- name    : AFIsingKS_toGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:23.823161+00:00
-- url     : https://prove2.me/theorems/5b591bf4-eb0a-41fb-b9b3-89ded80afd4e
-- title:
--   Simple matchings and the contracted graph
-- statement:
--   A perfect matching $M$ of the sockets contracts to a **simple** graph when no socket is matched inside its own cloud and no two matched pairs join the same two clouds. Equivalently, two distinct sockets of one cloud are never matched into one common cloud. The **contracted graph** has an edge between distinct $u,v$ when some socket of $u$ is matched to some socket of $v$.
--
--   **Formalization Note** The contracted graph is defined for every matching, forgetting loops and parallel pairs of a non-simple one; it is the paper's $G$ exactly on simple matchings, and the theorems use it only there.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9

import Mathlib
import Definitions.Def_AFIsingKS_Matching

open scoped Classical

namespace AFIsingKS

/-- The contraction of `M` is simple (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9): no socket is matched inside its own
cloud, and two distinct sockets of one cloud are never matched into one common cloud (no parallel
edges). -/
def IsSimpleM {n d : ℕ} (M : Matching n d) : Prop :=
  (∀ x, (M.1 x).1 ≠ x.1) ∧ ∀ x y, x.1 = y.1 → (M.1 x).1 = (M.1 y).1 → x = y

/-- The simple graph obtained by contracting the clouds of `M` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9): distinct
`u, v` are adjacent when a socket of one is matched to a socket of the other.

**Formalization Note.** Loops and parallel pairs of a non-simple `M` are forgotten here; this graph
is the paper's `G` exactly when `IsSimpleM M`, and the theorems use it only then. -/
def toGraph {n d : ℕ} (M : Matching n d) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => ∃ x : Fin n × Fin d, x.1 = u ∧ (M.1 x).1 = v)

end AFIsingKS


