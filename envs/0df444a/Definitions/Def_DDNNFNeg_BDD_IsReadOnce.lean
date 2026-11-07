-- Prove2me | Definitions.Def_DDNNFNeg_BDD_IsReadOnce
-- name    : DDNNFNeg_BDD_IsReadOnce
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:27.627298+00:00
-- url     : https://prove2.me/theorems/50fb2e93-0130-41eb-bec0-024c7c5121e8
-- title:
--   Read-once (free) branching program: nFBDD
-- statement:
--   A branching program is **read-once** (free) if on any source-to-sink path each variable labels at most one vertex: whenever a vertex $u$ reachable from the starting vertex is labelled by the variable $v$, no vertex reachable from a successor of $u$ is labelled by $v$.
--
--   A read-once branching program is a **nondeterministic FBDD** (nFBDD); it is an **unambiguous FBDD** (uFBDD) if it is moreover unambiguous, and an **FBDD** if it has no $\vee$ vertices.
--
--   **Formalization Note** As in the paper, the condition concerns paths from the starting vertex; vertices that cannot be reached from it are unconstrained.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD_Reach

namespace DDNNFNeg

/-- The branching program `B` is read-once (free) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9: "On any
source-to-sink path, each variable labels at most one vertex"): whenever a vertex `u` reachable
from the starting vertex is labelled by the variable `v`, no vertex reachable from a successor
of `u` is labelled by `v`.

**Formalization Note** The condition concerns paths from the starting vertex, as printed;
vertices unreachable from the start are unconstrained. A read-once branching program is an
nFBDD; it is a uFBDD if moreover `BDD.IsUnambiguous`, and an FBDD if `BDD.IsDeterministic`. -/
def BDD.IsReadOnce {X : Type*} (B : BDD X) : Prop :=
  ∀ (u : Fin B.size) (v : X) (lo hi : Fin B.size), B.Reach B.start u →
    B.node u = .test v lo hi →
    ∀ (w lo' hi' : Fin B.size), (B.Reach lo w ∨ B.Reach hi w) → B.node w ≠ .test v lo' hi'

end DDNNFNeg


