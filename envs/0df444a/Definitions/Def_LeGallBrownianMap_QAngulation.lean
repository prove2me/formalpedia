-- Prove2me | Definitions.Def_LeGallBrownianMap_QAngulation
-- name    : LeGallBrownianMap_QAngulation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:02.08287+00:00
-- url     : https://prove2.me/theorems/f9106b57-c984-4f18-9768-02dcf3a7d15d
-- title:
--   The finite set $A^q_n$ of rooted planar $q$-angulations with $n$ faces
-- statement:
--   For integers $q\ge 3$ and $n\ge1$, $A^q_n$ is the set of all **rooted planar $q$-angulations with $n$ faces**: rooted planar maps (a distinguished oriented edge, the root) all of whose faces have degree $q$, counted up to root-preserving isomorphism. Loops and multiple edges are allowed. A $q$-angulation with $n$ faces has $qn/2$ edges; $A^3_n$ is empty when $n$ is odd.
--
--   The set is finite; a uniform random element $M_n$ of $A^q_n$ is the random planar map of Theorem 1.1.
--
--   **Formalization Note** The set is the subtype of `OAI.FKCRT.RootedMap (q n / 2 − 1)` (maps with $qn/2$ edges) of $q$-angulations; such a map automatically has exactly $n$ faces. A `Fintype` instance is provided.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, p.2 (A^q_n)

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_IsQAngulation

open OAI.FKCRT

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §1, p.2:
"The set of all rooted planar q-angulations with n faces is denoted by A^q_n."

`QAngulation q n` is the finite set `A^q_n`: rooted planar maps (`OAI.FKCRT.RootedMap`, root =
dart `0`, loops and multiple edges allowed) all of whose faces have degree `q`, with `q n / 2`
edges.

**Formalization Note.** A q-angulation with `n` faces has `q n` darts (each face has `q` darts
and every dart lies in exactly one face), hence `q n / 2` edges; `RootedMap m` has `m + 1`
edges, so the index is `m = q n / 2 - 1`. Conversely a q-angulation with `q n / 2` edges has
exactly `n` faces, so no separate face count is needed. When `q n` is odd (q = 3, n odd) the
set is empty, as in the paper ("A^3_n is empty if n is odd"); the statements of the mission only
use `n ≥ 1` with `q n` even, where `q n / 2 - 1 + 1 = q n / 2`. -/
def QAngulation (q n : ℕ) : Type := {M : RootedMap (q * n / 2 - 1) // IsQAngulation q M}

noncomputable instance (q n : ℕ) : Fintype (QAngulation q n) :=
  Fintype.ofFinite {M : RootedMap (q * n / 2 - 1) // IsQAngulation q M}

end LeGallBrownianMap


