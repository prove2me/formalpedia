-- Prove2me | Definitions.Def_GyoriLovasz_ConnectedTo
-- name    : GyoriLovasz_ConnectedTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:13.85397+00:00
-- url     : https://prove2.me/theorems/3c48e1cb-323c-47e3-b7fb-c8b6ae6024bc
-- title:
--   $G[U]$ is connected to $r$
-- statement:
--   For a vertex set $U$ containing $r$, the induced subgraph $G[U]$ is **connected to $r$** if every $u\in U$ has a directed path to $r$ in $G[U]$, that is, a directed path of $G$ from $u$ to $r$ all of whose vertices lie in $U$.
--
--   **Formalization Note** The membership $r\in U$ is part of the predicate.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), §2, p.14

import Mathlib
import Definitions.Def_GyoriLovasz_IsDiPath

namespace GyoriLovasz

/-- **`G[U]` is connected to `r`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §2, p.14: "For v ∈ V′, we say that G[V′] is connected to v if every
u ∈ V′ has a directed path to v in G[V′]."

`ConnectedTo G U r` is `r ∈ U` together with: every `u ∈ U` has a directed path of `G` from `u` to `r`
all of whose vertices lie in `U`. -/
def ConnectedTo {V : Type*} (G : DG V) (U : Finset V) (r : V) : Prop :=
  r ∈ U ∧ ∀ u ∈ U, ∃ P : List V, IsDiPath G P ∧ P.head? = some u ∧ P.getLast? = some r ∧ ∀ x ∈ P, x ∈ U

end GyoriLovasz


