-- Prove2me | Definitions.Def_GyoriLovasz_kappa
-- name    : GyoriLovasz_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:12.17403+00:00
-- url     : https://prove2.me/theorems/b5007fa9-3b9e-4a46-9bdd-36a06f09b081
-- title:
--   Terminal connectivity $\kappa_G(v)$
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T$ and let $v\in V\setminus T$. A **vertex-disjoint family** of $r$ paths from $v$ to $T$ is a list of $r$ directed paths, each starting at $v$ and ending at a terminal, that are pairwise disjoint except for their common starting vertex $v$. In particular they end at distinct terminals.
--
--   The **terminal connectivity** of $v$ to $T$ is
--   $$\kappa_G(v)=\max\{\,r : \text{there is a vertex-disjoint family of } r \text{ paths from } v \text{ to } T\,\}.$$
--
--   The empty family always qualifies, so $\kappa_G(v)\ge0$; a family has at most $|T|$ paths, so the maximum exists. Paths may pass through a terminal before their end; in graphs satisfying the standing assumption of §2 this cannot happen.
--
--   **Formalization Note** $\kappa$ is `Nat.findGreatest` over $r\le|T|$; disjointness is stated on the paths with their first vertex removed. That the bound $|T|$ loses nothing is proved in the mission's sanity file.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition 2.2, p.14

import Mathlib
import Definitions.Def_GyoriLovasz_IsDiPath

namespace GyoriLovasz

/-- **A family of `r` vertex-disjoint paths from `v` to distinct terminals.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 2.2, p.14:
"a family of paths that all start at v, end at distinct terminals in T, and are pairwise
vertex-disjoint except for their common starting vertex v."

**Formalization Note.** Disjointness is of the tails, so the common start is allowed. For `v ∉ T` every
tail contains the end of its path, so disjoint tails give distinct terminals. Paths may pass through a
terminal; on graphs satisfying `Std` that cannot happen. -/
def HasFamily {V : Type*} (G : DG V) (T : Finset V) (v : V) (r : ℕ) : Prop :=
  ∃ F : List (List V), F.length = r ∧
    (∀ P ∈ F, IsDiPath G P ∧ P.head? = some v ∧ ∃ t ∈ T, P.getLast? = some t) ∧
    F.Pairwise fun P Q => P.tail.Disjoint Q.tail

open Classical in
/-- **Terminal connectivity `κ_G(v)`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 2.2, p.14: "the maximum cardinality of a family of
paths that all start at v, end at distinct terminals in T, and are pairwise vertex-disjoint except for
their common starting vertex v."

**Formalization Note.** A `Nat.findGreatest` up to `|T|`. For `v ∉ T` a family has at most `|T|` paths
(tails are disjoint and each contains its own terminal), so the bound loses nothing and this is the true
maximum; `r = 0` always qualifies, by the empty family. The value is only used for `v ∉ T`. -/
noncomputable def kappa {V : Type*} (G : DG V) (T : Finset V) (v : V) : ℕ :=
  Nat.findGreatest (HasFamily G T v) T.card

end GyoriLovasz


