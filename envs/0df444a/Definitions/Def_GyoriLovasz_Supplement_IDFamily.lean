-- Prove2me | Definitions.Def_GyoriLovasz_Supplement_IDFamily
-- name    : GyoriLovasz_Supplement_IDFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:12:18.624535+00:00
-- url     : https://prove2.me/theorems/b0f4d690-2caf-4432-8661-2d937905a5d3
-- title:
--   Internally vertex-disjoint paths from $v$ to $T'$
-- statement:
--   Let $G=(V,E)$ be a directed graph, $T'$ a set of terminals and $v$ a vertex. A family of $r$ directed paths of $G$, each starting at $v$ and ending at a vertex of $T'$, is **internally vertex-disjoint** if no two paths of the family share a vertex other than the common starting vertex $v$ and their terminal endpoints. Unlike the vertex-disjoint families defining terminal connectivity, several paths may end at the same terminal.
--
--   This is the path notion of the local connectivity condition (Definitions A.2–A.3) under which Theorems 7 and 8 hold.
--
--   **Formalization Note** The family is a list, so the one-edge path from $v$ to $t$ may be repeated; such a $v$ is a pre-terminal of $t$, which the local connected set counts anyway. A vertex shared by two paths must be $v$ or the last vertex of both; under the standing assumption that terminals have no outgoing edges, a terminal on a path is its last vertex, so this is the paper's notion.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition A.1, p.54

import Mathlib
import Definitions.Def_GyoriLovasz_IsDiPath

namespace GyoriLovasz

namespace Supplement

/-- **`r` internally vertex-disjoint paths from `v` to `T′`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani,
*Breaking the Exponential Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition A.1, p.54: "A family
of directed paths from v to T is internally vertex-disjoint if no two paths share a vertex other than the common
starting vertex v and their terminal endpoints. In particular, unlike the standard notion of vertex-disjoint paths,
several paths are allowed to end at the same terminal."

`IDFamily G T' v r`: a list of `r` directed paths of `G`, each starting at `v` and ending in `T'`, such that any vertex
shared by two paths at distinct positions is `v` or the last vertex of both.

**Formalization Note.** The family is a list, so the one-arc path `[v, t]` may occur repeatedly; such a `v` is a
pre-terminal of `t`, which Definition A.2 counts as locally connected anyway. Under the standing assumption `Std` a
terminal has no outgoing arc, so a terminal on a path is its last vertex and "terminal endpoints" is unambiguous. This
is a different object from the published `HasFamily` (Definition 2.2), which requires distinct end terminals. -/
def IDFamily {V : Type*} (G : DG V) (T' : Finset V) (v : V) (r : ℕ) : Prop :=
  ∃ F : List (List V), F.length = r ∧
    (∀ P ∈ F, IsDiPath G P ∧ P.head? = some v ∧ ∃ t ∈ T', P.getLast? = some t) ∧
    F.Pairwise fun P Q => ∀ x ∈ P, x ∈ Q → x = v ∨ (P.getLast? = some x ∧ Q.getLast? = some x)

end Supplement

end GyoriLovasz


