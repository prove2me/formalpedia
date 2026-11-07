-- Prove2me | Definitions.Def_GyoriLovasz_IsDiPath
-- name    : GyoriLovasz_IsDiPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:13.575653+00:00
-- url     : https://prove2.me/theorems/f7fa3088-d670-496c-97cd-740dd550b69a
-- title:
--   Directed path in a digraph
-- statement:
--   A **directed path** in $G$ is a nonempty sequence $(x_0,x_1,\dots,x_\ell)$ of pairwise distinct vertices of $G$ such that $(x_{j-1},x_j)\in E$ for every $1\le j\le\ell$. A single vertex is a path with no edges. The path starts at $x_0$ and ends at $x_\ell$.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), §2, p.14

import Mathlib
import Definitions.Def_GyoriLovasz_DG

namespace GyoriLovasz

/-- **Directed path.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §2, p.14: a nonempty list of distinct vertices of `G` with consecutive
entries joined by arcs. A single vertex is a path with no arcs. -/
def IsDiPath {V : Type*} (G : DG V) (P : List V) : Prop :=
  P ≠ [] ∧ P.Nodup ∧ (∀ x ∈ P, x ∈ G.verts) ∧ P.IsChain fun a b => (a, b) ∈ G.arcs

end GyoriLovasz


