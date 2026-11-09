-- Prove2me | Definitions.Def_TZLevelsADO_Hierarchy
-- name    : TZLevelsADO_Hierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:31.267106+00:00
-- url     : https://prove2.me/theorems/8c70e57b-9eac-4087-93df-19ea228ab242
-- title:
--   The Thorup–Zwick hierarchy, pivots $p_i(u)$, pivot distances $h_i(u)$ and bunches $B(u)$
-- statement:
--   Fix a graph $G$ as above and an integer $k \ge 1$. A **Thorup–Zwick hierarchy** is a nested family of vertex sets
--   $$V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_{k-1} \supseteq A_k = \emptyset, \qquad A_{k-1} \neq \emptyset.$$
--   For a vertex $u$ and a set $X$ write $d(u, X) = \min_{x \in X} d(u, x)$, with $d(u, \emptyset) = \infty$.
--
--   A **pivot choice** assigns to every level $i \in [k] = \{0, \dots, k-1\}$ and vertex $u$ a closest vertex $p_i(u) \in \arg\min_{w \in A_i} d(u, w)$, the $i$-th **pivot** of $u$, and $h_i(u) := d(u, p_i(u)) = d(u, A_i)$. Since $A_k = \emptyset$, $h_k(u) = \infty$.
--
--   The level-$i$ bunch and the **bunch** of $u$ are
--   $$B_i(u) = \{ w \in A_i \mid d(u, w) < h_{i+1}(u) \}, \qquad B(u) = \bigcup_{i \in [k]} B_i(u),$$
--   so in particular $B_{k-1}(u) = A_{k-1}$. The **one-level** and **two-level growth** of a vertex $x$ at level $i$ are
--   $$\Delta_i(x) = h_i(x) - h_{i-1}(x) \quad (1 \le i < k), \qquad \nabla_i(x) = h_i(x) - h_{i-2}(x) \quad (2 \le i < k).$$
--
--   These are the objects of the Thorup–Zwick hierarchy reviewed in §2 of the paper; the growth lemmas of the mission are statements about them.
--
--   **Formalization Note** The page samples the hierarchy at random and adds one fixed vertex to $A_1, \dots, A_{k-1}$; since the stretch analysis holds for every outcome of the sampling, the hierarchy here is any nested family with the properties displayed (the sampled one is `sampledHierarchy`). The bunches use $d(u, A_{i+1})$ in $\mathbb R \cup \{\infty\}$, so they do not depend on the pivot choice; ties in the argmin may be broken arbitrarily.
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §2 "The Thorup–Zwick hierarchy", p.7 (PDF p.8)

import Mathlib
import Definitions.Def_TZLevelsADO_Graph

namespace TZLevelsADO

/-!
# The Thorup–Zwick hierarchy, pivots and bunches

S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §2 "The Thorup–Zwick hierarchy", p.7 (PDF p.8): "a vertex hierarchy
V = A₀ ⊇ A₁ ⊇ … ⊇ A_k = ∅ … We also add one fixed vertex of A₀ to A₁, …, A_{k−1}, so that
A_{k−1} ≠ ∅. For every vertex u ∈ V, let p_i(u) ∈ arg min_{w∈A_i} d(u, w), h_i(u) := d(u, p_i(u)),
and B_i(u) = {w ∈ A_i | d(u, w) < h_{i+1}(u)}, and let B(u) = ∪_i B_i(u). … Since A_k = ∅, we have
h_k(u) = ∞, and hence B_{k−1}(u) = A_{k−1}. We write [k] = {0, 1, …, k − 1} for the set of levels.
For a vertex x, we write ∆_i(x) = h_i(x) − h_{i−1}(x) for 1 ≤ i < k and
∇_i(x) = h_i(x) − h_{i−2}(x) = ∆_i(x) + ∆_{i−1}(x) for 2 ≤ i < k".

**Formalization Note.**
* **Hierarchy.** `Hierarchy G k` is any nested family `A 0 = V ⊇ A 1 ⊇ ⋯` with `A (k−1)` nonempty and
  `A k = ∅`, for `k ≥ 1`. The page's random sampling only bounds bunch sizes, and the stretch analysis
  holds "for every outcome of the sampling" (p.7); "A_{k−1} ≠ ∅" is the only property of the fixed vertex
  the analysis uses. The sampled hierarchy itself is `sampledA` (module `Def_TZLevelsADO_sampledA`).
* **Pivots.** `PivotChoice A` is any choice `p i u ∈ argmin_{w ∈ A i} d(u, w)` for `i < k`; ties may be
  broken arbitrarily. Values of `p i u` for `i ≥ k` are unconstrained and never used.
* **`h` and bunches.** `distToSet G X u = d(u, X)` takes values in `WithTop ℝ` and equals `⊤` on the
  empty set, so `h_k(u) = d(u, A_k) = ∞` and `B_{k−1}(u) = A_{k−1}` as on the page. `bunchAt` and
  `bunch` depend only on the hierarchy (through `d(u, A_{i+1})`), not on the pivot choice. The real
  number `PivotChoice.h P i u = d(u, p_i(u))` is the page's `h_i(u)` for `i < k`.
* `oneLevel P i x = ∆_i(x)` and `twoLevel P i x = ∇_i(x)` are meaningful for `1 ≤ i < k` and
  `2 ≤ i < k` respectively; every statement using them carries those bounds.
-/

/-- §2, p.7: an admissible Thorup–Zwick hierarchy for the parameter `k ≥ 1`. -/
structure Hierarchy (G : Graph) (k : ℕ) where
  /-- the levels `A_0 ⊇ A_1 ⊇ ⋯` -/
  A : ℕ → Finset (Fin G.n)
  /-- `k` is a positive integer -/
  pos : 0 < k
  /-- `A_0 = V` -/
  zero : A 0 = Finset.univ
  /-- `A_{i+1} ⊆ A_i` -/
  mono : ∀ i, A (i + 1) ⊆ A i
  /-- `A_{k−1} ≠ ∅` -/
  top_nonempty : (A (k - 1)).Nonempty
  /-- `A_k = ∅` -/
  last : A k = ∅

/-- §2, p.7: `d(u, X) = min_{x ∈ X} d(u, x)`, with value `⊤ = ∞` on the empty set. -/
noncomputable def distToSet (G : Graph) (X : Finset (Fin G.n)) (u : Fin G.n) : WithTop ℝ :=
  X.inf fun w => ((dist G u w : ℝ) : WithTop ℝ)

/-- §2, p.7: `B_i(u) = {w ∈ A_i | d(u, w) < h_{i+1}(u)}`, where `h_{i+1}(u) = d(u, A_{i+1})`
(which is `∞` when `A_{i+1} = ∅`). -/
noncomputable def bunchAt {G : Graph} {k : ℕ} (A : Hierarchy G k) (i : ℕ) (u : Fin G.n) :
    Finset (Fin G.n) := by
  classical
  exact (A.A i).filter fun w => ((dist G u w : ℝ) : WithTop ℝ) < distToSet G (A.A (i + 1)) u

/-- §2, p.7: the bunch `B(u) = ⋃_{i ∈ [k]} B_i(u)`. -/
noncomputable def bunch {G : Graph} {k : ℕ} (A : Hierarchy G k) (u : Fin G.n) : Finset (Fin G.n) :=
  (Finset.range k).biUnion fun i => bunchAt A i u

/-- §2, p.7: a choice of pivots `p_i(u) ∈ arg min_{w ∈ A_i} d(u, w)` for every level `i ∈ [k]`. -/
structure PivotChoice {G : Graph} {k : ℕ} (A : Hierarchy G k) where
  /-- the `i`-th pivot `p_i(u)` -/
  p : ℕ → Fin G.n → Fin G.n
  /-- `p_i(u) ∈ A_i` -/
  mem : ∀ i < k, ∀ u, p i u ∈ A.A i
  /-- `p_i(u)` is a closest vertex of `A_i` to `u` -/
  min : ∀ i < k, ∀ u, ∀ w ∈ A.A i, dist G u (p i u) ≤ dist G u w

/-- §2, p.7: `h_i(u) := d(u, p_i(u))` (for `i ∈ [k]`). -/
noncomputable def PivotChoice.h {G : Graph} {k : ℕ} {A : Hierarchy G k} (P : PivotChoice A)
    (i : ℕ) (u : Fin G.n) : ℝ :=
  dist G u (P.p i u)

/-- §2, p.7: the one-level growth `∆_i(x) = h_i(x) − h_{i−1}(x)` (for `1 ≤ i < k`). -/
noncomputable def PivotChoice.oneLevel {G : Graph} {k : ℕ} {A : Hierarchy G k} (P : PivotChoice A)
    (i : ℕ) (x : Fin G.n) : ℝ :=
  P.h i x - P.h (i - 1) x

/-- §2, p.7: the two-level growth `∇_i(x) = h_i(x) − h_{i−2}(x)` (for `2 ≤ i < k`). -/
noncomputable def PivotChoice.twoLevel {G : Graph} {k : ℕ} {A : Hierarchy G k} (P : PivotChoice A)
    (i : ℕ) (x : Fin G.n) : ℝ :=
  P.h i x - P.h (i - 2) x

end TZLevelsADO


