-- Prove2me | Definitions.Def_BubeckCO_PSGD_IsEuclideanProj
-- name    : BubeckCO_PSGD_IsEuclideanProj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:54.956399+00:00
-- url     : https://prove2.me/theorems/d1d2540e-3a31-4f67-b2d5-436e9bc87dee
-- title:
--   Euclidean projection $\Pi_X$ onto a set (argmin predicate)
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ and $z \in \mathbb{R}^n$, with $\|\cdot\|$ the Euclidean norm. A point $p$ is a **Euclidean projection of $z$ onto $X$** if
--
--   $$
--   p \in X \quad\text{and}\quad \|z - p\| \le \|z - y\| \ \text{ for all } y \in X,
--   $$
--
--   that is, $p \in \operatorname{argmin}_{y \in X} \|z - y\|$. For a non-empty closed convex $X$ exactly one such point exists; it is the point the monograph denotes $\Pi_X(z)$ and uses in the projection step (3.3) of projected subgradient descent and in Lemma 3.1.
--
--   **Formalization Note** The projection is a predicate rather than a function, so no default value arises when the argmin does not exist. Existence and uniqueness for non-empty closed convex $X$ are Mathlib facts (`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`); hence a statement about every $p$ satisfying the predicate is a statement about $\Pi_X(z)$.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, p. 263 (PDF p. 36), definition of the projection operator Π_X before Lemma 3.1

import Mathlib

namespace BubeckCO.PSGD

/-- **Euclidean projection onto `X`, as an argmin predicate.**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
p. 263 (PDF p. 36): "We define the projection operator `Π_X` on `X` by
`Π_X(x) = argmin_{y ∈ X} ‖x − y‖`."

`IsEuclideanProj X z p` says that `p ∈ X` and `‖z − p‖ ≤ ‖z − y‖` for every `y ∈ X`.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, and `‖·‖` is the Euclidean norm (the
norm of Chapter 3 outside §3.3). The projection is a predicate rather than a function, so no junk
value arises when the argmin does not exist. For a non-empty closed convex `X` (in particular the
compact convex constraint sets of Chapter 3) a point `p` with `IsEuclideanProj X z p` exists and is
unique (Mathlib `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`),
so a statement about every such `p` is a statement about `Π_X(z)`. -/
def IsEuclideanProj {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (z p : EuclideanSpace ℝ (Fin n)) : Prop :=
  p ∈ X ∧ ∀ y ∈ X, ‖z - p‖ ≤ ‖z - y‖

end BubeckCO.PSGD


