-- Prove2me | Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
-- name    : OrabonaOL_OGD_IsEuclideanProj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:01:48.096741+00:00
-- url     : https://prove2.me/theorems/44cdd326-6658-4507-b248-19e0ae6f9f32
-- title:
--   Euclidean projection onto a set (argmin predicate)
-- statement:
--   Let $V \subseteq \mathbb{R}^d$ and $z \in \mathbb{R}^d$, where $\mathbb{R}^d$ carries the Euclidean norm $\|\cdot\|_2$. A point $p$ is a **Euclidean projection of $z$ onto $V$** if
--
--   $$
--   p \in V \quad\text{and}\quad \|z - p\|_2 \le \|z - y\|_2 \ \text{ for all } y \in V,
--   $$
--
--   that is, $p \in \operatorname{argmin}_{y \in V} \|z - y\|_2$.
--
--   When $V$ is non-empty, closed and convex, exactly one such point exists; it is the point the book denotes $\Pi_V(z)$ and uses in the update of Projected Online Gradient Descent (Algorithm 2.1) and in Proposition 2.11.
--
--   **Formalization Note** The projection is encoded as a predicate rather than a function, so no default value is produced when the minimizer does not exist. Existence and uniqueness for non-empty closed convex $V$ are Mathlib facts (`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`); hence a statement made for every $p$ satisfying the predicate is a statement about $\Pi_V(z)$. The ambient space is `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 12 (PDF p. 24), definition of Π_V in the sentence before Proposition 2.11 and line 5 of Algorithm 2.1

import Mathlib

namespace OrabonaOL.OGD

/-- **Euclidean projection onto a set, as an argmin predicate.**
Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 12 (PDF p. 24),
sentence before Proposition 2.11 and line 5 of Algorithm 2.1:
"the unique point `Π_V(x) := argmin_{y ∈ V} ‖x − y‖₂`".

`IsEuclideanProj V z p` says that `p ∈ V` and `p` minimizes `y ↦ ‖z − y‖₂` over `V`.

**Formalization Note.** The ambient space is `ℝ^d = EuclideanSpace ℝ (Fin d)` with the
Euclidean norm. The projection is encoded as a predicate instead of a function, so that no
junk value is produced when the argmin does not exist. For a non-empty closed convex `V` a
point `p` with `IsEuclideanProj V z p` exists and is unique (Mathlib
`exists_norm_eq_iInf_of_complete_convex` and `norm_eq_iInf_iff_real_inner_le_zero`), so
"every `p` with `IsEuclideanProj V z p`" is exactly the book's `Π_V(z)`. -/
def IsEuclideanProj {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (z p : EuclideanSpace ℝ (Fin d)) : Prop :=
  p ∈ V ∧ ∀ y ∈ V, ‖z - p‖ ≤ ‖z - y‖

end OrabonaOL.OGD


