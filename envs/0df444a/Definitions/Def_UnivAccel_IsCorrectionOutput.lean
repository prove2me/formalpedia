-- Prove2me | Definitions.Def_UnivAccel_IsCorrectionOutput
-- name    : UnivAccel_IsCorrectionOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:04.885014+00:00
-- url     : https://prove2.me/theorems/483ab48e-6b29-4b3f-ad60-aa300e88297a
-- title:
--   Definition 1 — correction oracle answer, eq. (25)
-- statement:
--   Let $f$ be differentiable and $\mu$-strongly convex. A **correction oracle** for $f$ takes a query point $y$ and returns a corrected point $u$ and a parameter $\lambda \ge 0$ such that, for some $p \in \{y, u\}$,
--   $$
--   \lambda (y - u) = \nabla f(p) + \mu (u - p). \tag{25}
--   $$
--   The predicate says that $(u, \lambda)$ is such an answer at $y$. With $p = y$ the oracle takes an explicit gradient step; with $p = u$ an implicit (proximal) one. The ball oracle is the case $p = u$, $\lambda = \|\nabla f(u)\|/r$.
--
--   **Formalization Note** The standing hypotheses of Definition 1 ($f$ differentiable and $\mu$-strongly convex) are assumed by the theorems that use the predicate, not built into it. `λ` is a Lean keyword, so the parameter is called `lam`.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), Definition 1, eq. (25), p.15

import Mathlib

namespace UnivAccel

/-- Definition 1 (Correction oracle) (Adil–Kyng, *Universal Acceleration: New Approaches to
Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), p.15):
for a query point `y`, the pair `(u, λ)` is a valid answer of a correction oracle for `f` with
parameter `μ` if `λ ≥ 0` and, for some `p ∈ {y, u}`,
`λ (y − u) = ∇f(p) + μ (u − p)`  (25).

**Formalization Note** The standing hypotheses of Definition 1 (`f` differentiable and
`μ`-strongly convex) are not part of the predicate; theorems using it assume them. `λ` is a Lean
keyword, so the parameter is named `lam`. -/
def IsCorrectionOutput {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (μ : ℝ) (y u : E) (lam : ℝ) : Prop :=
  0 ≤ lam ∧ ∃ p : E, (p = y ∨ p = u) ∧ lam • (y - u) = gradient f p + μ • (u - p)

end UnivAccel


