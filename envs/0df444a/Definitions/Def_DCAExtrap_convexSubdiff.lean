-- Prove2me | Definitions.Def_DCAExtrap_convexSubdiff
-- name    : DCAExtrap_convexSubdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:17.489114+00:00
-- url     : https://prove2.me/theorems/4ab43102-b588-4598-ab17-82d69e491650
-- title:
--   Convex subdifferential $\partial J(x)$ of an extended-real function
-- statement:
--   Let $J:E\to(-\infty,+\infty]$ and $x\in\operatorname{dom}J$. The **subdifferential in the sense of convex analysis** is
--
--   $$
--   \partial J(x) := \{v\in E : J(y)\ge J(x)+\langle v, y-x\rangle \ \text{for all } y\in E\}.
--   $$
--
--   Outside $\operatorname{dom}J$ it is empty. It is used for the convex components $g$ and $h$ of problem (1): in Algorithm 1 ($\xi^k\in\partial h(x^k)$) and in the definition of a critical point.
--
--   **Formalization Note** $J$ is `EReal`-valued and membership requires $J(x)\neq+\infty$. A real-valued $h$ is used through its coercion to `EReal`.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, §2, p.4, ∂J(x*) := {y : J(x) ≥ J(x*) + ⟨x − x*, y⟩, ∀x ∈ E}

import Mathlib

open scoped InnerProductSpace

namespace DCAExtrap

/-- **Subdifferential in the sense of convex analysis** (Phan–Le Thi, arXiv:2106.04743v1, §2,
p.4): for `J : E → (−∞, +∞]` and `x* ∈ dom J`,
`∂J(x*) := {y : J(x) ≥ J(x*) + ⟨x − x*, y⟩, ∀ x ∈ E}`.

**Formalization Note.** `J` is `EReal`-valued. The condition `J x ≠ ⊤` encodes the paper's
standing requirement `x* ∈ dom J` (the subdifferential is empty outside the domain). A real-valued
function `h` is used through its coercion `fun x => (h x : EReal)`, for which this condition is
automatic. -/
def convexSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : E → EReal) (x : E) : Set E :=
  {v | J x ≠ ⊤ ∧ ∀ y : E, J x + ((⟪v, y - x⟫_ℝ : ℝ) : EReal) ≤ J y}

end DCAExtrap


