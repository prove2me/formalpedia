-- Prove2me | Definitions.Def_ProxAlg_FixedPoint_Basic
-- name    : ProxAlg_FixedPoint_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:17.731992+00:00
-- url     : https://prove2.me/theorems/f957f3f3-2c29-4e07-a791-d289bdc668c6
-- title:
--   (2.3), p. 131 — the subdifferential of a closed proper convex function
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be a closed proper convex function. Its **subdifferential** at $x$ is the set of vectors $y$ satisfying the supporting inequality
--   $$
--   \partial f(x)=\{y\in\mathbb R^n\mid f(z)\ge f(x)+y^{\mathsf T}(z-x)\text{ for every }z\in\operatorname{dom}f\}.
--   $$
--
--   This is the point-to-set operator used in the proximal optimality condition and the resolvent identity. It is empty outside the effective domain.
--
--   **Formalization Note** The definition explicitly requires $x\in\operatorname{dom}f$ and tests every $z\in\mathbb R^n$. A point outside $\operatorname{dom}f$ has value $+\infty$, so its inequality is automatic when $x$ has finite value. The inner product is the Euclidean one, and the function takes values in `EReal`.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §2.3, p. 131, (2.3)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

namespace ProxAlg.FixedPoint

open scoped InnerProductSpace

/-- The subdifferential in Parikh--Boyd (2.3), defined at points of the effective
domain. Testing all `z` is equivalent to testing `z` in that domain for functions
with no `-∞` values: outside it the right side is `⊤`. -/
def subdifferential {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | f x < ⊤ ∧ ∀ z, f x + ((⟪y, z - x⟫_ℝ : ℝ) : EReal) ≤ f z}

end ProxAlg.FixedPoint


