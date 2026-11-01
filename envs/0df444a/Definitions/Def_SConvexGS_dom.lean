-- Prove2me | Definitions.Def_SConvexGS_dom
-- name    : SConvexGS_dom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:20.402773+00:00
-- url     : https://prove2.me/theorems/ca16fd10-c914-4a1b-b081-2582c8769d7c
-- title:
--   Feasible domain $\operatorname{dom}(f)$
-- statement:
--   For a function $f:\mathbb R^n\to[-\infty,\infty]$, the feasible domain is
--
--   $$\operatorname{dom}(f)=\{x\in\mathbb R^n\mid -\infty<f(x)<\infty\}.$$
--
--   Every convexity, conjugacy and exchange statement of the paper is restricted to this set.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, which carries the componentwise order, and values are in `EReal`.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9

import Mathlib

namespace SConvexGS

/-- The feasible domain `dom(f) = {x | −∞ < f(x) < ∞}` of an extended-real-valued function
(Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9).

Formalization Note: ℝⁿ is `Fin n → ℝ`, values are in `EReal`, with `⊤ = +∞` and `⊥ = −∞`. -/
def dom {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | f x ≠ ⊤ ∧ f x ≠ ⊥}

end SConvexGS


