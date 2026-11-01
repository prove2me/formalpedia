-- Prove2me | Definitions.Def_SConvexGS_convexConj
-- name    : SConvexGS_convexConj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:12.055486+00:00
-- url     : https://prove2.me/theorems/3119dc53-7782-415e-8592-be876666e057
-- title:
--   Convex conjugate $f^*$
-- statement:
--   For $f$ with $\operatorname{dom}(f)\ne\emptyset$, the **convex conjugate** is
--
--   $$f^*(p)=\sup\{p^{T}x-f(x)\mid x\in\operatorname{dom}(f)\},\qquad p\in\mathbb R^n.$$
--
--   It is the object of Theorem 3, on the convex side.
--
--   **Formalization Note** The supremum is taken in `EReal`. At $\operatorname{dom}(f)=\emptyset$, where the paper does not define the conjugate, the `def` is $-\infty$.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §3.2, p.14

import Mathlib
import Definitions.Def_SConvexGS_dom

open Matrix

namespace SConvexGS

/-- The convex conjugate `f*(p) = sup{pᵀx − f(x) | x ∈ dom(f)}`, `p ∈ ℝⁿ` (Chen, Li, *S-Convexity
and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), §3.2, p.14).

Formalization Note: the supremum is taken in `EReal` over `dom g`, so `pᵀx − g(x)` is a difference
of finite values and neither `⊤ − ⊤` nor `⊥ − ⊥` occurs. The paper defines the conjugate for
`dom g ≠ ∅` only; at `dom g = ∅` this `def` is `⊥`. -/
noncomputable def convexConj {n : ℕ} (g : (Fin n → ℝ) → EReal) (p : Fin n → ℝ) : EReal :=
  ⨆ x ∈ dom g, ((p ⬝ᵥ x : ℝ) : EReal) - g x

end SConvexGS


