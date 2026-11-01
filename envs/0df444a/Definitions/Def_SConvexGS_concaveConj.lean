-- Prove2me | Definitions.Def_SConvexGS_concaveConj
-- name    : SConvexGS_concaveConj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:10.013353+00:00
-- url     : https://prove2.me/theorems/2a3a6461-15e2-435b-af30-f2aea7301519
-- title:
--   Concave conjugate $f_*$
-- statement:
--   For $f$ with $\operatorname{dom}(f)\ne\emptyset$, the **concave conjugate** is
--
--   $$f_*(p)=\inf\{p^{T}x-f(x)\mid x\in\operatorname{dom}(f)\},\qquad p\in\mathbb R^n.$$
--
--   It is the object of Theorem 7 and Lemma EC.2, on the concave side.
--
--   **Formalization Note** The infimum is taken in `EReal`. At $\operatorname{dom}(f)=\emptyset$, where the paper does not define the conjugate, the `def` is $+\infty$.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §3.2, p.14

import Mathlib
import Definitions.Def_SConvexGS_dom

open Matrix

namespace SConvexGS

/-- The concave conjugate `f₍*₎(p) = inf{pᵀx − f(x) | x ∈ dom(f)}`, `p ∈ ℝⁿ` (Chen, Li, *S-Convexity
and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), §3.2, p.14).

Formalization Note: the infimum is taken in `EReal` over `dom f`, so `pᵀx − f(x)` is a difference
of finite values and neither `⊤ − ⊤` nor `⊥ − ⊥` occurs. The paper defines the conjugate for
`dom f ≠ ∅` only; at `dom f = ∅` this `def` is `⊤`. -/
noncomputable def concaveConj {n : ℕ} (f : (Fin n → ℝ) → EReal) (p : Fin n → ℝ) : EReal :=
  ⨅ x ∈ dom f, ((p ⬝ᵥ x : ℝ) : EReal) - f x

end SConvexGS


