-- Prove2me | Definitions.Def_OWFLocalDesc_Negligible
-- name    : OWFLocalDesc_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:02.585212+00:00
-- url     : https://prove2.me/theorems/118b76f1-4148-4f5c-b452-9c63a3cb613e
-- title:
--   Negligible function (Definition 2.2)
-- statement:
--   A nonnegative function $\varepsilon:\mathbb N\to\mathbb R$ is **negligible** if for every positive polynomial $p$ there is $n_0$ with
--   $$\varepsilon(n)\le \frac{1}{p(n)}\qquad\text{for all } n\ge n_0.$$
--
--   This is the smallness notion of one-way security.
--
--   **Formalization Note** Positive polynomials are polynomials with natural coefficients whose values are at least $1$ everywhere. Every positive real polynomial is dominated pointwise by such a polynomial, so the notion is unchanged.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.2, p.11

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Negligible error (Definition 2.2).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.2, p.11: "A nonnegative function ε(n) is negligible if, for every positive polynomial
p, it satisfies ε(n) ≤ 1/p(n) at all sufficiently large n."

**Formalization Note.** Positive polynomials are taken with natural coefficients and value at
least `1` everywhere. Every positive real polynomial is dominated pointwise by such a polynomial,
and every such polynomial is positive, so the notion is unchanged. -/
def Negligible (ε : ℕ → ℝ) : Prop :=
  ∀ p : Polynomial ℕ, (∀ n, 1 ≤ p.eval n) → ∃ n₀ : ℕ, ∀ n ≥ n₀, ε n ≤ 1 / ((p.eval n : ℕ) : ℝ)

end OWFLocalDesc


