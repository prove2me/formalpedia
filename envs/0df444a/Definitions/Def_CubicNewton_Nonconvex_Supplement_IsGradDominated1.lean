-- Prove2me | Definitions.Def_CubicNewton_Nonconvex_Supplement_IsGradDominated1
-- name    : CubicNewton_Nonconvex_Supplement_IsGradDominated1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:59:19.133915+00:00
-- url     : https://prove2.me/theorems/0c43c248-1c95-4659-be22-4ba4bade1589
-- title:
--   Definition 3 with $p=1$ — gradient domination of degree one
-- statement:
--   Let $F\subseteq\mathbb R^n$ and let $f$ have gradient $f'(x)$ on $F$. The function $f$ is **gradient dominated of degree one** on $F$ with constant $\tau_f$ if it attains its global minimum over $\mathbb R^n$ at a point $x^*\in F$, $\tau_f>0$, and for every $x\in F$
--   $$f(x)-f(x^*)\ \le\ \tau_f\,\|f'(x)\|.$$
--   Convex functions on a ball $\{\|x-x^*\|\le R\}$ are an example, with $\tau_f=R$. This is the class of Theorem 6.
--
--   **Formalization Note** The gradient is a map `g` (no differentiability is part of this predicate); the minimum is global over $\mathbb R^n$. Under Section 2, every global minimizer belongs to $F$, since its value is at most $f(x_0)$ and the initial level set lies in $\operatorname{int}F$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 191, Definition 3, (4.7), case p = 1

import Mathlib

namespace CubicNewton.Nonconvex.Supplement

/-- Gradient domination of degree `p = 1` (Nesterov–Polyak 2006, Section 4.2, p. 191,
Definition 3 with `p = 1`): `f` attains its global minimum over `ℝⁿ` at `xs ∈ F`, the constant
`τ` (the paper's `τ_f`) is positive, and for every `x ∈ F`
`f(x) − f(x*) ≤ τ_f ‖f′(x)‖`  (4.7) with `p = 1`,
with `g x` in the role of `f′(x)`. -/
def IsGradDominated1 {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (τ : ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  xs ∈ F ∧ (∀ y, f xs ≤ f y) ∧ 0 < τ ∧ ∀ x ∈ F, f x - f xs ≤ τ * ‖g x‖

end CubicNewton.Nonconvex.Supplement


