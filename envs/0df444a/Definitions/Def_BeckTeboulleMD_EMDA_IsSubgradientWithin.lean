-- Prove2me | Definitions.Def_BeckTeboulleMD_EMDA_IsSubgradientWithin
-- name    : BeckTeboulleMD_EMDA_IsSubgradientWithin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:07.28083+00:00
-- url     : https://prove2.me/theorems/e335be47-b2ae-45ad-a04c-4c2da844cc3a
-- title:
--   Subgradient of $f$ relative to $X$, Assumption A(d)
-- statement:
--   Let $X$ be a subset of a real normed space $E$, let $f$ be a real function defined (at least) on $X$, and let $x\in X$. A continuous linear functional $g$ on $E$ is a **subgradient of $f$ at $x$ relative to $X$** if
--   $$
--   f(x)+g(y-x)\le f(y)\qquad\text{for all } y\in X .
--   $$
--
--   In the paper $f:X\to\mathbb R$ is defined on the feasible set only, so its subdifferential $\partial f(x)$ consists of exactly these functionals; Assumption A(d) supposes one element $f'(x)\in\partial f(x)$ is available at every $x\in X$. The subgradients drive the SANP and EMDA iterations.
--
--   **Formalization Note** On $\mathbb R^n$ the paper writes the subgradient as a vector $f'(x)$ acting through $\langle\cdot,f'(x)\rangle$; here it is the functional itself, and its operator norm is the paper's dual norm $\|f'(x)\|_*=\max\{\langle z,f'(x)\rangle:\|z\|\le1\}$ (p. 171). Values of $f$ off $X$ are never read.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003) 167–175, doi:10.1016/s0167-6377(02)00231-6, §1, Assumption A(d), printed p. 167 (PDF p. 1)

import Mathlib

namespace BeckTeboulleMD.EMDA

/-- **Subgradient of `f : X → ℝ` at `x`, Assumption A(d).**
Beck & Teboulle, *Mirror descent and nonlinear projected subgradient methods for convex
optimization*, Oper. Res. Lett. 31 (2003), §1, Assumption A(d), printed p. 167 (PDF p. 1):
"A subgradient of f at x ∈ X is computable. An element of the subdifferential ∂f(x) is denoted by
f′(x)."

`IsSubgradientWithin X f x g` says that the continuous linear functional `g` is a subgradient of
`f` at `x` relative to `X`: `f x + g (y - x) ≤ f y` for every `y ∈ X`.

**Formalization Note.** The paper's `f` is defined on `X` only, so its subdifferential is taken
relative to `X`; the inequality is required for `y ∈ X` only and values of `f` off `X` are never
read. The paper's vector `f′(x) ∈ ℝⁿ` acts through the pairing `⟨·, f′(x)⟩`; here it is the
functional `g` itself, whose operator norm `‖g‖` is the paper's dual norm `‖f′(x)‖_*`
(p. 171: `‖z‖_* = max{⟨x, z⟩ : ‖x‖ ≤ 1}`). -/
def IsSubgradientWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ X, f x + g (y - x) ≤ f y

end BeckTeboulleMD.EMDA


