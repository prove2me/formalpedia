-- Prove2me | Definitions.Def_PertComp_persp
-- name    : PertComp_persp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:59.850061+00:00
-- url     : https://prove2.me/theorems/946e1627-6d06-4831-8785-af57688dc445
-- title:
--   Perspective $\widetilde f$
-- statement:
--   The **perspective** of $f\colon V\to\,]-\infty,+\infty]$ is $\widetilde f\colon V\times\mathbb R\to\,]-\infty,+\infty]$,
--   $$\widetilde f(x,\xi)=\begin{cases}\xi f(x/\xi), & \xi>0;\\ (\operatorname{rec} f)(x), & \xi=0;\\ +\infty, & \text{otherwise.}\end{cases}$$
--   Lemma 2.2(ii) relates the conjugate of $\widetilde f(\cdot,\xi)$ to $\xi\odot f^*$, and the dual objective (3.11) contains the perspective $\widetilde{f^*}$ of the conjugate $f^*$.
--
--   **Formalization Note** `persp f x ξ` is $\widetilde f(x,\xi)$; $x/\xi$ is $\xi^{-1}x$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (2.7), p.5

import Mathlib
import Definitions.Def_PertComp_recFn

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (2.7), p.5: the *perspective*
`f̃ : V × ℝ → ]−∞, +∞]` of `f`, `f̃(x, ξ) = ξ f(x/ξ)` if `ξ > 0`, `(rec f)(x)` if `ξ = 0`, and
`+∞` otherwise. `persp f x ξ` is `f̃(x, ξ)`.

**Formalization Note.** The pair `(x, ξ)` is curried so that `f̃(·, ξ)` is
`fun x => persp f x ξ`; `x/ξ` is `ξ⁻¹ • x`. -/
noncomputable def persp {V : Type*} [AddCommGroup V] [Module ℝ V] (f : V → EReal) (x : V)
    (ξ : ℝ) : EReal :=
  if 0 < ξ then (ξ : EReal) * f (ξ⁻¹ • x) else if ξ = 0 then recFn f x else ⊤

end PertComp


