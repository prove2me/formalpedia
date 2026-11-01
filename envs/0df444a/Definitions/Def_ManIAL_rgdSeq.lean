-- Prove2me | Definitions.Def_ManIAL_rgdSeq
-- name    : ManIAL_rgdSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:11.823364+00:00
-- url     : https://prove2.me/theorems/7025a5fe-f315-4b91-a8c7-256420cd9583
-- title:
--   Iterates of Riemannian gradient descent (Algorithm 2)
-- statement:
--   Given $\psi$, $L>0$ and a starting point $x_0\in\mathcal M$, Riemannian gradient descent with constant stepsize $1/L$ produces
--
--   $$
--   x_{t+1}=R_{x_t}\Big(-\frac1L\operatorname{grad}\psi(x_t)\Big),\qquad t=0,1,2,\dots
--   $$
--
--   Algorithm 2, $\mathrm{RGD}(\psi,L,T,x_0)$, runs this recursion and outputs $x_{t^*}$ with $t^*\in\arg\min_{0\le t\le T}\|\operatorname{grad}\psi(x_t)\|$. It is the subroutine with which ManIAL solves its subproblems.
--
--   **Formalization Note** The sequence is defined for all $t$; the statements of the mission choose the output index $t^*$ explicitly (any minimizer, or the first iterate meeting a stopping test).
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Algorithm 2, display (3.18), p.10

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad

open ZORiem.RGD

namespace ManIAL

/-- The iterates of Riemannian gradient descent, Algorithm 2 `RGD(ψ, L, T, x₀)`
(Deng–Hu–Wu–Wen, arXiv:2404.05121v2, display (3.18), p.10): `x_0 = x₀` and
`x_{t+1} = R_{x_t}(−(1/L) grad ψ(x_t))` (stepsize `α_t = 1/L`).

**Formalization Note.** The sequence is infinite; Algorithm 2 with an integer `T` uses
`x_0, …, x_T` and outputs an `x_{t*}` with `t* ∈ argmin_{0 ≤ t ≤ T} ‖grad ψ(x_t)‖`; the
statements that use it quantify over `t*`. `grad ψ` is `rgrad M ψ`. -/
noncomputable def rgdSeq {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | t + 1 => R (rgdSeq M R ψ L x₀ t) (-(1 / L) • rgrad M ψ (rgdSeq M R ψ L x₀ t))

end ManIAL


