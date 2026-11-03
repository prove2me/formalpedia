-- Prove2me | Definitions.Def_PertComp_Psi
-- name    : PertComp_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:19.194798+00:00
-- url     : https://prove2.me/theorems/50e863ca-9055-48ea-8960-d883c57ba950
-- title:
--   The perturbation $\Psi$ of $\varphi\circ f$ (3.1)
-- statement:
--   For $\varphi\colon\mathbb R\to\,]-\infty,+\infty]$ and $f\colon X\to\,]-\infty,+\infty]$, the function $\Psi\colon X\oplus\mathbb R\to\,]-\infty,+\infty]$ is
--   $$\Psi(x,\xi)=\begin{cases}\varphi\big(f(x)+\xi\big), & f(x)+\xi\in\operatorname{dom}\varphi;\\ +\infty, & f(x)+\xi\notin\operatorname{dom}\varphi.\end{cases}$$
--   Since $\Psi(x,0)=(\varphi\circ f)(x)$, it is a perturbation of $\varphi\circ f$ in the sense of Definition 2.10, with perturbation space $U=\mathbb R$.
--
--   The helper `realDual` is the identification $\xi^*\mapsto(\xi\mapsto\xi\xi^*)$ of $\mathbb R$ with $\mathbb R^*$, by which the paper writes the dual variable of $\Psi$ as a real number.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 3.1, (3.1), p.10

import Mathlib

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, Proposition 3.1, (3.1), p.10: the perturbation
`Ψ : X ⊕ ℝ → ]−∞, +∞]` of `φ ∘ f`, `Ψ(x, ξ) = φ(f(x) + ξ)` if `f(x) + ξ ∈ dom φ` and `+∞` if
`f(x) + ξ ∉ dom φ`.

**Formalization Note.** `X ⊕ ℝ` is the Lean product `X × ℝ`. `f(x) + ξ ∈ dom φ` means `f x` is
real and `φ` is finite at `f(x) + ξ`. -/
noncomputable def Psi {X : Type*} (φ : ℝ → EReal) (f : X → EReal) : X × ℝ → EReal :=
  fun p => if f p.1 ≠ ⊤ ∧ φ ((f p.1).toReal + p.2) ≠ ⊤ then φ ((f p.1).toReal + p.2) else ⊤

/-- The identification `ℝ ≅ ℝ*`, `ξ* ↦ (ξ ↦ ξ ξ*)`, by which the paper writes the dual variable
of `Ψ` as a real number `ξ*` (Proposition 3.1, p.10). -/
noncomputable def realDual (s : ℝ) : StrongDual ℝ ℝ :=
  s • ContinuousLinearMap.id ℝ ℝ

end PertComp


