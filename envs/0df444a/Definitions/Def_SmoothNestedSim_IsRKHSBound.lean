-- Prove2me | Definitions.Def_SmoothNestedSim_IsRKHSBound
-- name    : SmoothNestedSim_IsRKHSBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:17.731194+00:00
-- url     : https://prove2.me/theorems/a906bb68-319c-4153-9121-4a219e4979eb
-- title:
--   Bound $C$ on the squared RKHS norm (Aronszajn's criterion)
-- statement:
--   Let $k$ be a kernel on a set $E$, $\Omega\subseteq E$, $f:E\to\mathbb R$ and $C\in\mathbb R$. We say that **$C$ bounds the squared RKHS norm of $f$** if $C\ge 0$ and for every $N$, all $c_1,\dots,c_N\in\mathbb R$ and all $x_1,\dots,x_N\in\Omega$,
--
--   $$
--   \Bigl(\sum_{i=1}^N c_i f(x_i)\Bigr)^2 \le C \sum_{i=1}^N\sum_{j=1}^N c_i c_j\, k(x_i,x_j).
--   $$
--
--   For a positive definite kernel, $f$ belongs to the RKHS $\mathcal N_k(\Omega)$ (the closure of $\operatorname{span}\{k(\cdot,x):x\in\Omega\}$ under the inner product $\langle\sum\beta_i k(\cdot,x_i),\sum\tilde\beta_j k(\cdot,\tilde x_j)\rangle=\sum_{i,j}\beta_i\tilde\beta_j k(x_i,\tilde x_j)$) with $\|f\|^2_{\mathcal N_k(\Omega)}\le C$ exactly when $C$ bounds its squared norm in this sense (Aronszajn 1950; Paulsen and Raghupathi 2016, Theorem 3.11). This predicate is the building block of the RKHS and its norm below.
--
--   **Formalization Note** Only the values of $f$ on $\Omega$ enter.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3, p.11 (construction of N_k(Ω))

import Mathlib

namespace SmoothNestedSim

/-- **`C` bounds the squared RKHS norm of `f`** for a kernel `k` on `Ω` (Aronszajn's
criterion): `C ≥ 0` and for every `N`, all coefficients `c₁, …, c_N ∈ ℝ` and all points
`x₁, …, x_N ∈ Ω`,
`(Σᵢ cᵢ f(xᵢ))² ≤ C · Σᵢ Σⱼ cᵢ cⱼ k(xᵢ, xⱼ)`.

This is the auxiliary predicate behind the function-space description of the RKHS
`N_k(Ω)` of Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6, §3, p.11
(the closure of `N⁰_k(Ω) = span{k(·, x) : x ∈ Ω}` under
`⟨Σ βᵢ k(·,xᵢ), Σ β̃ⱼ k(·,x̃ⱼ)⟩ := Σᵢ Σⱼ βᵢ β̃ⱼ k(xᵢ, x̃ⱼ)`).

**Formalization Note.** For a positive definite kernel `k`, a function `f : Ω → ℝ` lies in
that closure with `‖f‖²_{N_k(Ω)} ≤ C` if and only if `C · k − f ⊗ f` is a positive
semidefinite kernel on `Ω`, which is the displayed inequality (Aronszajn 1950; Paulsen and
Raghupathi, *An Introduction to the Theory of Reproducing Kernel Hilbert Spaces*, 2016,
Theorem 3.11). Only the values of `f` on `Ω` enter. -/
def IsRKHSBound {E : Type*} (k : E → E → ℝ) (Ω : Set E) (f : E → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (N : ℕ) (c : Fin N → ℝ) (x : Fin N → E), (∀ i, x i ∈ Ω) →
    (∑ i, c i * f (x i)) ^ 2 ≤ C * ∑ i, ∑ j, c i * c j * k (x i) (x j)

end SmoothNestedSim


