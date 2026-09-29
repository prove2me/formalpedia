-- Prove2me | Definitions.Def_BealeConvexMin_RandomLP_expectedCost
-- name    : BealeConvexMin_RandomLP_expectedCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:41:34.758444+00:00
-- url     : https://prove2.me/theorems/328c3915-d3df-476d-98c3-bbc12424680b
-- title:
--   Beale (1955), eqs. (5.1)–(5.4): the cost C(x) and its mean value E(C)
-- statement:
--   Given constants $c\in\mathbb R^n$, $f\in\mathbb R^p$ and $D\in\mathbb R^{m\times p}$, Beale's problem is to choose a non-negative first-stage vector $x\in\mathbb R^n$ to minimise the mean value $E(C)$ of
--   $$C=c'x+f'y,\tag{5.3}$$
--   where the non-negative $y$ is chosen, once the data are known, to minimise $C$ subject to $Ax+Dy=\beta$ (eq. (5.4)). The $m\times n$ matrix $A=(\alpha_{ij})$ and the vector $\beta\in\mathbb R^m$ are random variables whose distribution is known when $x$ is chosen and whose values are known when $y$ is chosen.
--
--   This file defines:
--
--   1. the **cost** for fixed data $(A,\beta)$,
--   $$C(x)=c'x+Q(\beta-Ax),$$
--   where $Q(b)=\inf\{f'y: y\ge0,\ Dy=b\}$ is the second-stage value;
--   2. the **expected cost**: for random data $A(\omega)$, $\beta(\omega)$ on a probability space $(\Omega,P)$,
--   $$E(C)(x)=\int_\Omega \bigl(c'x+Q(\beta(\omega)-A(\omega)x)\bigr)\,dP(\omega).$$
--
--   These are the objects of Theorems 2 and 3 of the paper.
--
--   **Formalization Note** The mean is the Bochner integral, which Lean sets to $0$ for a non-integrable integrand; theorems about $E(C)$ therefore assume integrability of $\omega\mapsto C(x,\omega)$. The value $Q$ is the real infimum, which is a junk $0$ when the second stage is infeasible or unbounded, so theorems also assume attainment of the second-stage minimum.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, pp. 181–182 (PDF pp. 9–10), §5, eqs. (5.1)–(5.4)

import Mathlib
import Definitions.Def_BealeConvexMin_RandomLP_secondStageValue

namespace BealeConvexMin.RandomLP

open Matrix MeasureTheory

/-- Beale (1955), §5, p. 182, eqs. (5.3)–(5.4): for fixed values of the data `A` and `β`, the cost
`C(x) = c′x + min {f′y | y ≥ 0, Ax + Dy = β}`, i.e. the value of `C = c′x + f′y` (eq. (5.3)) when
the second-stage `y` is chosen optimally subject to `Ax + Dy = β` (eq. (5.4)). -/
noncomputable def cost {m n p : ℕ} (c : Fin n → ℝ) (f : Fin p → ℝ)
    (D : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  c ⬝ᵥ x + secondStageValue D f (β - A *ᵥ x)

/-- Beale (1955), §5, p. 181, eq. (5.1): the mean value `E(C)` of the cost as a function of the
first-stage decision `x`, where the random data `A(ω)`, `β(ω)` are defined on a probability space
`(Ω, P)`. This is the Bochner integral, which is `0` when the integrand is not integrable, so
theorems about it assume integrability. -/
noncomputable def expectedCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n p : ℕ}
    (c : Fin n → ℝ) (f : Fin p → ℝ) (D : Matrix (Fin m) (Fin p) ℝ)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) (β : Ω → Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ ω, cost c f D (A ω) (β ω) x ∂P

end BealeConvexMin.RandomLP


