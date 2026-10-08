-- Prove2me | Definitions.Def_RobinsonSR_IFT_Setting
-- name    : RobinsonSR_IFT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:20.899057+00:00
-- url     : https://prove2.me/theorems/c1249441-0f4e-47b4-97fc-1a2774c9faa7
-- title:
--   §1 and DEFINITION, pp. 43, 45 — normal-cone operator ∂ψ_C, strong regularity at x₀ with Lipschitz constant λ, residual r(p, x)
-- statement:
--   Let $X$ be a real normed linear space with topological dual $X'$ (the continuous linear functionals on $X$), and let $C\subseteq X$.
--
--   1. **Normal-cone operator** (§1, p. 43). For $x\in X$,
--   $$\partial\psi_C(x) := \begin{cases}\{y\in X' : y(c-x)\le 0 \text{ for all } c\in C\}, & x\in C,\\ \emptyset, & x\notin C.\end{cases}$$
--   A generalized equation $0\in f(x)+\partial\psi_C(x)$ is thus the membership $-f(x)\in\partial\psi_C(x)$, and it forces $x\in C$.
--
--   2. **Strong regularity** (DEFINITION, p. 45). Let $x_0\in X$, $a\in X'$ and $A$ a bounded linear operator from $X$ to $X'$, and set
--   $$T x := a + A(x-x_0) + \partial\psi_C(x), \qquad x\in X .$$
--   The generalized equation is **strongly regular at $x_0$ with associated Lipschitz constant $\lambda$** if there are neighbourhoods $U$ of the origin in $X'$ and $V$ of $x_0$ such that the restriction to $U$ of $T^{-1}\cap V$ is a single-valued function $s:U\to V$ which is Lipschitzian on $U$ with modulus $\lambda$: for every $y\in U$, $s(y)\in V$ satisfies $y\in T\,s(y)$; it is the only $x\in V$ with $y\in Tx$; and $\|s(y_1)-s(y_2)\|\le\lambda\|y_1-y_2\|$ for all $y_1,y_2\in U$. In the paper $a=f(x_0)$ and $A=f'(x_0)$ for a function $f$ Fréchet differentiable at a solution $x_0$ of $0\in f(x)+\partial\psi_C(x)$.
--
--   3. **Residual** (proof of Theorem 2.1, p. 45). For a parametrised $f:P\times X\to X'$ with partial derivative $f'(p,x)$ in $x$, and a base point $(p_0,x_0)$,
--   $$r(p,x) := f(p_0,x_0)+f'(p_0,x_0)(x-x_0)-f(p,x).$$
--
--   These are the objects of the implicit-function theorem for generalized equations (Theorem 2.1) and of its corollaries.
--
--   **Formalization Note** $X'$ is Mathlib's `StrongDual ℝ X`. The normal cone carries the clause $x\in C$, so it is empty off $C$, as on the page. Strong regularity is stated on the linearisation's data $(a, A)$ only, since $T$ depends on $f$ only through $f(x_0)$ and $f'(x_0)$; the standing assumptions of the DEFINITION ($\Omega$ open, $C$ closed convex, differentiability, $x_0$ a solution) are hypotheses of each theorem. $\lambda$ is a real number, not required to be nonnegative, because the page does not require it. Neighbourhoods are filter neighbourhoods, not necessarily open.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), pp. 43, 45, (1.1), DEFINITION, and proof of Theorem 2.1 (definition of r(p, x))

import Mathlib

namespace RobinsonSR.IFT

open scoped Topology

/-- The normal-cone operator `∂ψ_C` (Robinson 1980, §1, p. 43): for `x ∈ C` it is the set of
continuous linear functionals `y ∈ X′` with `y (c - x) ≤ 0` for all `c ∈ C`; for `x ∉ C` it is `∅`. -/
def normalCone {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (x : X) : Set (StrongDual ℝ X) :=
  {y | x ∈ C ∧ ∀ c ∈ C, y (c - x) ≤ 0}

/-- Strong regularity (DEFINITION, p. 45), stated on the data of the linearisation:
`a` plays `f(x₀)` and `A` plays `f′(x₀)`, so that `T x = a + A (x - x₀) + ∂ψ_C(x)`.
The generalized equation is strongly regular at `x₀` with associated Lipschitz constant `lam`
if there are neighbourhoods `U` of `0` in `X′` and `V` of `x₀` such that the restriction to `U`
of `T⁻¹ ∩ V` is a single-valued function `s : U → V` that is Lipschitzian on `U` with modulus
`lam`: for each `y ∈ U`, `s y ∈ V` solves `y ∈ T (s y)`, it is the only solution in `V`, and
`‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖` on `U`. -/
def StronglyRegular {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (a : StrongDual ℝ X) (A : X →L[ℝ] StrongDual ℝ X) (x0 : X) (lam : ℝ) : Prop :=
  ∃ U ∈ 𝓝 (0 : StrongDual ℝ X), ∃ V ∈ 𝓝 x0, ∃ s : StrongDual ℝ X → X,
    (∀ y ∈ U, s y ∈ V ∧ y - (a + A (s y - x0)) ∈ normalCone C (s y) ∧
       ∀ x ∈ V, y - (a + A (x - x0)) ∈ normalCone C x → x = s y) ∧
    ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖

/-- The residual of the proof of Theorem 2.1 (p. 45):
`r(p, x) = f(p₀, x₀) + f′(p₀, x₀)(x − x₀) − f(p, x)`, where `f′` is the partial Fréchet derivative
of `f` in its second variable. -/
noncomputable def residual {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {P : Type*}
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X)) (p0 : P) (x0 : X)
    (p : P) (x : X) : StrongDual ℝ X :=
  f p0 x0 + f' p0 x0 (x - x0) - f p x

end RobinsonSR.IFT


