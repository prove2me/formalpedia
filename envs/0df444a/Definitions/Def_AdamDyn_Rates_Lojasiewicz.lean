-- Prove2me | Definitions.Def_AdamDyn_Rates_Lojasiewicz
-- name    : AdamDyn_Rates_Lojasiewicz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:01:46.348923+00:00
-- url     : https://prove2.me/theorems/fcbe6f62-9f04-47fd-928f-cae9f825518a
-- title:
--   The critical set $\mathcal S$, Łojasiewicz exponents (3.7) and the Łojasiewicz property (Assumption 3.3)
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be a function and write $\nabla F$ for its gradient. The **critical set** of $F$ is
--
--   $$\mathcal S := \nabla F^{-1}(\{0\}) = \{x\in\mathbb R^d : \nabla F(x)=0\}.$$
--
--   A real number $\theta$ is a **Łojasiewicz exponent of $F$ at a point $x^*$** if there exist constants $c>0$ and $\sigma>0$ such that
--
--   $$\forall x\in\mathbb R^d \text{ with } \|x-x^*\|\le\sigma,\qquad \|\nabla F(x)\|\ \ge\ c\,|F(x)-F(x^*)|^{1-\theta}.$$
--
--   The function $F$ has the **Łojasiewicz property** (Assumption 3.3) if every critical point $x^*\in\mathcal S$ admits a Łojasiewicz exponent $\theta\in(0,\tfrac12]$.
--
--   The property holds for real-analytic and for semialgebraic functions. It is the hypothesis under which the continuous-time Adam trajectory converges to a single critical point, at a rate governed by the exponent.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $\nabla F$ is Mathlib's `gradient F`. The power $|F(x)-F(x^*)|^{1-\theta}$ is the real power of a nonnegative number. The definition of an exponent does not restrict $\theta$; the range $(0,\tfrac12]$ is part of Assumption 3.3 and of every statement that uses an exponent. The paper writes "exponent of $f$ at $x^*$", where $f$ is the stochastic integrand; inequality (3.7) concerns the objective $F$, which is what is defined here.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 3 (critical set 𝒮), p. 6, Assumption 3.3 and Eq. (3.7)

import Mathlib

namespace AdamDyn.Rates

/-- The critical set `𝒮 := ∇F⁻¹({0})` of a function `F : ℝ^d → ℝ` (Barakat–Bianchi, p. 3). -/
def critSet {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | gradient F x = 0}

/-- `θ` is a Łojasiewicz exponent of `F` at `xstar` (Barakat–Bianchi, p. 6, Eq. (3.7)): there exist
`c > 0` and `σ > 0` such that `‖∇F(x)‖ ≥ c |F(x) − F(xstar)|^{1−θ}` for every `x` with
`‖x − xstar‖ ≤ σ`. The power is `Real.rpow` of the nonnegative number `|F(x) − F(xstar)|`. -/
def IsLojExponent {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (xstar : EuclideanSpace ℝ (Fin d))
    (θ : ℝ) : Prop :=
  ∃ c > 0, ∃ σ > 0, ∀ x : EuclideanSpace ℝ (Fin d), ‖x - xstar‖ ≤ σ →
    c * |F x - F xstar| ^ (1 - θ) ≤ ‖gradient F x‖

/-- Assumption 3.3 (Łojasiewicz property, Barakat–Bianchi, p. 6): at every critical point
`xstar ∈ 𝒮` the function `F` has a Łojasiewicz exponent `θ ∈ (0, 1/2]`. -/
def LojasiewiczProperty {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ xstar ∈ critSet F, ∃ θ ∈ Set.Ioc (0 : ℝ) (1 / 2), IsLojExponent F xstar θ

end AdamDyn.Rates


