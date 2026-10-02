-- Prove2me | Definitions.Def_HunterPDE_Shared_PartialDeriv
-- name    : HunterPDE_Shared_PartialDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:00:13.100719+00:00
-- url     : https://prove2.me/theorems/7f38589e-71f1-4ac6-9400-eb0bb26326b8
-- title:
--   Partial derivatives ∂ᵢu and multi-index derivatives ∂^α u (§1.8)
-- statement:
--   For $u : \mathbb{R}^n \to \mathbb{R}$ and a coordinate $i$, $\partial_i u(x)$ is the partial derivative of $u$ at $x$ in the direction of the standard basis vector $e_i$. For an $n$-dimensional multi-index $\alpha = (\alpha_1, \dots, \alpha_n) \in \mathbb{N}_0^n$ of order $|\alpha| = \alpha_1 + \cdots + \alpha_n$, the book defines
--   $$\partial^\alpha = \frac{\partial}{\partial x^{\alpha_1}} \frac{\partial}{\partial x^{\alpha_2}} \cdots \frac{\partial}{\partial x^{\alpha_n}},$$
--   that is, $\partial^\alpha u$ differentiates $u$ $\alpha_1$ times in $x_1$, $\alpha_2$ times in $x_2$, and so on; $\partial^0 u = u$.
--
--   This notation (Hunter, p. 10, §1.8) serves three missions of the series: the derivative estimates for harmonic functions (mission I, Theorems 2.7 and 2.9, p. 23), and the classical derivatives of test functions in the definition of weak derivatives (missions IV and VI, Definitions 3.1–3.2, pp. 47–48, used in §§3.9–3.11, pp. 71–75, and §4.8, pp. 124–125).
--
--   **Formalization Note.** Coordinates are 0-based: $i$ ranges over `Fin n`, so the book's $x_1, \dots, x_n$ are indices $0, \dots, n-1$. $\partial_i u(x)$ is `fderiv ℝ u x (EuclideanSpace.single i 1)` (Lean's `fderiv` is $0$ where $u$ is not differentiable; in every theorem that uses it, $u$ is smooth where it is evaluated). $\partial^\alpha u$ is built by applying $\partial_i$ repeatedly along the list consisting of $\alpha_0$ copies of $0$, then $\alpha_1$ copies of $1$, and so on; for smooth $u$ the order of differentiation does not matter.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 10, §1.8

import Mathlib

namespace HunterPDE.Shared

/-- The partial derivative `∂ᵢu(x)` of `u : ℝⁿ → ℝ` in the `i`-th coordinate direction, as the
Fréchet derivative applied to the standard basis vector `eᵢ = EuclideanSpace.single i 1`.
Coordinates are 0-based (`i : Fin n`), the book's `1 ≤ i ≤ n` shifted by one. Where `u` is not
differentiable at `x`, Lean's `fderiv` is `0`. -/
noncomputable def partialDeriv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

/-- Iterated partial derivative along a list of coordinate directions:
`iteratedPartial u [i₁, i₂, …, iₘ] = ∂_{i₁} ∂_{i₂} ⋯ ∂_{iₘ} u` (the last direction is applied
first). The empty list gives `u` itself. -/
noncomputable def iteratedPartial {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    List (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ
  | [] => u
  | i :: l => partialDeriv (iteratedPartial u l) i

/-- The list of directions of a multi-index `α = (α₀, …, α_{n-1}) ∈ ℕⁿ`: `α₀` copies of `0`,
then `α₁` copies of `1`, …; its length is the order `|α| = ∑ i, α i`. -/
def multiIndexList {n : ℕ} (α : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap (fun i => List.replicate (α i) i)

/-- The multi-index partial derivative `∂^α u = ∂₀^{α₀} ∂₁^{α₁} ⋯ ∂_{n-1}^{α_{n-1}} u` (Hunter,
*Notes on PDEs*, §1.8, with 0-based coordinates). For `α = 0` it is `u`. -/
noncomputable def multiDeriv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  iteratedPartial u (multiIndexList α)

end HunterPDE.Shared


