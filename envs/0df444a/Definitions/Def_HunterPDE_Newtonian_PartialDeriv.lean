-- Prove2me | Definitions.Def_HunterPDE_Newtonian_PartialDeriv
-- name    : HunterPDE_Newtonian_PartialDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:10:49.662833+00:00
-- url     : https://prove2.me/theorems/0fcc091c-314f-4051-b132-3cdeffe5f5c9
-- title:
--   First and second partial derivatives ∂ᵢu and ∂ᵢⱼu = ∂ᵢ∂ⱼu on ℝⁿ
-- statement:
--   For $u : \mathbb{R}^n \to \mathbb{R}$ and a coordinate index $i$, the **partial derivative** $\partial_i u(x)$ is the derivative of $u$ at $x$ in the direction of the $i$-th standard basis vector $e_i$, and the **second partial derivative** is
--   $$\partial_{ij} u = \partial_i \partial_j u,$$
--   first differentiating in the $j$-th direction and then in the $i$-th, as in the book's convention $\partial_i\partial_j = \partial_{ij}$.
--
--   **Formalization Note.** $\partial_i u(x)$ is `fderiv ℝ u x (EuclideanSpace.single i 1)`. Coordinates are 0-based (`i : Fin n`), the book's $1 \le i \le n$ shifted by one. Where $u$ is not differentiable, Lean's `fderiv` is $0$; every theorem using these operators applies them to functions that the theorem itself asserts (or the book proves) to be smooth, or at points away from the singularity.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 37, §2.7.1 (notation ∂ᵢ∂ⱼ = ∂ᵢⱼ)

import Mathlib

namespace HunterPDE.Newtonian

/-- The partial derivative `∂ᵢu(x)` of `u : ℝⁿ → ℝ` in the `i`-th coordinate direction, as the
Fréchet derivative applied to the standard basis vector `eᵢ = EuclideanSpace.single i 1`.
Coordinates are 0-based (`i : Fin n`), the book's `1 ≤ i ≤ n` shifted by one. Where `u` is not
differentiable at `x`, Lean's `fderiv` is `0`. -/
noncomputable def partialDeriv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

/-- The second partial derivative `∂ᵢⱼu = ∂ᵢ∂ⱼu` (Hunter, *Notes on PDEs*, §2.7.1, p. 37:
"We write `∂ᵢ∂ⱼ = ∂ᵢⱼ`"): first `∂ⱼ`, then `∂ᵢ`. 0-based indices. -/
noncomputable def secondPartial {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  partialDeriv (partialDeriv u j) i x

end HunterPDE.Newtonian


