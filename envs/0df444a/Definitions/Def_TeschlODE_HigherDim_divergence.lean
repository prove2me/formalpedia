-- Prove2me | Definitions.Def_TeschlODE_HigherDim_divergence
-- name    : TeschlODE_HigherDim_divergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:04:15.997133+00:00
-- url     : https://prove2.me/theorems/6a8eb200-b385-4c7f-8d0d-ad2d33006e23
-- title:
--   Divergence $\operatorname{div} f = \operatorname{tr}(df)$ of a vector field on $\mathbb{R}^n$
-- statement:
--   For a vector field $f : \mathbb{R}^n \to \mathbb{R}^n$ and $x \in \mathbb{R}^n$, the **divergence** of $f$ at $x$ is
--   $$\operatorname{div}(f(x)) = \sum_{i=1}^{n} \frac{\partial f_i}{\partial x_i}(x) = \operatorname{tr}\big(df(x)\big),$$
--   where $\partial f_i / \partial x_i (x)$ is the $i$-th component of the derivative $df(x)$ applied to the $i$-th standard basis vector $\delta_i$.
--
--   It appears in Liouville's formula for volumes (8.28): the rate of change of the volume transported by a flow is the integral of the divergence.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`; the derivative is Mathlib's `fderiv`, which is $0$ where $f$ is not differentiable. Every theorem using the divergence assumes $f \in C^1$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 237, proof of Lemma 8.8 ("recall tr(df(x)) = div(f(x))")

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.2, p. 237 (proof of Lemma 8.8): the divergence
`div f(x) = ∑ᵢ ∂fᵢ/∂xᵢ(x) = tr(df(x))` of a vector field `f : ℝⁿ → ℝⁿ`. -/
noncomputable def divergence {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, fderiv ℝ f x (EuclideanSpace.single i 1) i

end TeschlODE.HigherDim


