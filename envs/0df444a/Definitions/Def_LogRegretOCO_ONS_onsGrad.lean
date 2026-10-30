-- Prove2me | Definitions.Def_LogRegretOCO_ONS_onsGrad
-- name    : LogRegretOCO_ONS_onsGrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:56.73515+00:00
-- url     : https://prove2.me/theorems/d249e289-2747-4cee-9593-bb2c322b6a38
-- title:
--   Observed gradient $\nabla_\tau = \nabla f_\tau(x_\tau)$
-- statement:
--   Given a sequence of loss functions $f_1, f_2, \dots : \mathbb R^n \to \mathbb R$ and a sequence of points $x_1, x_2, \dots \in \mathbb R^n$, the **gradient observed in round $\tau$** is
--   $$
--   \nabla_\tau = \nabla f_\tau(x_\tau),
--   $$
--   the gradient of the loss of round $\tau$ at the point played in that round. Online Newton Step uses only these gradients.
--
--   **Formalization Note** $\nabla$ is Mathlib's `gradient` on `EuclideanSpace ℝ (Fin n)`, which returns $0$ where the function is not differentiable; the theorems assume each $f_t$ is differentiable at the points of $\mathcal P$. Rounds are indexed from $1$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Fig. 2, p. 176 (PDF p. 8)

import Mathlib

namespace LogRegretOCO.ONS

/-- **The observed gradient `∇_τ = ∇f_τ(x_τ)`.**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Fig. 2, p. 176: "where ∇_τ = ∇f_τ(x_τ)".

`onsGrad f x τ` is the gradient of the loss `f τ` at the point `x τ` played in round `τ`.

**Formalization Note.** `gradient` is Mathlib's gradient on `EuclideanSpace ℝ (Fin n)`; it
equals `0` where `f τ` is not differentiable, so every theorem using it assumes that each
loss is differentiable at the points of `P`. Rounds are indexed from `1`; index `0` is
unused. -/
noncomputable def onsGrad {n : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (τ : ℕ) : EuclideanSpace ℝ (Fin n) :=
  gradient (f τ) (x τ)

end LogRegretOCO.ONS


