-- Prove2me | Definitions.Def_TeschlODE_HigherDim_hamiltonianVectorField
-- name    : TeschlODE_HigherDim_hamiltonianVectorField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:06:45.001008+00:00
-- url     : https://prove2.me/theorems/b379645c-69dd-438b-8dd8-89e3329d0e3e
-- title:
--   The Hamiltonian vector field of $H(p, q)$, right-hand side of Hamilton's equations (8.43)
-- statement:
--   Let $H : \mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R}$ be a Hamilton function of the momenta $p$ and positions $q$. **Hamilton's equations** are
--   $$\dot q = \frac{\partial H(p, q)}{\partial p}, \qquad \dot p = -\frac{\partial H(p, q)}{\partial q}. \qquad (8.43)$$
--   The **Hamiltonian vector field** of $H$ is their right-hand side on the phase space $\mathbb{R}^n \times \mathbb{R}^n \ni (p, q)$:
--   $$X_H(p, q) = \Big(-\frac{\partial H}{\partial q}(p, q),\ \frac{\partial H}{\partial p}(p, q)\Big),$$
--   where $\partial H / \partial q$ is the gradient of $q \mapsto H(p, q)$ and $\partial H / \partial p$ the gradient of $p \mapsto H(p, q)$. A Hamiltonian flow is the flow of $\dot x = X_H(x)$.
--
--   **Formalization Note.** A phase point is the pair `(p, q)`, momenta first, as in the book's $H(p, q)$. The partial gradients are Mathlib's `gradient` in `EuclideanSpace ℝ (Fin n)`; they are $0$ where $H$ is not differentiable, and every theorem using $X_H$ assumes $H \in C^2$ on its domain.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 239, §8.3, Eq. (8.43)

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.3, p. 239, (8.43): the Hamiltonian vector field of `H(p, q)` on the phase space
`ℝⁿ × ℝⁿ ∋ (p, q)`, i.e. the right-hand side of Hamilton's equations
`ṗ = -∂H/∂q (p, q)`, `q̇ = ∂H/∂p (p, q)`. The partial gradients are the gradients of
`q ↦ H(p, q)` and `p ↦ H(p, q)`. -/
noncomputable def hamiltonianVectorField {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  (-(gradient (fun q => H (x.1, q)) x.2), gradient (fun p => H (p, x.2)) x.1)

end TeschlODE.HigherDim


