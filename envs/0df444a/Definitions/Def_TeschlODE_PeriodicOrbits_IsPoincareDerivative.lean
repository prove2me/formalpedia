-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_IsPoincareDerivative
-- name    : TeschlODE_PeriodicOrbits_IsPoincareDerivative
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T04:03:17.426434+00:00
-- url     : https://prove2.me/theorems/3a9c7392-984a-4237-8bdb-f349fbb87b44
-- title:
--   The derivative $dP_\Sigma(x_0)$ of the Poincaré map as an endomorphism of $T_{x_0}\Sigma$
-- statement:
--   Let $P_\Sigma(y) = \Phi(\tau(y), y)$ be the Poincaré map of the section $\Sigma = \{S = 0\}$, with $x_0 \in \Sigma$. Its **derivative at $x_0$** is a linear map of the tangent space
--   $$T_{x_0}\Sigma = \ker \tfrac{\partial S}{\partial x}(x_0) \qquad (\text{dimension } n-1)$$
--   into itself. Since the formula $\Phi(\tau(y), y)$ defines $P_\Sigma$ on a full neighborhood of $x_0$ in $\mathbb{R}^n$, $dP_\Sigma(x_0)$ is the restriction to $T_{x_0}\Sigma$ of the derivative of $y \mapsto \Phi(\tau(y), y)$ at $x_0$. An endomorphism $L$ of $T_{x_0}\Sigma$ **is** $dP_\Sigma(x_0)$ when
--   $$L v = \frac{\partial}{\partial y}\Phi(\tau(y), y)\Big|_{y = x_0} v \qquad \text{for all } v \in T_{x_0}\Sigma .$$
--
--   This is the operator whose eigenvalues Theorem 12.4 compares with the monodromy matrix.
--
--   **Formalization Note.** The condition determines $L$ uniquely (vectors of the subspace are determined by their values in $\mathbb{R}^n$); whether such an $L$ exists (i.e. the derivative maps $T_{x_0}\Sigma$ into itself) is part of what the theorems assert.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), pp. 317–318, §12.2, Theorem 12.4 and its proof

import Mathlib

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §12.2, pp. 317–318: `L` is the derivative `dP_Σ(x₀)` of the Poincaré map
`P_Σ(y) = Φ(τ(y), y)` (6.25), (12.9) at `x₀ ∈ Σ = {S = 0}`, regarded as an endomorphism of the
tangent space `T_{x₀}Σ = ker (∂S/∂x)(x₀)` (dimension `n − 1`). Since `P_Σ` is defined by the same
formula on a full neighborhood of `x₀`, `dP_Σ(x₀)` is the restriction to `T_{x₀}Σ` of the
derivative at `x₀` of `y ↦ Φ(τ(y), y)`; the condition says exactly that `L` is this restriction
(it determines `L` uniquely). -/
def IsPoincareDerivative {n : ℕ} (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (τ : (Fin n → ℝ) → ℝ)
    (S : (Fin n → ℝ) → ℝ) (x₀ : Fin n → ℝ)
    (L : Module.End ℝ (LinearMap.ker (fderiv ℝ S x₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ))) : Prop :=
  ∀ v : LinearMap.ker (fderiv ℝ S x₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ),
    (L v : Fin n → ℝ) = fderiv ℝ (fun y => Φ (τ y) y) x₀ (v : Fin n → ℝ)

end TeschlODE.PeriodicOrbits


