-- Prove2me | Definitions.Def_PetzFisher_partialDeriv
-- name    : PetzFisher_partialDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:02.062972+00:00
-- url     : https://prove2.me/theorems/ac90a42c-4d70-4463-bd0d-418eca5ad1eb
-- title:
--   Partial derivative $\partial_{\theta_i}\rho(\theta)$ of a matrix-valued family
-- statement:
--   Let $\theta\mapsto\rho(\theta)$ be a family of $n\times n$ complex matrices indexed by a parameter $\theta\in\mathbb R^k$. Its $i$-th partial derivative at $\theta$ is the matrix
--
--   $$
--   B_i(\theta)=\partial_{\theta_i}\rho(\theta),\qquad \big(B_i(\theta)\big)_{ab}=\frac{\partial}{\partial\theta_i}\rho(\theta)_{ab}.
--   $$
--
--   These are the tangent vectors of the statistical manifold $\{\rho(\theta)\}$ that enter the score operators (25) and the Fisher information matrix (26).
--
--   **Formalization Note** The derivative is taken entrywise: the $(a,b)$ entry is the Fréchet derivative of $\theta'\mapsto\rho(\theta')_{ab}$ at $\theta$ applied to the $i$-th standard basis vector. This avoids choosing a matrix norm; all norms give the same derivative. Where an entry is not differentiable, Mathlib's derivative is $0$, so every statement assumes entrywise differentiability on an open parameter set.
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, §2, eqs. (25)–(26), p.14, and proof of Theorem 2.3, p.15 ("We set Bi(θ) := ∂θiρ(θ)")

import Mathlib

namespace PetzFisher

/-- The partial derivative `∂_{θ_i} ρ(θ)` of a matrix-valued family `θ ↦ ρ(θ)`, `θ ∈ ℝᵏ`
(Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, §2, eq. (25)–(26),
p.14, and proof of Theorem 2.3, p.15: "We set `B_i(θ) := ∂_{θ_i} ρ(θ)`").

**Formalization Note.** The derivative is taken entrywise: the `(a, b)` entry is the Fréchet
derivative of the scalar function `θ' ↦ ρ(θ')_{ab}` at `θ`, applied to the `i`-th standard basis
vector `Pi.single i 1`. Entrywise differentiation avoids choosing a norm on `Matrix`; all norms on a
finite-dimensional space give the same derivative. Where the entry is not differentiable at `θ`,
Mathlib's `fderiv` is `0`; every statement using it assumes entrywise differentiability on an open
parameter set containing `θ`. -/
noncomputable def partialDeriv {I : Type} {k : ℕ} (ρ : (Fin k → ℝ) → Matrix I I ℂ)
    (θ : Fin k → ℝ) (i : Fin k) : Matrix I I ℂ :=
  fun a b => fderiv ℝ (fun θ' => ρ θ' a b) θ (Pi.single i 1)

end PetzFisher


