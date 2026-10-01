-- Prove2me | Definitions.Def_LindgrenPriceDynamics
-- name    : LindgrenPriceDynamics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T17:42:57.634958+00:00
-- url     : https://prove2.me/theorems/d5913507-8518-4d6e-9213-728e1c5d98a1
-- title:
--   Lindgren price dynamics: dot product, partial derivatives, Hamiltonian, optimal velocity
-- statement:
--   Shared definitions for the price-adjustment model of Lindgren (2022). There are $l$ commodities; price vectors are $p\in\mathbb R^l$.
--
--   1. **Contraction** (eq. (1)): $\langle x,y\rangle=\sum_{i=1}^l x_iy_i$.
--   2. **Price partial derivative and gradient**: $\partial f/\partial p_i$ at $p$, and $\nabla f(p)=(\partial f/\partial p_1,\dots,\partial f/\partial p_l)$.
--   3. **Time partial derivative** of a function $F(t,p)$: $\partial F/\partial t$, the derivative of $\tau\mapsto F(\tau,p)$.
--   4. **Aggregate expenditure**: $E(p)=\sum_{j=1}^n\lambda_je_j(p)$.
--   5. **Hamiltonian** (eq. (8)), as a function of the control $v$, with $g$ standing for $\nabla J$:
--   $$H_{m,E,g}(v)=\tfrac12 m\langle v,v\rangle+E+\langle g,v\rangle .$$
--   6. **Optimal price velocity** (eq. (9)): $v(t,p)=-\tfrac1m\nabla_pJ(t,p)$.
--
--   These are the objects in which the HJB equation, the price-velocity evolution equation and the Lyapunov condition of the paper are stated.
--
--   **Formalization Note** Partial derivatives are Fréchet derivatives applied to standard basis vectors; as usual in Mathlib, they return $0$ where the function is not differentiable, and $1/m$ is $0$ when $m=0$.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, Section 2 (eqs. (1), (7), (8), (9))

import Mathlib

/-!
# Lindgren (2022): price-adjustment dynamics — shared definitions

Source: J. Lindgren, *General Equilibrium with Price Adjustments — A Dynamic Programming
Approach*, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003.

There are `l` commodities (prices `p : Fin l → ℝ`) and `n` agents.
-/

namespace LindgrenPriceDynamics

/-- The implicit-summation contraction `x^i y_i = ∑_{i=1}^l x_i y_i` of eq. (1). -/
noncomputable def dot {l : ℕ} (x y : Fin l → ℝ) : ℝ := ∑ i, x i * y i

/-- Partial derivative `∂f/∂p_i` of a function of the price vector, i.e. the Fréchet
derivative of `f` at `p` applied to the `i`-th standard basis vector. -/
noncomputable def pricePartial {l : ℕ} (f : (Fin l → ℝ) → ℝ) (p : Fin l → ℝ) (i : Fin l) : ℝ :=
  fderiv ℝ f p (Pi.single i 1)

/-- Price gradient `∇f(p) = (∂f/∂p_1, …, ∂f/∂p_l)`. -/
noncomputable def priceGrad {l : ℕ} (f : (Fin l → ℝ) → ℝ) (p : Fin l → ℝ) : Fin l → ℝ :=
  fun i => pricePartial f p i

/-- Partial time derivative `∂F/∂t (t, p)` of a function of time and prices. -/
noncomputable def timePartial {l : ℕ} (F : ℝ → (Fin l → ℝ) → ℝ) (t : ℝ) (p : Fin l → ℝ) : ℝ :=
  deriv (fun τ => F τ p) t

/-- Aggregate expenditure `λ^j e_j(p) = ∑_{j=1}^n λ_j e_j(p)` (the running cost in eq. (7)). -/
noncomputable def aggregateExpenditure {n l : ℕ} (lam : Fin n → ℝ) (e : Fin n → (Fin l → ℝ) → ℝ)
    (p : Fin l → ℝ) : ℝ :=
  ∑ j, lam j * e j p

/-- The Hamiltonian of eq. (8), `H = ½ m v^i v_i + λ^j e_j + (∂J/∂p_i) v^i`,
written as a function of the control `v`, with `E = λ^j e_j` and `g = ∇J`. -/
noncomputable def hamiltonian {l : ℕ} (m E : ℝ) (g v : Fin l → ℝ) : ℝ :=
  (1 / 2) * m * dot v v + E + dot g v

/-- The optimal price velocity (feedback policy) of eq. (9): `v_i = -(1/m) ∂J/∂p_i`. -/
noncomputable def optimalVelocity {l : ℕ} (m : ℝ) (J : ℝ → (Fin l → ℝ) → ℝ) (t : ℝ)
    (p : Fin l → ℝ) : Fin l → ℝ :=
  fun i => -(1 / m) * pricePartial (J t) p i

end LindgrenPriceDynamics


