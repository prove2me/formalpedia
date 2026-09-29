-- Prove2me | Definitions.Def_StationaryActionCore
-- name    : StationaryActionCore
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T17:49:00.209914+00:00
-- url     : https://prove2.me/theorems/2c903024-08b1-473c-ad72-b2c04d034052
-- title:
--   Action, admissible variations, stationary paths, Euler–Lagrange expression
-- statement:
--   This file fixes the variational vocabulary used by the whole mission, in the one-dimensional setting of Chapter 3 of the source monograph.
--
--   An **integrand** is a function $f(y, y', x)$ of three real arguments. For a path $y : \mathbb{R} \to \mathbb{R}$ and endpoints $x_1, x_2$, the **action** is
--
--   $$S[y] = \int_{x_1}^{x_2} f\bigl(y(x), y'(x), x\bigr)\, dx,$$
--
--   where $y'$ is the derivative of $y$. The two **partial derivatives** of the integrand, $\partial f/\partial y$ and $\partial f/\partial y'$, are the derivatives of $f$ in its first and second slot with the other two arguments held fixed.
--
--   Neighbouring paths are $y(x,\alpha) = y(x) + \alpha\,\eta(x)$. A variation $\eta$ is **admissible** on $[x_1,x_2]$ when it is twice continuously differentiable and $\eta(x_1) = \eta(x_2) = 0$, which is the class of comparison paths used in the source. A path is a **stationary path** when, for every admissible $\eta$, the function $\alpha \mapsto S[y + \alpha\eta]$ has derivative $0$ at $\alpha = 0$.
--
--   Finally the **Euler–Lagrange expression** along $y$ is
--
--   $$E_f[y](x) = \frac{\partial f}{\partial y}\bigl(y(x), y'(x), x\bigr) - \frac{d}{dx}\left[\frac{\partial f}{\partial y'}\bigl(y(x), y'(x), x\bigr)\right],$$
--
--   so that the Euler–Lagrange equation of the source is the assertion $E_f[y] = 0$. Taking $x = t$, $y = q$ and $f = L = T - U$ turns these definitions into Hamilton's principle and the Lagrange equations of motion.
--
--   **Formalization Note** Derivatives are Lean's `deriv`, which returns $0$ at points of non-differentiability; the theorems of this mission therefore carry explicit $C^2$ hypotheses wherever a derivative is asserted to be a genuine derivative. Paths, variations and integrands are defined on all of $\mathbb{R}$, and only their behaviour on $[x_1, x_2]$ is constrained.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. Chapter 3, pp. 38–40, Eqs. (3.1)–(3.4) and (3.9); §3.1, pp. 43–44, Eqs. (3.14)–(3.17).

import Mathlib

namespace StationaryAction

/-- `partialY f y v x` is the partial derivative `∂f/∂y` of the integrand
`f = f (y, y', x)` with respect to its first slot, evaluated at `(y, v, x)`. -/
noncomputable def partialY (f : ℝ → ℝ → ℝ → ℝ) (y v x : ℝ) : ℝ :=
  deriv (fun u => f u v x) y

/-- `partialV f y v x` is the partial derivative `∂f/∂y'` of the integrand
`f = f (y, y', x)` with respect to its second slot, evaluated at `(y, v, x)`. -/
noncomputable def partialV (f : ℝ → ℝ → ℝ → ℝ) (y v x : ℝ) : ℝ :=
  deriv (fun w => f y w x) v

/-- The action (variational) integral `S = ∫_{x₁}^{x₂} f (y x, y' x, x) dx`. -/
noncomputable def action (f : ℝ → ℝ → ℝ → ℝ) (y : ℝ → ℝ) (x₁ x₂ : ℝ) : ℝ :=
  ∫ x in x₁..x₂, f (y x) (deriv y x) x

/-- The one-parameter family of neighbouring paths `y (x, a) = y x + a * η x`. -/
noncomputable def vary (y η : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := fun x => y x + a * η x

/-- An admissible variation on `[x₁, x₂]`: twice continuously differentiable and
vanishing at both endpoints. -/
def IsAdmissibleVariation (η : ℝ → ℝ) (x₁ x₂ : ℝ) : Prop :=
  ContDiff ℝ 2 η ∧ η x₁ = 0 ∧ η x₂ = 0

/-- `y` makes the action stationary on `[x₁, x₂]`: for every admissible variation `η`,
the derivative at `a = 0` of `a ↦ S (y + a η)` vanishes. -/
def IsStationaryPath (f : ℝ → ℝ → ℝ → ℝ) (y : ℝ → ℝ) (x₁ x₂ : ℝ) : Prop :=
  ∀ η : ℝ → ℝ, IsAdmissibleVariation η x₁ x₂ →
    deriv (fun a : ℝ => action f (vary y η a) x₁ x₂) 0 = 0

/-- The Euler–Lagrange expression `∂f/∂y - d/dx (∂f/∂y')` evaluated along the path `y`. -/
noncomputable def eulerLagrangeExpr (f : ℝ → ℝ → ℝ → ℝ) (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  partialY f (y x) (deriv y x) x - deriv (fun t => partialV f (y t) (deriv y t) t) x

end StationaryAction


