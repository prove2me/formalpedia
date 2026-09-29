-- Prove2me | Definitions.Def_SDYM_ChazyEquations
-- name    : SDYM_ChazyEquations
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T01:21:54.385599+00:00
-- url     : https://prove2.me/theorems/471663fb-4795-4cae-8574-81bb83bd806d
-- title:
--   The classical and generalized Chazy equations
-- statement:
--   Two predicates describing what it means for a complex-valued function of a complex variable to solve the Chazy equation on a prescribed set.
--
--   The **classical Chazy equation** (eq. (71) of the source) is the third-order equation
--
--   $$\frac{d^3y}{dt^3} = 2y\,\frac{d^2y}{dt^2} - 3\left(\frac{dy}{dt}\right)^2 .$$
--
--   Rather than iterating a derivative operator, the first two derivatives are carried as explicit companion functions: $y_1$ plays the role of $dy/dt$ and $y_2$ the role of $d^2y/dt^2$, and the predicate asserts that $y$ has derivative $y_1$, that $y_1$ has derivative $y_2$, and that $y_2$ has derivative $2yy_2 - 3y_1^2$, at every point of the set. This convention keeps every derivative that the statement mentions an actual derivative, and imposes no regularity off the set.
--
--   The **generalized Chazy equation** with parameter $n$ (eq. (81)) is
--
--   $$\frac{d^3y}{dt^3} - 2y\,\frac{d^2y}{dt^2} + 3\left(\frac{dy}{dt}\right)^2 = \frac{4}{36-n^2}\left(6\frac{dy}{dt} - y^2\right)^2 ,$$
--
--   of which the classical equation is the case $n = \infty$. The parameter $n$ ranges over the complex numbers; statements that use this predicate carry the hypothesis $n^2 \ne 36$.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V.A p. 3168 Eq. (71), and Sec. V.B p. 3170 Eq. (81)

import Mathlib

namespace SDYM

/-- The classical Chazy equation, Ablowitz–Chakravarty–Halburd eq. (71):
`y''' = 2 y y'' - 3 (y')^2`, on a set `s` of the complex `t`-plane.

The predicate carries the first two derivatives of `y` as explicit data: `y₁` is `dy/dt`,
`y₂` is `d²y/dt²`, and the third equation is the Chazy equation itself. -/
def IsChazySolution (s : Set ℂ) (y y₁ y₂ : ℂ → ℂ) : Prop :=
  (∀ t ∈ s, HasDerivAt y (y₁ t) t) ∧
  (∀ t ∈ s, HasDerivAt y₁ (y₂ t) t) ∧
  (∀ t ∈ s, HasDerivAt y₂ (2 * y t * y₂ t - 3 * y₁ t ^ 2) t)

/-- The generalized Chazy equation with parameter `n`,
Ablowitz–Chakravarty–Halburd eq. (81):
`y''' - 2 y y'' + 3 (y')^2 = 4 / (36 - n^2) * (6 y' - y^2)^2`.

As in `IsChazySolution`, `y₁` is `dy/dt` and `y₂` is `d²y/dt²`.  The classical Chazy
equation (71) is the limiting case `n = ∞`. -/
def IsGeneralizedChazySolution (n : ℂ) (s : Set ℂ) (y y₁ y₂ : ℂ → ℂ) : Prop :=
  (∀ t ∈ s, HasDerivAt y (y₁ t) t) ∧
  (∀ t ∈ s, HasDerivAt y₁ (y₂ t) t) ∧
  (∀ t ∈ s, HasDerivAt y₂
    (2 * y t * y₂ t - 3 * y₁ t ^ 2 + 4 / (36 - n ^ 2) * (6 * y₁ t - y t ^ 2) ^ 2) t)

end SDYM


