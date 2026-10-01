-- Prove2me | Definitions.Def_HilbertSixteenth_Dynamics
-- name    : HilbertSixteenth_Dynamics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T19:05:24.85298+00:00
-- url     : https://prove2.me/theorems/520cb26a-45a2-4800-814e-1959008385a5
-- title:
--   Planar vector fields: periodic orbits, limit cycles, hyperbolicity, inverse integrating factors
-- statement:
--   Let $F:\mathbb R^2\to\mathbb R^2$ be a planar vector field, defining the differential equation $\dot z = F(z)$.
--
--   1. A **solution** is a curve $\gamma:\mathbb R\to\mathbb R^2$, defined for all times, with $\gamma'(t) = F(\gamma(t))$ for every $t\in\mathbb R$.
--   2. A **periodic solution with period $T$** is a non-constant solution with $T>0$ and $\gamma(t+T)=\gamma(t)$ for all $t$.
--   3. A **periodic orbit** is the image $\gamma(\mathbb R)$ of a periodic solution.
--   4. A **limit cycle** is a periodic orbit $O$ isolated in the set of periodic orbits: there is an open set $U\supseteq O$ such that the only periodic orbit contained in $U$ is $O$ itself.
--   5. The **divergence** of $F=(P,Q)$ at $p$ is $\operatorname{div}F(p) = \partial P/\partial x(p) + \partial Q/\partial y(p)$.
--   6. A limit cycle $O$ is **hyperbolic** if for some $T$-periodic solution $\gamma$ with image $O$,
--   $$\int_0^T \operatorname{div}F(\gamma(t))\,dt \neq 0.$$
--   7. A function $V$ is an **inverse integrating factor** of $F=(P,Q)$ on $U\subseteq\mathbb R^2$ if $V$ is $C^1$ on $U$ and
--   $$P\,\frac{\partial V}{\partial x} + Q\,\frac{\partial V}{\partial y} = \Big(\frac{\partial P}{\partial x}+\frac{\partial Q}{\partial y}\Big)V \quad\text{on } U.$$
--
--   These notions are the dynamical vocabulary of the whole mission: every statement about limit cycles refers to them.
--
--   **Formalization Note** The vector field is an arbitrary function `ℝ × ℝ → ℝ × ℝ`; a field given only on an open set $U$ is represented by any extension. The divergence is computed with the Fréchet derivative, which Lean sets to $0$ at points where $F$ is not differentiable, so the divergence is only meaningful where $F$ is differentiable. The characteristic exponent does not depend on the chosen period or parametrisation, which is why an existential quantifier is used.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §1 (definition of limit cycle), §7 (inverse integrating factor, before Theorem 5), and Theorem 2 (hyperbolic limit cycles).

import Mathlib

/-!
# Planar vector fields: solutions, periodic orbits and limit cycles

Source: J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015),
no. 3, 543–554, §1 (definition of limit cycle) and §7 (inverse integrating factor).

A planar vector field is an arbitrary map `F : ℝ × ℝ → ℝ × ℝ`; the differential equation
is `ż = F z`.
-/

namespace HilbertSixteenth

/-- `γ` is a solution of `ż = F z` defined for all real times. -/
def IsSolution (F : ℝ × ℝ → ℝ × ℝ) (γ : ℝ → ℝ × ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt γ (F (γ t)) t

/-- `γ` is a non-constant solution of `ż = F z` which is periodic with period `T > 0`. -/
def IsPeriodicSolution (F : ℝ × ℝ → ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (T : ℝ) : Prop :=
  IsSolution F γ ∧ 0 < T ∧ (∀ t : ℝ, γ (t + T) = γ t) ∧ ∃ t : ℝ, γ t ≠ γ 0

/-- `O` is a periodic orbit of `ż = F z`: the trajectory of a non-constant periodic solution. -/
def IsPeriodicOrbit (F : ℝ × ℝ → ℝ × ℝ) (O : Set (ℝ × ℝ)) : Prop :=
  ∃ (γ : ℝ → ℝ × ℝ) (T : ℝ), IsPeriodicSolution F γ T ∧ Set.range γ = O

/-- A limit cycle is a periodic orbit which is isolated in the set of all periodic orbits:
some open neighbourhood of it contains no other periodic orbit. -/
def IsLimitCycle (F : ℝ × ℝ → ℝ × ℝ) (O : Set (ℝ × ℝ)) : Prop :=
  IsPeriodicOrbit F O ∧
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ O ⊆ U ∧
      ∀ O' : Set (ℝ × ℝ), IsPeriodicOrbit F O' → O' ⊆ U → O' = O

/-- The divergence `∂P/∂x + ∂Q/∂y` of the vector field `F = (P, Q)` at `p`. -/
noncomputable def divergence (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  (fderiv ℝ F p (1, 0)).1 + (fderiv ℝ F p (0, 1)).2

/-- A hyperbolic limit cycle: a limit cycle `O`, parametrised by a `T`-periodic solution `γ`,
whose characteristic exponent `∫₀ᵀ div F (γ t) dt` is non-zero. -/
def IsHyperbolicLimitCycle (F : ℝ × ℝ → ℝ × ℝ) (O : Set (ℝ × ℝ)) : Prop :=
  IsLimitCycle F O ∧
    ∃ (γ : ℝ → ℝ × ℝ) (T : ℝ), IsPeriodicSolution F γ T ∧ Set.range γ = O ∧
      (∫ t in (0 : ℝ)..T, divergence F (γ t)) ≠ 0

/-- `V` is an inverse integrating factor of `F = (P, Q)` on `U`: `V` is `C¹` on `U` and
`P ∂V/∂x + Q ∂V/∂y = (∂P/∂x + ∂Q/∂y) V` on `U`. -/
def IsInverseIntegratingFactor (F : ℝ × ℝ → ℝ × ℝ) (U : Set (ℝ × ℝ)) (V : ℝ × ℝ → ℝ) :
    Prop :=
  ContDiffOn ℝ 1 V U ∧ ∀ p ∈ U, fderiv ℝ V p (F p) = divergence F p * V p

end HilbertSixteenth


