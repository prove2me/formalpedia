-- Prove2me | Definitions.Def_LaplaceTide_core
-- name    : LaplaceTide_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T21:26:21.621765+00:00
-- url     : https://prove2.me/theorems/5cff0404-b1f2-4587-85e1-19c228095497
-- title:
--   Laplace's tidal equations: fields, the equations, and the energy quantities
-- statement:
--   This file fixes the model in which Laplace's tidal equations and their energetics are stated.
--
--   A **field** is a real-valued function of the two horizontal coordinates $x$, $y$ and of time
--   $t$. For such a field $F$ we write $\partial_x F$, $\partial_y F$, $\partial_t F$ for the
--   partial derivatives, each defined as an ordinary one-variable derivative of the corresponding
--   section of $F$. A field is *partially differentiable* when each of these three sections is
--   differentiable at every point; for a time-independent field such as the resting depth
--   $D(x,y)$ the corresponding two-variable notion is used.
--
--   **Laplace's tidal equations.** Given a Coriolis parameter $f$, gravity $g$, constant density
--   $\rho$, resting depth $D(x,y)$, tide generating potential $\Gamma$, dissipative force per unit
--   area $(F^x, F^y)$, horizontal velocity $(u,v)$, free-surface elevation $\zeta$ and solid Earth
--   tide $\delta$, the equations are
--
--   $$ u_t - f v = -g\left(\zeta - \tfrac{\Gamma}{g}\right)_x + \frac{F^x}{\rho D}, \qquad
--      v_t + f u = -g\left(\zeta - \tfrac{\Gamma}{g}\right)_y + \frac{F^y}{\rho D}, $$
--
--   $$ (\zeta - \delta)_t + (uD)_x + (vD)_y = 0 . $$
--
--   These are equations (22), (23) and (34) of the lecture notes; taking $\delta \equiv 0$ gives
--   the equations with the solid Earth tide ignored.
--
--   **Energetics.** The file also fixes the energy quantities of §6.1, written in terms of the
--   observed (geocentric) tide $\zeta_0 = \zeta - \delta$:
--
--   $$ \mathrm{KE} = \tfrac12 \rho D (u^2+v^2), \qquad
--      \mathrm{PE} = \tfrac12 \rho g (\zeta_0^2 + 2\zeta_0\delta + 2\delta D), $$
--
--   $$ \vec P = \rho g D \vec u\,(\zeta_0 + \delta), \qquad
--      W_t = \rho \zeta_{0t}\Gamma + \rho\,\nabla\cdot(\vec u D \Gamma) + \rho g (\zeta_0 + D)\delta_t, $$
--
--   which are equations (36), (37), (38) and (39), and the observed tide $\zeta_0 = \zeta-\delta$
--   of equation (21).
--
--   **Formalization Note** Partial derivatives are Lean's one-variable `deriv` applied to the
--   corresponding section, so they take the value $0$ wherever a section fails to be
--   differentiable; differentiability is therefore carried as an explicit hypothesis by every
--   theorem that uses a product rule. The two energy fluxes are given as separate scalar fields,
--   one per horizontal direction, and the potential energy is the one printed in the notes, which
--   differs from $\int_{-D+\delta}^{\zeta}\rho g z\,\mathrm{d}z$ by a time-independent constant.
-- source:
--   M. Hendershott, Lecture 3: Solutions to Laplace's Tidal Equations, Woods Hole Oceanographic Institution GFD Program lecture notes, notes by V. Birman and E. Williams Frajka, pp. 34-44, https://www.whoi.edu/cms/files/lecture03_21374.pdf, equations (21), (22), (23), (34), (36), (37), (38), (39)

import Mathlib

/-!
# Laplace's Tidal Equations — basic objects

Formalization of the objects appearing in M. Hendershott, *Lecture 3: Solutions to Laplace's
Tidal Equations* (WHOI GFD Program notes, pp. 34–44).

Everything is phrased for scalar fields `ℝ → ℝ → ℝ → ℝ` of the horizontal coordinates
`x`, `y` and of time `t`, with partial derivatives taken slot-wise.

This file contains only definitions; the theorems are stated separately.
-/

namespace LaplaceTide

/-- A scalar field of the horizontal coordinates `x`, `y` and of time `t`. -/
abbrev Field3 : Type := ℝ → ℝ → ℝ → ℝ

/-- Partial derivative `∂F/∂x`. -/
noncomputable def dx (F : Field3) (x y t : ℝ) : ℝ := deriv (fun s => F s y t) x

/-- Partial derivative `∂F/∂y`. -/
noncomputable def dy (F : Field3) (x y t : ℝ) : ℝ := deriv (fun s => F x s t) y

/-- Partial derivative `∂F/∂t`. -/
noncomputable def dt (F : Field3) (x y t : ℝ) : ℝ := deriv (fun s => F x y s) t

/-- A field is *partially differentiable* when it is differentiable in each of its three
variables separately, the other two being held fixed. -/
def PartialDiff (F : Field3) : Prop :=
  (∀ x y t, DifferentiableAt ℝ (fun s => F s y t) x) ∧
  (∀ x y t, DifferentiableAt ℝ (fun s => F x s t) y) ∧
  (∀ x y t, DifferentiableAt ℝ (fun s => F x y s) t)

/-- A time-independent field (such as the depth `D (x, y)`) is *partially differentiable* when
it is differentiable in each of its two variables separately. -/
def PartialDiff₂ (D : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, DifferentiableAt ℝ (fun s => D s y) x) ∧
  (∀ x y, DifferentiableAt ℝ (fun s => D x s) y)

/-- **Laplace's tidal equations** in the form (22), (23), (34) of the lecture notes, on a
plane with constant Coriolis parameter `f`, gravity `g`, constant density `rho`, resting
depth `D (x, y)`, tide generating potential `Gamma`, dissipative force per unit area
`(Fx, Fy)`, horizontal velocity `(u, v)`, free-surface elevation `zeta` and solid-Earth tide
`delta`:

* `u_t - f v = -g (zeta - Gamma / g)_x + F^x / (rho D)`,
* `v_t + f u = -g (zeta - Gamma / g)_y + F^y / (rho D)`,
* `(zeta - delta)_t + (u D)_x + (v D)_y = 0`.

Taking `delta = 0` gives the equations with the solid-Earth tide ignored. -/
structure IsLTE (f g rho : ℝ) (D : ℝ → ℝ → ℝ)
    (Gamma Fx Fy u v zeta delta : Field3) : Prop where
  momentum_x : ∀ x y t, dt u x y t - f * v x y t
    = -g * dx zeta x y t + dx Gamma x y t + Fx x y t / (rho * D x y)
  momentum_y : ∀ x y t, dt v x y t + f * u x y t
    = -g * dy zeta x y t + dy Gamma x y t + Fy x y t / (rho * D x y)
  continuity : ∀ x y t, dt zeta x y t - dt delta x y t
    + dx (fun x y t => u x y t * D x y) x y t
    + dy (fun x y t => v x y t * D x y) x y t = 0

/-- Kinetic energy per unit area, `KE = ρ D (u² + v²) / 2`, equation (36). -/
noncomputable def kineticEnergy (rho : ℝ) (D : ℝ → ℝ → ℝ) (u v : Field3) : Field3 :=
  fun x y t => (1 / 2) * rho * D x y * ((u x y t) ^ 2 + (v x y t) ^ 2)

/-- Potential energy per unit area, `PE = ρ g (ζ₀² + 2 ζ₀ δ + 2 δ D) / 2`, equation (37),
where `ζ₀ = ζ - δ` is the observed (geocentric) tide and `δ` the solid-Earth tide. -/
noncomputable def potentialEnergy (rho g : ℝ) (D : ℝ → ℝ → ℝ) (zeta0 delta : Field3) : Field3 :=
  fun x y t => (1 / 2) * rho * g *
    ((zeta0 x y t) ^ 2 + 2 * zeta0 x y t * delta x y t + 2 * delta x y t * D x y)

/-- First component of the energy flux `P = ρ g D u (ζ₀ + δ)`, equation (38). -/
noncomputable def energyFluxX (rho g : ℝ) (D : ℝ → ℝ → ℝ) (u zeta0 delta : Field3) : Field3 :=
  fun x y t => rho * g * D x y * u x y t * (zeta0 x y t + delta x y t)

/-- Second component of the energy flux `P = ρ g D u (ζ₀ + δ)`, equation (38). -/
noncomputable def energyFluxY (rho g : ℝ) (D : ℝ → ℝ → ℝ) (v zeta0 delta : Field3) : Field3 :=
  fun x y t => rho * g * D x y * v x y t * (zeta0 x y t + delta x y t)

/-- Rate of working by the tide generating potential and by the solid-Earth tide,
`W_t = ρ ζ₀ₜ Γ + ρ ∇ · (u D Γ) + ρ g (ζ₀ + D) δₜ`, equation (39). -/
noncomputable def workRate (rho g : ℝ) (D : ℝ → ℝ → ℝ)
    (u v Gamma zeta0 delta : Field3) : Field3 :=
  fun x y t =>
    rho * dt zeta0 x y t * Gamma x y t
      + rho * (dx (fun x y t => u x y t * D x y * Gamma x y t) x y t
        + dy (fun x y t => v x y t * D x y * Gamma x y t) x y t)
      + rho * g * (zeta0 x y t + D x y) * dt delta x y t

/-- The observed (geocentric) tide `ζ₀ = ζ - δ`, equation (21). -/
def observedTide (zeta delta : Field3) : Field3 := fun x y t => zeta x y t - delta x y t

end LaplaceTide


