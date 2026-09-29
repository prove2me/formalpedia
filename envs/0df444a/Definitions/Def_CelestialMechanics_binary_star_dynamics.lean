-- Prove2me | Definitions.Def_CelestialMechanics_binary_star_dynamics
-- name    : CelestialMechanics_binary_star_dynamics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T17:41:26.772128+00:00
-- url     : https://prove2.me/theorems/c96f0885-22f2-4d20-8521-282f54e1f8ed
-- title:
--   Binary star dynamics: two-body system, center of mass, relative Kepler problem, conic orbit
-- statement:
--   This file fixes the kinematic and dynamical vocabulary used throughout the mission, following Section 4.16 of Fitzpatrick's *Celestial Mechanics*.
--
--   Motion takes place in $\mathbb{R}^3$ with the Euclidean norm. A pair of trajectories $\mathbf{r}_1,\mathbf{r}_2:\mathbb{R}\to\mathbb{R}^3$ is a **Newtonian gravitational two-body system** with constant $G$ and masses $m_1,m_2$ when both trajectories are twice continuously differentiable, the stars never coincide, and, writing $\mathbf{r}=\mathbf{r}_2-\mathbf{r}_1$ and $r=\lVert\mathbf{r}\rVert$, Newton's second law holds for each star under the gravitational force of Eq. (4.108),
--
--   $$ m_1\,\ddot{\mathbf{r}}_1 = \frac{G\,m_1 m_2}{r^{3}}\,\mathbf{r}, \qquad m_2\,\ddot{\mathbf{r}}_2 = -\frac{G\,m_1 m_2}{r^{3}}\,\mathbf{r}. $$
--
--   The **center of mass** is $(m_1\mathbf{r}_1+m_2\mathbf{r}_2)/(m_1+m_2)$.
--
--   A curve $\mathbf{r}$ solves the **relative (one-body) Kepler problem** with gravitational parameter $G M$ when it is twice continuously differentiable, never zero, and satisfies Eq. (4.110), $\ddot{\mathbf{r}} = -\,(G M/r^{3})\,\mathbf{r}$.
--
--   Finally, a curve is a **Keplerian conic orbit** with major radius $a$, eccentricity $e$ and angular momentum per unit reduced mass $h$, with polar description $(\rho(t),\theta(t))$, when $\theta$ is differentiable, the motion lies in the $x$-$y$ plane as in Eq. (4.112), $\mathbf{r}=(\rho\cos\theta,\ \rho\sin\theta,\ 0)$, and Eqs. (4.113)-(4.114) hold:
--
--   $$ \rho = \frac{a\,(1-e^{2})}{1+e\cos\theta}, \qquad \dot{\theta} = \frac{h}{\rho^{2}}. $$
-- source:
--   Richard Fitzpatrick, *Celestial Mechanics* (University of Texas at Austin, lecture notes), Chapter 4 "Keplerian orbits", Section 4.16 "Binary star systems", https://farside.ph.utexas.edu/teaching/celestial/Celestial/node38.html, Eqs. (4.108)-(4.119)

import Mathlib

noncomputable section

namespace CelestialMechanics

/-- Physical space: `ℝ³` with the Euclidean norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- `IsNewtonianTwoBody G m₁ m₂ r₁ r₂` says that the trajectories `r₁, r₂ : ℝ → ℝ³` form a
Newtonian gravitational two-body system with gravitational constant `G` and masses `m₁, m₂`:
both trajectories are twice continuously differentiable, the two bodies never occupy the same
point, and each obeys Newton's second law under the inverse-square attraction of the other,
the force on the second body being `-(G m₁ m₂ / ‖r‖³) r` with `r = r₂ - r₁`. -/
def IsNewtonianTwoBody (G m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space) : Prop :=
  ContDiff ℝ 2 r₁ ∧ ContDiff ℝ 2 r₂ ∧ (∀ t, r₁ t ≠ r₂ t) ∧
  (∀ t, m₁ • iteratedDeriv 2 r₁ t =
      (G * m₁ * m₂ / ‖r₂ t - r₁ t‖ ^ 3) • (r₂ t - r₁ t)) ∧
  (∀ t, m₂ • iteratedDeriv 2 r₂ t =
      (-(G * m₁ * m₂) / ‖r₂ t - r₁ t‖ ^ 3) • (r₂ t - r₁ t))

/-- The center of mass `(m₁ r₁ + m₂ r₂) / (m₁ + m₂)` of the two bodies. -/
def centerOfMass (m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space) : ℝ → Space :=
  fun t => (m₁ / (m₁ + m₂)) • r₁ t + (m₂ / (m₁ + m₂)) • r₂ t

/-- `IsKeplerRelative G M r` says that `r : ℝ → ℝ³` solves the equivalent one-body Kepler
problem with gravitational parameter `G M`: it is twice continuously differentiable, never
zero, and satisfies `r'' = -(G M / ‖r‖³) r`. -/
def IsKeplerRelative (G M : ℝ) (r : ℝ → Space) : Prop :=
  ContDiff ℝ 2 r ∧ (∀ t, r t ≠ 0) ∧
  ∀ t, iteratedDeriv 2 r t = (-(G * M) / ‖r t‖ ^ 3) • r t

/-- `IsConicOrbit a e h rad th r` says that the curve `r : ℝ → ℝ³` is the Keplerian conic with
major radius `a`, eccentricity `e` and angular momentum per unit reduced mass `h`, described
in polar coordinates `rad` (radius) and `th` (true anomaly): the motion takes place in the
`x`-`y` plane, `rad = a (1 - e²) / (1 + e cos th)`, and `th' = h / rad²`. -/
def IsConicOrbit (a e h : ℝ) (rad th : ℝ → ℝ) (r : ℝ → Space) : Prop :=
  Differentiable ℝ th ∧
  (∀ t, rad t = a * (1 - e ^ 2) / (1 + e * Real.cos (th t))) ∧
  (∀ t, deriv th t = h / rad t ^ 2) ∧
  (∀ t, r t 0 = rad t * Real.cos (th t)) ∧
  (∀ t, r t 1 = rad t * Real.sin (th t)) ∧
  (∀ t, r t 2 = 0)

end CelestialMechanics


