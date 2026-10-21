-- Prove2me | Definitions.Def_Tegmark_phys
-- name    : Tegmark_phys
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T04:10:20.470602+00:00
-- url     : https://prove2.me/theorems/07dae4f0-2335-4755-901e-f7635c12755b
-- title:
--   The physics layer: the Newtonian potential, the effective two-body potential, and the radial Laplacian
-- statement:
--   The physics layer of the letter. The Newtonian potential of a point mass with coupling k in a space of n dimensions at radius r is the Green's function of the Poisson equation, which scales as the (2 - n)-th power of the radius for n > 2 (page L70, after Ehrenfest 1917): the inverse-square law of electrostatics and gravity is the three-dimensional case, an inverse-cube law the four-dimensional one. The effective potential of the two-body problem is the centrifugal barrier plus the Newtonian potential; a circular orbit is a positive critical point of the effective potential, and a stable circular orbit is a circular orbit at which the effective potential has positive curvature, the linear stability of the orbit. A space of n dimensions admits stable circular Newtonian orbits when some positive coupling, angular momentum, and radius give a stable circular orbit. The radially reduced Laplace operator of a radial profile g is the second derivative of g plus the (n - 1)/r correction to its first derivative, and the radial Green profile is the (2 - n)-th power of the radius, the fundamental solution of the Laplace equation in n > 2 dimensions. Real powers, real division, and derivatives are noncomputable in the pinned Mathlib; the four definitions that use them are marked noncomputable accordingly.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, pp. L70-L71 (after Ehrenfest 1917; Courant and Hilbert 1962).

import Mathlib
import Definitions.Def_Tegmark_sig

namespace Tegmark

/-!
# On the dimensionality of spacetime: the physics layer

The physics layer of the letter: the Newtonian potential of a point
mass in "n" space dimensions, which is the Green's-function scaling
of the Poisson equation (Tegmark 1997, p. L70), the effective
potential of the two-body problem with its circular-orbit and
stability criteria (pp. L70-L71), and the radially reduced Laplace
equation with its Green profile.
-/

/-- The Newtonian potential of a point mass with coupling "k" in a
space of "n" dimensions at radius "r": the Green's function of the
Poisson equation scales as the (2 - n)-th power for "n > 2"
(Tegmark 1997, p. L70, after Ehrenfest 1917). -/
noncomputable def newton (k : ℝ) (n : ℕ) (r : ℝ) : ℝ := -k * r ^ (2 - (n : ℝ))

/-- The effective potential of the two-body problem in a space of "n"
dimensions with angular momentum per unit reduced mass "L" at radius
"r": the centrifugal barrier plus the Newtonian potential. -/
noncomputable def effPot (k L : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  L ^ 2 / (2 * r ^ 2) + newton k n r

/-- A circular orbit at radius "r": a positive critical point of the
effective potential. -/
def CircularOrbit (k L : ℝ) (n : ℕ) (r : ℝ) : Prop :=
  0 < r ∧ deriv (effPot k L n) r = 0

/-- A stable circular orbit: a circular orbit at which the effective
potential has positive curvature, the linear stability of the
orbit. -/
def StableOrbit (k L : ℝ) (n : ℕ) (r : ℝ) : Prop :=
  CircularOrbit k L n r ∧ 0 < deriv (fun x => deriv (effPot k L n) x) r

/-- A space of "n" dimensions admits stable circular Newtonian
orbits: some positive coupling, angular momentum, and radius give a
stable circular orbit (Tegmark 1997, pp. L70-L71). -/
def HasStableOrbit (n : ℕ) : Prop :=
  ∃ k L r : ℝ, 0 < k ∧ 0 < L ∧ StableOrbit k L n r

/-- The radially reduced Laplace operator of a radial profile "g" in
"n" dimensions: the second derivative of "g" plus the (n - 1) / r
correction to its first derivative (Courant and Hilbert 1962, as
cited by Tegmark 1997, p. L70). -/
noncomputable def radialLap (n : ℕ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (fun x => deriv g x) r + ((n : ℝ) - 1) / r * deriv g r

/-- The radial Green profile: the (2 - n)-th power of the radius, the
fundamental solution of the Laplace equation in "n > 2" dimensions
(Tegmark 1997, p. L70). -/
noncomputable def greenProfile (n : ℕ) (r : ℝ) : ℝ := r ^ (2 - (n : ℝ))

end Tegmark


