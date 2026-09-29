-- Prove2me | Definitions.Def_LangevinHarmonicTrap_IsLangevinPath
-- name    : LangevinHarmonicTrap_IsLangevinPath
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T19:09:12.682405+00:00
-- url     : https://prove2.me/theorems/29e618e0-8371-410b-b029-c9a022a239e0
-- title:
--   Newton's second law $m\ddot r = -\zeta\dot r - k r + f$ for one realization
-- statement:
--   The model predicate of the mission. For a particle of mass $m$ with hydrodynamic drag coefficient $\zeta$, held in a harmonic trap of spring constant $k$ and driven by the force $f$ of the surrounding medium, a **path** is a triple of component families $x$ (position), $v$ (velocity), $a$ (acceleration) such that $v$ is the time derivative of $x$, $a$ is the time derivative of $v$, and $$ m\,\ddot r(t) = -\zeta\, \dot r(t) - k\, r(t) + f(t) \qquad \text{for all } t, $$ componentwise. This is Eq. (1) of the source. Velocity and acceleration are carried as explicit data together with the statements that they *are* the derivatives, so that no smoothness is assumed implicitly and the later statements can quantify over the second derivative without using a junk-value convention.
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib

namespace LangevinHarmonicTrap

/-- Newton's second law for one realization of a particle of mass `m` with hydrodynamic
drag coefficient `zeta`, trapped in a harmonic potential with spring constant `k` and
driven by the force `f` of the surrounding medium, written in `d` Cartesian components:

  `m r̈(t) = -zeta ṙ(t) - k r(t) + f(t)`.

Here `x i t` is the `i`-th component of the position, `v i t` of the velocity and
`a i t` of the acceleration, and the structure records that `v` is the derivative of
`x`, that `a` is the derivative of `v`, and that Newton's law holds at every time. -/
structure IsLangevinPath (d : ℕ) (m zeta k : ℝ) (x v a f : Fin d → ℝ → ℝ) : Prop where
  /-- the velocity is the time derivative of the position -/
  hasDerivAt_pos : ∀ (i : Fin d) (t : ℝ), HasDerivAt (x i) (v i t) t
  /-- the acceleration is the time derivative of the velocity -/
  hasDerivAt_vel : ∀ (i : Fin d) (t : ℝ), HasDerivAt (v i) (a i t) t
  /-- Newton's second law with drag, harmonic trap and random force -/
  newton : ∀ (i : Fin d) (t : ℝ), m * a i t = -(zeta * v i t) - k * x i t + f i t

end LangevinHarmonicTrap


