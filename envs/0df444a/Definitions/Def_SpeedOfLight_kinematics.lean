-- Prove2me | Definitions.Def_SpeedOfLight_kinematics
-- name    : SpeedOfLight_kinematics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T12:24:44.805569+00:00
-- url     : https://prove2.me/theorems/62008609-d425-4211-81bf-8baa88644b7a
-- title:
--   One-dimensional relativistic kinematics: $u \oplus_c v$, $\gamma_c$, $c^2t^2-x^2$, boosts, $(\gamma-1)mc^2$
-- statement:
--   The definition layer for the mission, in one spatial dimension and for an arbitrary invariant speed $c$. It introduces relativistic velocity addition $u \oplus_c v = (u+v)/(1 + uv/c^2)$; the Lorentz factor $\gamma_c(v) = 1/\sqrt{1 - v^2/c^2}$; the Lorentz interval $I_c(x,t) = c^2 t^2 - x^2$ of an event with spatial coordinate $x$ and time coordinate $t$; the Lorentz boost of velocity $v$, which sends $(x,t)$ to $(\gamma_c(v)(x - vt),\ \gamma_c(v)(t - vx/c^2))$; and the relativistic kinetic energy $K_c(m,v) = (\gamma_c(v) - 1)mc^2$ of a body of rest mass $m$ at speed $v$. All five are total real functions: outside the subluminal range $|v| < c$ the Lorentz factor takes the junk value $0$, because the real square root of a negative number is $0$, and velocity addition takes the junk value $0$ where its denominator vanishes. The theorems of the mission therefore carry explicit hypotheses $c > 0$ and $|v| < c$.
-- source:
--   Speed of light, Wikipedia (PDF supplied by the proposal owner), sections 'Invariance of c and the Lorentz factor' (Lorentz factor gamma = 1/sqrt(1 - v^2/c^2), diverging as v -> c), 'Synthesis of space and time' (Lorentz interval), and 'Mass and massless particles' (kinetic energy (gamma - 1) m c^2; c unattainable for positive rest mass). https://en.wikipedia.org/wiki/Speed_of_light

import Mathlib

namespace SpeedOfLight

/-- Relativistic (Einstein) velocity addition of the speeds `u` and `v` at
invariant speed `c`, in one spatial dimension. -/
noncomputable def velAdd (c u v : ℝ) : ℝ := (u + v) / (1 + u * v / c ^ 2)

/-- The Lorentz factor `γ = 1 / √(1 - v ^ 2 / c ^ 2)`. -/
noncomputable def lorentzFactor (c v : ℝ) : ℝ := 1 / Real.sqrt (1 - v ^ 2 / c ^ 2)

/-- The Lorentz (spacetime) interval `c ^ 2 * t ^ 2 - x ^ 2` of an event with
spatial coordinate `x` and time coordinate `t`. -/
noncomputable def lorentzInterval (c x t : ℝ) : ℝ := c ^ 2 * t ^ 2 - x ^ 2

/-- The Lorentz boost of velocity `v`, sending an event `(x, t)` to its
coordinates `(γ * (x - v * t), γ * (t - v * x / c ^ 2))` in the moving frame. -/
noncomputable def boost (c v x t : ℝ) : ℝ × ℝ :=
  (lorentzFactor c v * (x - v * t), lorentzFactor c v * (t - v * x / c ^ 2))

/-- The relativistic kinetic energy `(γ - 1) * m * c ^ 2` of a body of rest
mass `m` moving with speed `v`. -/
noncomputable def kineticEnergy (c m v : ℝ) : ℝ := (lorentzFactor c v - 1) * m * c ^ 2

end SpeedOfLight


