-- Prove2me | Definitions.Def_GravitationalConstantBasic
-- name    : GravitationalConstantBasic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T13:11:02.361467+00:00
-- url     : https://prove2.me/theorems/344ea455-7d01-417f-93f1-01c7794c4639
-- title:
--   Newtonian gravitation: force, surface gravity, mean density, circular orbits, $\kappa$
-- statement:
--   The vocabulary of elementary Newtonian gravitation used throughout the mission, all over the real numbers.
--
--   - $F(G,m_1,m_2,r) = G m_1 m_2 / r^2$ is the magnitude of the gravitational attraction between two point masses at centre-to-centre distance $r$.
--   - $g(G,M,R) = G M / R^2$ is the surface gravity of a spherically symmetric body of mass $M$ and radius $R$ - "small $g$", as opposed to "big $G$".
--   - $V(r) = \tfrac{4}{3}\pi r^3$ is the volume of a ball of radius $r$, and $\rho(M,R) = M/V(R)$ is the mean density of a body of mass $M$ filling such a ball.
--   - $\kappa(G,c) = 8\pi G/c^4$ is the Einstein gravitational constant.
--   - A circular orbit of radius $r$ and period $P$ about a mass $M$ is the condition $r>0$, $P>0$ and $(2\pi/P)^2 r = GM/r^2$, i.e. centripetal acceleration equals gravitational acceleration.
--   - $G_{\mathrm{SI}} = 6.674\,30\times10^{-11}$ is the CODATA-recommended numerical value of $G$ in $\mathrm{m^3\,kg^{-1}\,s^{-2}}$.
--
--   Division is the total real division, so each of these is defined at every argument, with the value $0$ wherever the denominator vanishes.
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Mathlib

namespace GravitationalConstant

/-- The magnitude of the Newtonian gravitational attraction between two point
masses `m₁` and `m₂` whose centres are a distance `r` apart, for a
gravitational constant `G`: `F = G m₁ m₂ / r²`. -/
noncomputable def newtonForce (G m₁ m₂ r : ℝ) : ℝ := G * m₁ * m₂ / r ^ 2

/-- The gravitational field strength ("small g") at the surface of a
spherically symmetric body of mass `M` and radius `R`: `g = G M / R²`. -/
noncomputable def surfaceGravity (G M R : ℝ) : ℝ := G * M / R ^ 2

/-- The volume of a ball of radius `r`: `V = (4/3) π r³`. -/
noncomputable def ballVolume (r : ℝ) : ℝ := 4 / 3 * Real.pi * r ^ 3

/-- The mean density of a body of mass `M` occupying a ball of radius `R`. -/
noncomputable def meanDensity (M R : ℝ) : ℝ := M / ballVolume R

/-- The Einstein gravitational constant `κ = 8 π G / c⁴`, where `c` is the
speed of light. -/
noncomputable def einsteinConstant (G c : ℝ) : ℝ := 8 * Real.pi * G / c ^ 4

/-- A circular orbit of radius `r` and period `P` about a body of mass `M`:
the centripetal acceleration `(2π/P)² r` equals the Newtonian gravitational
acceleration `G M / r²`. -/
def IsCircularOrbit (G M r P : ℝ) : Prop :=
  0 < r ∧ 0 < P ∧ (2 * Real.pi / P) ^ 2 * r = G * M / r ^ 2

/-- The CODATA-recommended numerical value of the gravitational constant in SI
units (m³ kg⁻¹ s⁻²): `6.67430 × 10⁻¹¹`. -/
noncomputable def gravitationalConstantSI : ℝ := 6.67430e-11

end GravitationalConstant


