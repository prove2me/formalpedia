-- Prove2me | Definitions.Def_planck_units
-- name    : planck_units
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T21:28:44.398677+00:00
-- url     : https://prove2.me/theorems/8d516ef6-ea28-4cc2-a361-96f21f282b89
-- title:
--   Systems of base units, normalization of $c,G,\hbar,k_B$, and the Planck system
-- statement:
--   This bundle sets up the objects the mission is stated in terms of.
--
--   A **unit system** is a quadruple $u=(L,M,T,\Theta)$ of real numbers: the sizes of a chosen unit of length, mass, time and temperature, measured in some fixed reference system of units (SI, say). The predicate `IsPositive` says all four are strictly positive.
--
--   Given four real constants $c,G,\hbar,k_B$, the predicate `Normalizes` says that each of them has numerical value $1$ when expressed in the units of $u$, i.e. that
--
--   $$\frac{L}{T}=c,\qquad \frac{L^{3}}{M\,T^{2}}=G,\qquad \frac{M\,L^{2}}{T}=\hbar,\qquad \frac{M\,L^{2}}{T^{2}\,\Theta}=k_B,$$
--
--   the four left-hand sides being the coherent unit of speed, of the dimension $L^{3}M^{-1}T^{-2}$ of the gravitational constant, of action, and of heat capacity.
--
--   Finally, `planckSystem` is the quadruple of Table 1 of the source,
--
--   $$l_P=\sqrt{\frac{\hbar G}{c^{3}}},\qquad m_P=\sqrt{\frac{\hbar c}{G}},\qquad t_P=\sqrt{\frac{\hbar G}{c^{5}}},\qquad T_P=\frac{1}{k_B}\sqrt{\frac{\hbar c^{5}}{G}}.$$
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Mathlib

namespace PlanckUnits

/-- A system of base units: a length, mass, time and temperature, recorded as
bare real numbers (their sizes in some fixed reference system).  Positivity is
not built in; it is imposed separately by `UnitSystem.IsPositive`. -/
structure UnitSystem where
  length : ℝ
  mass : ℝ
  time : ℝ
  temperature : ℝ

/-- All four base units are positive. -/
def UnitSystem.IsPositive (u : UnitSystem) : Prop :=
  0 < u.length ∧ 0 < u.mass ∧ 0 < u.time ∧ 0 < u.temperature

/-- `u` normalizes the four constants `c`, `G`, `ħ`, `k_B`: measured in the base
units of `u`, each of the four has numerical value `1`.  Written out, the speed
`length/time`, the quantity `length³/(mass·time²)`, the action
`mass·length²/time` and the heat capacity `mass·length²/(time²·temperature)`
equal `c`, `G`, `ħ` and `k_B` respectively. -/
def UnitSystem.Normalizes (u : UnitSystem) (c G hbar kB : ℝ) : Prop :=
  u.length / u.time = c ∧
  u.length ^ 3 / (u.mass * u.time ^ 2) = G ∧
  u.mass * u.length ^ 2 / u.time = hbar ∧
  u.mass * u.length ^ 2 / (u.time ^ 2 * u.temperature) = kB

/-- The Planck system of units:
`l_P = √(ħG/c³)`, `m_P = √(ħc/G)`, `t_P = √(ħG/c⁵)`, `T_P = √(ħc⁵/G)/k_B`. -/
noncomputable def planckSystem (c G hbar kB : ℝ) : UnitSystem where
  length := Real.sqrt (hbar * G / c ^ 3)
  mass := Real.sqrt (hbar * c / G)
  time := Real.sqrt (hbar * G / c ^ 5)
  temperature := Real.sqrt (hbar * c ^ 5 / G) / kB

end PlanckUnits


