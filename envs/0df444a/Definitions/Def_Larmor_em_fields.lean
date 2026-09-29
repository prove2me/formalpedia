-- Prove2me | Definitions.Def_Larmor_em_fields
-- name    : Larmor_em_fields
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T01:02:32.743963+00:00
-- url     : https://prove2.me/theorems/d4343ec4-14c3-42c7-b9c1-bb82c1b404e5
-- title:
--   Maxwell's equations, the Poynting vector and the electromagnetic energy density (SI)
-- statement:
--   This file states Maxwell's equations in vacuum, in SI units, together with the two energy quantities of the electromagnetic field.
--
--   A field configuration consists of a charge density $\rho(t,x)$, a current density $J(t,x)$, an electric field $E(t,x)$ and a magnetic field $B(t,x)$, all functions of a time $t\in\mathbb{R}$ and a position $x\in\mathbb{R}^3$. Given a permittivity $\varepsilon_0$ and a speed of light $c$ — so that the vacuum permeability is $\mu_0=1/(\varepsilon_0c^2)$ — the configuration is said to satisfy **Maxwell's equations** when, at every time and every point,
--
--   $$\nabla\cdot E=\frac{\rho}{\varepsilon_0},\qquad
--   \nabla\cdot B=0,\qquad
--   \nabla\times E=-\,\partial_tB,\qquad
--   \nabla\times B=\frac{1}{\varepsilon_0c^2}\,J+\frac{1}{c^2}\,\partial_tE .$$
--
--   These are, in order, Gauss's law, the absence of magnetic monopoles, Faraday's law of induction and the Ampère–Maxwell law.
--
--   The **Poynting vector** and the **electromagnetic energy density** are
--   $$S=\frac{1}{\mu_0}\,E\times B=\varepsilon_0c^2\,(E\times B),\qquad
--   u=\frac{\varepsilon_0}{2}\bigl(\|E\|^2+c^2\|B\|^2\bigr).$$
--
--   $S$ is the energy flux density of the field and $u$ its energy per unit volume; Poynting's theorem, stated elsewhere in this mission, is what licenses those interpretations, and the surface integral of $S$ is what the Larmor formula evaluates.
--
--   **Formalization Note** The divergence, curl and cross product are those of the mission's vector-calculus file. Time derivatives are ordinary derivatives of the map $s\mapsto E(s,x)$ at fixed $x$; where a field is not differentiable, the ambient convention gives the derivative value $0$. The permeability $\mu_0$ is never a primitive constant: it appears only as $1/(\varepsilon_0c^2)$.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section ("we integrate the Poynting vector over the surface of a sphere of radius R"); J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, §6.7 (Poynting's theorem, energy density and energy flux) and §6.1 (Maxwell's equations in SI units).

import Definitions.Def_Larmor_vec3

namespace Larmor

/-- Maxwell's equations in vacuum, in SI units, for a charge density `ρ` and a current
density `J`, with `ε₀` the vacuum permittivity and `c` the speed of light (so that the
vacuum permeability is `μ₀ = 1 / (ε₀ * c ^ 2)`).  Fields are functions of time and
position. -/
structure IsMaxwell (ε₀ c : ℝ) (ρ : ℝ → Vec → ℝ) (J E B : ℝ → Vec → Vec) : Prop where
  /-- Gauss's law. -/
  gauss : ∀ t x, divg (E t) x = ρ t x / ε₀
  /-- Absence of magnetic monopoles. -/
  noMonopole : ∀ t x, divg (B t) x = 0
  /-- Faraday's law of induction. -/
  faraday : ∀ t x, curl (E t) x = -deriv (fun s => B s x) t
  /-- The Ampère-Maxwell law. -/
  ampere : ∀ t x, curl (B t) x
      = (1 / (ε₀ * c ^ 2)) • J t x + (1 / c ^ 2) • deriv (fun s => E s x) t

/-- The Poynting vector `S = (1 / μ₀) E × B = ε₀ c ^ 2 (E × B)`, the energy flux density of
the electromagnetic field. -/
noncomputable def poynting (ε₀ c : ℝ) (E B : Vec) : Vec := (ε₀ * c ^ 2) • cross E B

/-- The electromagnetic energy density `u = (ε₀ / 2) (‖E‖ ^ 2 + c ^ 2 ‖B‖ ^ 2)`. -/
noncomputable def energyDensity (ε₀ c : ℝ) (E B : Vec) : ℝ :=
  ε₀ / 2 * (‖E‖ ^ 2 + c ^ 2 * ‖B‖ ^ 2)

end Larmor


