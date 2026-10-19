-- Prove2me | Definitions.Def_bohm_states
-- name    : bohm_states
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T22:49:24.282323+00:00
-- url     : https://prove2.me/theorems/48ed2ac8-3742-4aeb-9203-a82101a0b5be
-- title:
--   Bohmian states: density, current, and the guiding velocity field
-- statement:
--   The vocabulary of the Bohmian theory of a spinless particle on a line, in the source's own normalization. For a wavefunction ψ : ℝ → ℂ the bundle defines three quantities. The probability density ρ(q) = |ψ(q)|² — the position distribution of quantum equilibrium, the distribution the theory postulates at one moment of time and proves for all times. The probability current j(q) = (ℏ/m) Im(ψ(q)* ψ'(q)) — the flux of the equilibrium density, the quantity whose conservation under Schrödinger evolution is the goal theorem of the mission. The Bohmian velocity field v(q) = (ℏ/m) Im(ψ'(q)/ψ(q)) — the guiding equation in its phase-gradient form: the velocity of the particle when the configuration is q.
--
--   The reduced Planck constant ℏ and the mass m are explicit real parameters, the standing conventions of the fragment; every theorem states the positivity it needs. The definitions are total functions: where a derivative does not exist, Lean's deriv returns its junk value, and where ψ vanishes, the quotient degenerates; each theorem that uses these definitions carries the differentiability and nonvanishing hypotheses under which the expression is the source's.
--
--   **Formalization Note** The three definitions are the one-dimensional, one-particle case of the source's displayed chain m_k dq^k/dt = ħ Im(∇_k ψ/ψ) = j_k/(ψ*ψ), the configuration space being the line ℝ — the basic setup the source presents before the three-dimensional and many-particle extensions.
-- source:
--   "De Broglie–Bohm theory", Wikipedia, retrieved 2026-10-18, oldid 1371420612, sections "Overview" and "Guiding equation"

import Mathlib

open ComplexConjugate

namespace Bohm

/-- The probability density carried by a spinless one-dimensional
wavefunction: |ψ(q)|², the position distribution of quantum
equilibrium — the distribution the theory postulates at one moment
and proves for all times. -/
def density (ψ : ℝ → ℂ) (q : ℝ) : ℝ := Complex.normSq (ψ q)

/-- The probability current, j = (ℏ/m) Im(ψ(q)* ψ'(q)): the flux of the
quantum equilibrium density, in the normalization of the source's
displayed chain (so that the velocity field is the current divided by
the density). -/
noncomputable def current (ℏ m : ℝ) (ψ : ℝ → ℂ) (q : ℝ) : ℝ :=
  (ℏ / m) * Complex.im (conj (ψ q) * deriv ψ q)

/-- The Bohmian velocity field of the guiding equation, in the
phase-gradient form v = (ℏ/m) Im(ψ'(q)/ψ(q)): the velocity of the
particle at the configuration point q. -/
noncomputable def guide (ℏ m : ℝ) (ψ : ℝ → ℂ) (q : ℝ) : ℝ :=
  (ℏ / m) * Complex.im (deriv ψ q / ψ q)

end Bohm


