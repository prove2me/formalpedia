-- Prove2me | Definitions.Def_FRWUniverse
-- name    : FRWUniverse
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T00:43:29.709182+00:00
-- url     : https://prove2.me/theorems/4d6441d9-9403-4ad0-ace1-e37067443eed
-- title:
--   FRW universe satisfying the two Friedmann equations
-- statement:
--   An **FRW universe** is the bundle of data appearing in the Friedmann–Robertson–Walker
--   model, together with the two Friedmann equations imposed as axioms.
--
--   The data are: a gravitational constant $G$; a spatial curvature constant $K$; a set of
--   cosmic times $I \subseteq \mathbb{R}$, assumed open and preconnected; a strictly positive
--   scale factor $a$ on $I$; an energy density $\rho$; a pressure $p$; and three further
--   functions $\dot a$, $\ddot a$, $\dot\rho$ that are required to be the derivatives of $a$,
--   $\dot a$ and $\rho$ at every point of $I$.
--
--   Two equations are imposed at every $t \in I$, with the Hubble parameter written
--   $H = \dot a/a$ and its derivative written $\dot H = \ddot a / a - (\dot a/a)^2$:
--
--   $$H^2 = \frac{8\pi G}{3}\rho - \frac{K}{a^2}, \qquad \dot H = -4\pi G(\rho + p) + \frac{K}{a^2}.$$
--
--   The file also defines the Hubble parameter $H = \dot a / a$ as a function on all of
--   $\mathbb{R}$, and the predicate expressing the **linear barotropic equation of state**
--   $p(t) = w\,\rho(t)$ for all $t \in I$, for a constant $w$.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, Chapter 4, §4.3, eqs. (4.24)-(4.26) pp. 55-56, and eq. (4.30) p. 60

import Mathlib

namespace FRWCosmology

/-- A Friedmann–Robertson–Walker (FRW) universe on a time interval.

The data are Newton's constant `G`, the spatial curvature constant `K`, an open connected
time domain `I`, the scale factor `a` with its first two derivatives `adot`, `addot`, the
energy density `rho` with its derivative `rhodot`, and the pressure `p`.

The two Friedmann equations are imposed pointwise on `I`, in the form of the source:
`H ^ 2 = 8 π G ρ / 3 - K / a ^ 2` and `Ḣ = -4 π G (ρ + p) + K / a ^ 2`, where the Hubble
parameter is `H = adot / a` and `Ḣ = addot / a - (adot / a) ^ 2`. -/
structure FRWUniverse where
  /-- Newton's gravitational constant. -/
  G : ℝ
  /-- The spatial curvature constant of the Robertson–Walker metric. -/
  K : ℝ
  /-- The time domain on which the solution is considered. -/
  I : Set ℝ
  /-- The scale factor. -/
  a : ℝ → ℝ
  /-- The time derivative of the scale factor. -/
  adot : ℝ → ℝ
  /-- The second time derivative of the scale factor. -/
  addot : ℝ → ℝ
  /-- The energy density. -/
  rho : ℝ → ℝ
  /-- The time derivative of the energy density. -/
  rhodot : ℝ → ℝ
  /-- The pressure. -/
  p : ℝ → ℝ
  I_open : IsOpen I
  I_conn : IsPreconnected I
  a_pos : ∀ t ∈ I, 0 < a t
  ha : ∀ t ∈ I, HasDerivAt a (adot t) t
  hadot : ∀ t ∈ I, HasDerivAt adot (addot t) t
  hrho : ∀ t ∈ I, HasDerivAt rho (rhodot t) t
  friedmann₁ : ∀ t ∈ I, (adot t / a t) ^ 2 = 8 * Real.pi * G / 3 * rho t - K / a t ^ 2
  friedmann₂ : ∀ t ∈ I, addot t / a t - (adot t / a t) ^ 2 =
    -(4 * Real.pi * G) * (rho t + p t) + K / a t ^ 2

/-- The Hubble parameter `H = ȧ / a`. -/
noncomputable def FRWUniverse.H (U : FRWUniverse) (t : ℝ) : ℝ := U.adot t / U.a t

/-- The linear barotropic equation of state `p = w ρ`, with `w` a constant. -/
def FRWUniverse.LinearEoS (U : FRWUniverse) (w : ℝ) : Prop := ∀ t ∈ U.I, U.p t = w * U.rho t

end FRWCosmology


