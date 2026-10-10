-- Prove2me | Definitions.Def_hack_flrw_friedmann
-- name    : hack_flrw_friedmann
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:26:15.381988+00:00
-- url     : https://prove2.me/theorems/851eb86b-56c2-4627-9779-6a6deff1a3c9
-- title:
--   Flat FLRW cosmology: Hubble rate $H=\dot a/a$ and the two Friedmann equations
-- statement:
--   This definition file fixes the notation of Hack (2016), Section 3.1, for spatially flat FLRW cosmology.
--
--   Let $a:\mathbb R\to\mathbb R$ be the scale factor, $\rho,p:\mathbb R\to\mathbb R$ the energy density and pressure, $G$ Newton's constant, and $I\subseteq\mathbb R$ a set of cosmological times.
--
--   1. **Hubble rate** (eq. (3.1)): $H(t)=\dfrac{\dot a(t)}{a(t)}$.
--   2. **First Friedmann equation on $I$** (eq. (3.5)): for every $t\in I$,
--   $$H(t)^2=\frac{8\pi G}{3}\,\rho(t).$$
--   3. **Second Friedmann equation on $I$** (eq. (3.5)): for every $t\in I$,
--   $$\frac{\ddot a(t)}{a(t)}=-\frac{4\pi G}{3}\,\big(\rho(t)+3p(t)\big).$$
--
--   Every statement in the mission is phrased in terms of these three objects.
--
--   **Formalization Note** Derivatives are Mathlib's `deriv` (equal to $0$ where the function is not differentiable) and $\ddot a$ is the derivative of the function $t\mapsto\dot a(t)$. Lean's division gives $x/0=0$. The definitions impose no regularity or positivity; each theorem states these hypotheses explicitly.
-- source:
--   T.-P. Hack, *Cosmological Applications of Algebraic Quantum Field Theory in Curved Spacetimes*, SpringerBriefs in Mathematical Physics 6, Springer, 2016, DOI 10.1007/978-3-319-21894-6 (https://doi.org/10.1007/978-3-319-21894-6), Sect. 3.1, pp. 78–80, eqs. (3.1), (3.5)

import Mathlib

namespace HackCosmologicalAQFT

/-- The Hubble rate `H(t) = ȧ(t) / a(t)` of a scale factor `a` (Hack 2016, eq. (3.1)). -/
noncomputable def hubbleRate (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- The first Friedmann equation `H² = (8πG/3) ρ` (Hack 2016, eq. (3.5)),
holding at every cosmological time `t ∈ I`. -/
def FirstFriedmannEq (G : ℝ) (a ρ : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, hubbleRate a t ^ 2 = 8 * Real.pi * G / 3 * ρ t

/-- The second Friedmann equation `ä / a = -(4πG/3) (ρ + 3p)` (Hack 2016, eq. (3.5)),
holding at every cosmological time `t ∈ I`. -/
def SecondFriedmannEq (G : ℝ) (a ρ p : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, deriv (deriv a) t / a t = -(4 * Real.pi * G / 3) * (ρ t + 3 * p t)

end HackCosmologicalAQFT


