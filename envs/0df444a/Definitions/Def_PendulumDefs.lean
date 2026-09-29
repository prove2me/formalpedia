-- Prove2me | Definitions.Def_PendulumDefs
-- name    : PendulumDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T17:19:08.920999+00:00
-- url     : https://prove2.me/theorems/33c06dfa-5a9e-425e-88b1-90b78ace913a
-- title:
--   The simple gravity pendulum: motions, energy, and the period $4\sqrt{\ell/g}\,K(\sin(\theta_0/2))$
-- statement:
--   This is the model on which the whole mission rests: the simple gravity pendulum of
--   *Pendulum (mechanics)*, together with the two periods that the mission compares.
--
--   Let $g$ be the magnitude of the gravitational field and $\ell$ the length of the rod, and let
--   $\theta(t)$ denote the angle between the rod and the downward vertical at time $t$.
--
--   1. **Motions.** A *motion* of the pendulum is a triple of functions $(\theta,\omega,\alpha)$ from
--   $\mathbb R$ to $\mathbb R$ such that $\theta$ is differentiable with derivative $\omega$ at every
--   time, $\omega$ is differentiable with derivative $\alpha$ at every time, and the equation of motion
--   (Eq. 1 of the article)
--
--   $$\alpha(t)=-\frac{g}{\ell}\,\sin\theta(t)$$
--
--   holds at every time. Carrying the angular velocity $\omega$ and the angular acceleration $\alpha$
--   as explicit functions, rather than as formal second derivatives, keeps every differentiability
--   requirement visible in the statements that use the model.
--
--   2. **Harmonic motions.** For a real number $w$, a *harmonic motion of angular frequency $w$* is the
--   same kind of triple satisfying the linear equation $\alpha(t)=-w^2\,\theta(t)$ instead. This is the
--   small-angle model obtained from Eq. 1 by replacing $\sin\theta$ with $\theta$, and it is also the
--   model of the compound pendulum.
--
--   3. **Energy.** The mechanical energy of a motion, per unit of $m\ell^2$, is
--
--   $$E(t)=\frac{\omega(t)^2}{2}-\frac{g}{\ell}\cos\theta(t).$$
--
--   4. **The small-angle period.** $T_0=2\pi\sqrt{\ell/g}$, Huygens's law for the period.
--
--   5. **The complete elliptic integral of the first kind.**
--
--   $$K(k)=\int_0^{\pi/2}\frac{du}{\sqrt{1-k^2\sin^2u}},$$
--
--   defined as an integral over the interval $[0,\pi/2]$.
--
--   6. **The exact period.** For an amplitude $\theta_0$,
--
--   $$T=4\sqrt{\frac{\ell}{g}}\;K\!\left(\sin\frac{\theta_0}{2}\right),$$
--
--   which is Eq. 3 of the article.
--
--   Together these fix the vocabulary of the mission: every milestone and the goal theorem are
--   statements about motions in sense 1 or 2, and the two period functions are the quantities whose
--   relationship the mission establishes.
--
--   **Formalization Note** The two notions of motion are predicates on triples of real functions, so a
--   hypothesis that something *is* a motion carries its own differentiability. $K$ is defined by an
--   interval integral with no integrability hypothesis attached; for $|k|\ge 1$ the integrand is not
--   integrable and the definition returns a junk value, so every statement about $K$ in this mission
--   restricts the modulus. Likewise the period functions use real division and square roots, which are
--   total in Lean: for $g\le 0$ or $\ell\le0$ they return junk values, and the statements that use them
--   assume $g>0$ and $\ell>0$.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

/-
Definition block of the draft Prove2Me mission
**Pendulum (mechanics) I: The Exact Period of the Simple Gravity Pendulum**.

Source: Wikipedia, *Pendulum (mechanics)*, revision 1374595895
(the PDF supplied with this project).

This is the Lean code uploaded as the platform definition item `PendulumDefs`.
-/
import Mathlib

namespace Pendulum

/-! ### Definitions -/

/-- `IsMotion g l theta omega alpha` says that `theta` is a motion of the simple gravity
pendulum of length `l` in a uniform gravitational field of magnitude `g`:
`omega` is its angular velocity, `alpha` its angular acceleration, and the equation of
motion `θ'' = -(g/l) sin θ` (Eq. 1) holds at every time. -/
structure IsMotion (g l : ℝ) (theta omega alpha : ℝ → ℝ) : Prop where
  hasDerivAt_theta : ∀ t, HasDerivAt theta (omega t) t
  hasDerivAt_omega : ∀ t, HasDerivAt omega (alpha t) t
  equation : ∀ t, alpha t = -(g / l) * Real.sin (theta t)

/-- `IsHarmonicMotion w theta omega alpha` says that `theta` solves the harmonic oscillator
equation `θ'' = -w² θ`, with angular velocity `omega` and angular acceleration `alpha`. -/
structure IsHarmonicMotion (w : ℝ) (theta omega alpha : ℝ → ℝ) : Prop where
  hasDerivAt_theta : ∀ t, HasDerivAt theta (omega t) t
  hasDerivAt_omega : ∀ t, HasDerivAt omega (alpha t) t
  equation : ∀ t, alpha t = -(w ^ 2) * theta t

/-- The mechanical energy of the pendulum per unit of `m * l ^ 2`:
`E = ω²/2 - (g/l) cos θ`. -/
noncomputable def energy (g l : ℝ) (theta omega : ℝ → ℝ) (t : ℝ) : ℝ :=
  omega t ^ 2 / 2 - (g / l) * Real.cos (theta t)

/-- The small-angle period `T₀ = 2π √(l/g)` (Huygens's law). -/
noncomputable def smallAnglePeriod (g l : ℝ) : ℝ := 2 * Real.pi * Real.sqrt (l / g)

/-- The complete elliptic integral of the first kind,
`K(k) = ∫₀^{π/2} dφ / √(1 - k² sin² φ)`. -/
noncomputable def ellipticK (k : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.sqrt (1 - k ^ 2 * Real.sin u ^ 2))⁻¹

/-- The exact period of a simple pendulum of length `l` in gravity `g` released from rest at
amplitude `theta0`: `T = 4 √(l/g) K(sin(θ₀/2))` (Eq. 3). -/
noncomputable def exactPeriod (g l theta0 : ℝ) : ℝ :=
  4 * Real.sqrt (l / g) * ellipticK (Real.sin (theta0 / 2))

end Pendulum


