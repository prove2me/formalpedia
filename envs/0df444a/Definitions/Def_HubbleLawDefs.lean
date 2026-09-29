-- Prove2me | Definitions.Def_HubbleLawDefs
-- name    : HubbleLawDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T04:48:54.575831+00:00
-- url     : https://prove2.me/theorems/c1418e84-8c47-4add-aa84-65c5487bee24
-- title:
--   Scale factor, Hubble and deceleration parameters, proper position and distance
-- statement:
--   This bundle fixes the kinematic model of a uniformly expanding universe used by every
--   statement of the mission. A **scale factor** is a function $a : \mathbb{R} \to \mathbb{R}$ of
--   cosmic time. From it we define four objects.
--
--   The **Hubble parameter** is the logarithmic rate of expansion
--   $$H(t) \;=\; \frac{\dot a(t)}{a(t)},$$
--   whose present-day value is the Hubble constant $H_0$.
--
--   The dimensionless **deceleration parameter** is
--   $$q(t) \;=\; -\,\frac{\ddot a(t)\, a(t)}{\dot a(t)^{2}},$$
--   so that $q > 0$ means a decelerating expansion and $q < 0$ an accelerating one.
--
--   A **comoving point** is a fixed coordinate $\mathbf{x} \in \mathbb{R}^3$, taken with the
--   Euclidean norm; its **proper position** at time $t$ is the physical position
--   $$\mathbf{X}_{\mathbf{x}}(t) \;=\; a(t)\,\mathbf{x},$$
--   and the **proper distance** between the comoving points $\mathbf{x}$ and $\mathbf{y}$ is the
--   physical distance between their proper positions,
--   $$D_{\mathbf{x},\mathbf{y}}(t) \;=\; \big\lVert a(t)\mathbf{x} - a(t)\mathbf{y} \big\rVert .$$
--   All measured proper distances between comoving points therefore increase proportionally to
--   $a$, which is the defining property of the scale factor in the source.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib

namespace HubbleLaw

/-- The Hubble parameter `H(t) = ȧ(t) / a(t)` of a scale factor `a`. -/
noncomputable def hubbleParameter (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- The dimensionless deceleration parameter `q(t) = - ä(t) a(t) / ȧ(t)^2`. -/
noncomputable def decelerationParameter (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(deriv (deriv a) t * a t) / deriv a t ^ 2

/-- The proper position at time `t` of the comoving point with comoving coordinate `x`,
namely `a(t) • x`. -/
noncomputable def properPosition (a : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    EuclideanSpace ℝ (Fin 3) := a t • x

/-- The proper distance at time `t` between the comoving points with comoving
coordinates `x` and `y`. -/
noncomputable def properDistance (a : ℝ → ℝ) (x y : EuclideanSpace ℝ (Fin 3)) (t : ℝ) : ℝ :=
  ‖properPosition a x t - properPosition a y t‖

end HubbleLaw


