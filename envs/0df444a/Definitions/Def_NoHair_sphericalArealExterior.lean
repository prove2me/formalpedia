-- Prove2me | Definitions.Def_NoHair_sphericalArealExterior
-- name    : NoHair_sphericalArealExterior
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T20:50:51.364165+00:00
-- url     : https://prove2.me/theorems/5d48b8ca-dcb9-4f7b-8261-67f7ea8944e6
-- title:
--   Static spherical areal chart with electric and magnetic flux profiles
-- statement:
--   Let $D$ be a region of a four-dimensional spacetime with metric $g$ and electromagnetic two-form $F$. A spherical areal chart consists of a number $R>0$ and a diffeomorphism from the full coordinate exterior $r>R$ onto the open set $D$. Here $r$ is the Euclidean spatial radius in the chart. Write $k=dt+dr$, let $B=d(k/r)$ be the unit Coulomb field, and take the Hodge dual using the metric in this chart.
--
--   There are three radial functions: the squared lapse $A$ and the electric and magnetic flux coefficients $q,p$. The pullbacks satisfy
--
--   $$
--   g=\eta+(1-A(r))k\otimes k,\qquad F=q(r)B+p(r)\star_g B.
--   $$
--
--   The lapse is continuous on $[R,\infty)$, vanishes at $R$, and is positive on $(R,\infty)$. The definition leaves the three radial functions free for the field equations to determine.
-- source:
--   H. S. Reall, Part III Black Holes (2024), §6.1, p. 82, equations (6.2)–(6.6), https://www.damtp.cam.ac.uk/user/hsr1000/black_holes_lectures_2024.pdf. Areal Kerr–Schild chart and unit Coulomb field in the notation of NoHair_spacetime.

import Definitions.Def_NoHair_spacetime

open scoped ContDiff Manifold
open Set

namespace NoHair

/-- A global static spherical chart in areal Kerr–Schild coordinates. The squared lapse
and the coefficients of the unit Coulomb field and its dual are radial functions. -/
structure SphericalArealExterior {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (D : Set M) where
  horizonRadius : ℝ
  radius_pos : 0 < horizonRadius
  chart : E4 → M
  isOpen_domain : IsOpen D
  diffeo : IsDiffeoOnto chart {y | horizonRadius < ksRadius 0 y} D
  lapseSq : ℝ → ℝ
  electricFlux : ℝ → ℝ
  magneticFlux : ℝ → ℝ
  lapse_continuous : ContinuousOn lapseSq (Ici horizonRadius)
  lapse_horizon : lapseSq horizonRadius = 0
  lapse_pos : ∀ r, horizonRadius < r → 0 < lapseSq r
  metric_coeffs : ∀ y, horizonRadius < ksRadius 0 y →
    pullbackCoeffs g chart y = fun μ ν =>
      minkowski μ ν + (1 - lapseSq (ksRadius 0 y)) * ksNull 0 y μ * ksNull 0 y ν
  field_coeffs : ∀ y, horizonRadius < ksRadius 0 y →
    pullbackCoeffs F chart y =
      electricFlux (ksRadius 0 y) • kerrNewmanField 0 1 y +
      magneticFlux (ksRadius 0 y) • hodgeDual (pullbackCoeffs g chart y) (kerrNewmanField 0 1 y)

end NoHair


