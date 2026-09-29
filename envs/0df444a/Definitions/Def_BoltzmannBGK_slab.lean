-- Prove2me | Definitions.Def_BoltzmannBGK_slab
-- name    : BoltzmannBGK_slab
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T22:15:22.408098+00:00
-- url     : https://prove2.me/theorems/c7648421-3899-4dfc-a238-0bcb8d8cb908
-- title:
--   Slab-geometry reduction of the BGK model
-- statement:
--   This file sets up the slab geometry of parts (c) and (d) of the source question. There the position is $x=(x,y,z)$, the bulk velocity is $u=(u,0,0)$, the velocity splits as $v=(w,w_\perp)$ with $w_\perp=(v_y,v_z)$, and the distribution function is independent of $y$ and $z$.
--
--   The three-dimensional Maxwellian written in these variables is
--
--   $$M(w,w_\perp)=\frac{\rho}{(2\pi\theta)^{3/2}}\exp\Big(-\frac{(w-u)^2+|w_\perp|^2}{2\theta}\Big),$$
--
--   and the one-dimensional Maxwellian is
--
--   $$g^{(0)}(w)=\frac{\rho}{(2\pi\theta)^{1/2}}\exp\Big(-\frac{(w-u)^2}{2\theta}\Big).$$
--
--   Given a distribution $F(w,w_\perp)$, the two reduced fields of part (c) are obtained by integrating out the perpendicular velocity,
--
--   $$g(w)=\int \mathrm dw_\perp\,F(w,w_\perp),\qquad h(w)=\int \mathrm dw_\perp\,|w_\perp|^2 F(w,w_\perp).$$
--
--   The hydrodynamic quantities of the reduced system are
--
--   $$\rho=\int \mathrm dv\,g,\qquad u=\frac1\rho\int \mathrm dv\,v\,g,\qquad 3\rho\theta=\int \mathrm dv\,(v-u)^2 g+\int \mathrm dv\,h,$$
--
--   and the two further quantities of part (d) are
--
--   $$T=-2\rho\theta+\int \mathrm dv\,h,\qquad q=\frac12\int \mathrm dv\,w^3 g+\frac12\int \mathrm dv\,w\,h,$$
--
--   with $w=v-u$ the peculiar velocity; $T$ is the deviatoric part of the longitudinal stress and $q$ is the heat flux.
--
--   **Formalization Note** The perpendicular velocity lives in `EuclideanSpace ℝ (Fin 2)` and the reduced fields are ordinary real functions of one real variable; all integrals are against Lebesgue measure. The quantities $\rho$, $u$, $\theta$, $T$ and $q$ are defined as functions of the reduced pair $(g,h)$ rather than being supplied as parameters, so they cannot be instantiated independently of the fields.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Parts (c) and (d).

import Mathlib

noncomputable section

open MeasureTheory Real

namespace BoltzmannBGK

/-- The two perpendicular velocity components `v⊥ = (v_y, v_z)`. -/
abbrev Perp := EuclideanSpace ℝ (Fin 2)

/-- The three–dimensional Maxwellian written in slab geometry, where the bulk velocity is
`u = (u, 0, 0)`, the velocity is `v = (w, w⊥)`, and the distribution depends on `x` only:
`ρ (2πθ)^(-3/2) exp (-((w - u)² + |w⊥|²)/(2θ))`. -/
def maxwellianSlab (ρ u θ : ℝ) (w : ℝ) (wperp : Perp) : ℝ :=
  ρ / (2 * π * θ) ^ (3 / 2 : ℝ) * exp (-(((w - u) ^ 2 + ‖wperp‖ ^ 2) / (2 * θ)))

/-- The one–dimensional Maxwellian `ρ (2πθ)^(-1/2) exp (-(w - u)²/(2θ))`. -/
def maxwellian1d (ρ u θ : ℝ) (w : ℝ) : ℝ :=
  ρ / (2 * π * θ) ^ (1 / 2 : ℝ) * exp (-((w - u) ^ 2 / (2 * θ)))

/-- The reduced distribution `g(w) = ∫ dw⊥ F(w, w⊥)`. -/
def reduceG (F : ℝ → Perp → ℝ) (w : ℝ) : ℝ := ∫ wperp, F w wperp

/-- The reduced distribution `h(w) = ∫ dw⊥ |w⊥|² F(w, w⊥)`. -/
def reduceH (F : ℝ → Perp → ℝ) (w : ℝ) : ℝ := ∫ wperp, ‖wperp‖ ^ 2 * F w wperp

/-- Mass density of the reduced system, `ρ = ∫ dv g`. -/
def density1d (g : ℝ → ℝ) : ℝ := ∫ v, g v

/-- Bulk velocity of the reduced system, `u = (1/ρ) ∫ dv v g`. -/
def bulkVelocity1d (g : ℝ → ℝ) : ℝ := (∫ v, v * g v) / density1d g

/-- Temperature of the reduced system, `3ρθ = ∫ dv (v - u)² g + ∫ dv h`. -/
def temperature1d (g h : ℝ → ℝ) : ℝ :=
  ((∫ v, (v - bulkVelocity1d g) ^ 2 * g v) + ∫ v, h v) / (3 * density1d g)

/-- The quantity `T = -2ρθ + ∫ dv h` of the reduced system. -/
def stressT (g h : ℝ → ℝ) : ℝ :=
  -2 * density1d g * temperature1d g h + ∫ v, h v

/-- The quantity `q = ½ ∫ dv w³ g + ½ ∫ dv w h`, where `w = v - u` is the peculiar velocity. -/
def heatFlux (g h : ℝ → ℝ) : ℝ :=
  1 / 2 * (∫ v, (v - bulkVelocity1d g) ^ 3 * g v) +
    1 / 2 * (∫ v, (v - bulkVelocity1d g) * h v)

end BoltzmannBGK


