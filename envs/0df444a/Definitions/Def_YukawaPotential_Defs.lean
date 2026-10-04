-- Prove2me | Definitions.Def_YukawaPotential_Defs
-- name    : YukawaPotential_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-03T12:14:01.073367+00:00
-- url     : https://prove2.me/theorems/8d902eb5-fa06-438f-a813-07d84a7970ec
-- title:
--   Yukawa potential and the potential of a uniform spherical shell
-- statement:
--   Two definitions used throughout the mission.
--
--   1. **Yukawa potential.** For real parameters $g$ (coupling), $\alpha$ (scaling constant), $m$ (mass) and a radial distance $r$,
--   $$V_{g,\alpha,m}(r) = -g^2\,\frac{e^{-\alpha m r}}{r}.$$
--
--   2. **Potential of a uniform spherical shell.** For a thin uniform shell of radius $R$ centred at the origin with total scaling constant $G$, the potential at $x\in\mathbb R^3$ felt by a point of scaling constant $g$ is $G g$ times the average, over the unit sphere $S^2$ with its uniform surface measure $\sigma$, of the pair interaction:
--   $$V^{\mathrm{shell}}_{G,g,\alpha,m,R}(x) = G\,g\;\frac{1}{\sigma(S^2)}\int_{S^2}\frac{e^{-\alpha m\,|x-Ru|}}{|x-Ru|}\,d\sigma(u).$$
--
--   These are the objects of the article's introduction and of its section *Spherical shell*.
--
--   **Formalization Note** Lean's division by zero returns $0$, so $V(0)=0$ and the shell integrand is $0$ at a point $u$ with $x=Ru$; statements about these objects restrict to $r>0$, $x\ne0$, or $|x|\neq R$ as appropriate. The surface measure is Mathlib's `Measure.toSphere` of Lebesgue measure; the definition uses the normalised average `⨍`.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, introduction (definition of V_Yukawa) and section 'Spherical shell'.

import Mathlib

namespace YukawaPotential

open MeasureTheory

/-- The Yukawa (screened Coulomb) potential
`V(r) = -g^2 * exp(-α m r) / r`, with coupling `g`, scaling constant `α`,
mass `m` and radial distance `r`. -/
noncomputable def yukawaPotential (g α m r : ℝ) : ℝ :=
  -g ^ 2 * Real.exp (-(α * m * r)) / r

/-- Potential at the point `x ∈ ℝ³` felt by a point of scaling constant `g`, produced by an
infinitesimally thin uniform spherical shell of radius `R` centred at the origin with total
scaling constant `G`, where each pair interacts through `G g exp(-α m d) / d` at distance `d`:
`G g` times the average of `exp(-α m ‖x - R u‖) / ‖x - R u‖` over the unit sphere `u ∈ S²`
(with respect to the uniform surface measure). -/
noncomputable def yukawaShellPotential (G g α m R : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  G * g * ⨍ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
    Real.exp (-(α * m * ‖x - R • (u : EuclideanSpace ℝ (Fin 3))‖)) /
      ‖x - R • (u : EuclideanSpace ℝ (Fin 3))‖ ∂(volume.toSphere)

end YukawaPotential


