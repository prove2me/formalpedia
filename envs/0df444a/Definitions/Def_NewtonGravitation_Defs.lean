-- Prove2me | Definitions.Def_NewtonGravitation_Defs
-- name    : NewtonGravitation_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T17:30:48.623096+00:00
-- url     : https://prove2.me/theorems/c03c094a-463c-46ac-9e32-be15df3d8270
-- title:
--   Newtonian gravitation: point force, fields, potential, symmetric mass distributions
-- statement:
--   This bundle fixes the objects of Newtonian gravitation used by every statement in the mission. Space is $\mathbb{E}^3 = \mathbb{R}^3$ with the Euclidean norm, and $G = 6.67430\times10^{-11}$.
--
--   1. **Point force** (vector form of the law). For masses $m_1,m_2$ at positions $r_1,r_2$,
--   $$F_{21}(m_1,m_2,r_1,r_2) = -\frac{G m_1 m_2}{\|r_2-r_1\|^2}\cdot\frac{r_2-r_1}{\|r_2-r_1\|},$$
--   the force applied on body 2 by body 1.
--   2. **Point field** of a mass $M$ at $c$: $g_{M,c}(x) = -\dfrac{GM}{\|x-c\|^3}(x-c)$.
--   3. **Point potential** of a mass $M$ at $c$: $V_{M,c}(x) = -\dfrac{GM}{\|x-c\|}$.
--   4. **Field of a mass distribution** $\mu$ (a measure on $\mathbb{E}^3$):
--   $$g_\mu(x) = \int -\frac{G}{\|x-y\|^3}(x-y)\,d\mu(y).$$
--   5. **Spherical symmetry**: $\mu\circ A^{-1} = \mu$ for every linear isometry $A$ of $\mathbb{E}^3$.
--   6. **Uniform shell** $\sigma_{M,a}$: the surface measure of the unit sphere, pushed forward by $u\mapsto a u$ and scaled to total mass $M\ge 0$.
--   7. **Uniform solid ball** $\beta_{M,R}$: Lebesgue measure on the open ball $\|y\|<R$, scaled to total mass $M\ge0$.
--
--   These are the basic notions in terms of which the shell theorem and its corollaries are stated.
--
--   **Formalization Note** At coincident points the formulas divide by zero; Lean's convention $a/0 = 0$ makes the point force and point field equal to $0$ there, and the corresponding theorems exclude that case where relevant. A non-integrable Bochner integral is $0$. For $R\le 0$ the "uniform ball" is the zero measure; theorems assume positive radii.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529), sections Modern form, Vector form, Gravity field, Bodies with spatial extent

import Mathlib

open MeasureTheory

namespace NewtonGravitation

/-- Physical space: three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The Newtonian constant of gravitation, `G = 6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²` (CODATA 2022). -/
noncomputable def G : ℝ := 6.67430e-11

/-- Vector form of Newton's law: the force `F₂₁` applied on body 2 (mass `m₂`, position `r₂`)
exerted by body 1 (mass `m₁`, position `r₁`):
`F₂₁ = -G m₁ m₂ / ‖r₂₁‖² • r̂₂₁`, with `r₂₁ = r₂ - r₁` and `r̂₂₁ = r₂₁ / ‖r₂₁‖`. -/
noncomputable def pointForce (m₁ m₂ : ℝ) (r₁ r₂ : Space) : Space :=
  -(G * m₁ * m₂ / ‖r₂ - r₁‖ ^ 2) • (‖r₂ - r₁‖⁻¹ • (r₂ - r₁))

/-- Gravitational field at `x` of a point mass `M` located at `c`:
`g(x) = -G M / ‖x - c‖³ • (x - c)`. -/
noncomputable def pointField (M : ℝ) (c x : Space) : Space :=
  -(G * M / ‖x - c‖ ^ 3) • (x - c)

/-- Gravitational potential at `x` of a point mass `M` located at `c`: `V(x) = -G M / ‖x - c‖`. -/
noncomputable def pointPotential (M : ℝ) (c x : Space) : ℝ :=
  -(G * M / ‖x - c‖)

/-- Gravitational field at `x` produced by a mass distribution `μ` (a measure on space, giving the
mass of each region): the superposition (integral) of the point-mass fields of its elements,
`g_μ(x) = ∫ -G / ‖x - y‖³ • (x - y) dμ(y)`. -/
noncomputable def gravField (μ : Measure Space) (x : Space) : Space :=
  ∫ y, -(G / ‖x - y‖ ^ 3) • (x - y) ∂μ

/-- A mass distribution is spherically symmetric about the origin if it is invariant under every
linear isometry of space (every rotation and reflection fixing the origin). -/
def IsSphericallySymmetric (μ : Measure Space) : Prop :=
  ∀ A : Space ≃ₗᵢ[ℝ] Space, μ.map A = μ

/-- A uniform spherical shell of total mass `M` and radius `a`, centred at the origin: the surface
measure of the unit sphere, transported to the sphere of radius `a`, normalised to total mass `M`. -/
noncomputable def uniformShell (M : NNReal) (a : ℝ) : Measure Space :=
  ((M : ENNReal) / (volume : Measure Space).toSphere Set.univ) •
    ((volume : Measure Space).toSphere.map (fun u : Metric.sphere (0 : Space) 1 => a • (u : Space)))

/-- A uniform solid ball of total mass `M` and radius `R`, centred at the origin: Lebesgue measure
restricted to the open ball, normalised to total mass `M`. -/
noncomputable def uniformBall (M : NNReal) (R : ℝ) : Measure Space :=
  ((M : ENNReal) / volume (Metric.ball (0 : Space) R)) • volume.restrict (Metric.ball (0 : Space) R)

end NewtonGravitation


