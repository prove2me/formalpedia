-- Prove2me | Definitions.Def_HunterPDE_Harmonic_MeanValue
-- name    : HunterPDE_Harmonic_MeanValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:55:13.853103+00:00
-- url     : https://prove2.me/theorems/78d28955-756f-4b85-bb41-1249cae078a5
-- title:
--   Sphere average (1.3) and the mean-value property (2.3)
-- statement:
--   Let $n \in \mathbb{N}$, $x \in \mathbb{R}^n$, $r > 0$ and $u : \mathbb{R}^n \to \mathbb{R}$. The **average of $u$ over the sphere** $\partial B_r(x) = \{y : |y - x| = r\}$ is
--   $$⨍_{\partial B_r(x)} u \, dS = \frac{1}{n\alpha_n r^{n-1}} \int_{\partial B_r(x)} u \, dS, \qquad (1.3)$$
--   where $dS$ is surface measure and $n\alpha_n$ is the area of the unit sphere. The average over the open ball $B_r(x)$ is $⨍_{B_r(x)} u\,dx = \frac{1}{\alpha_n r^n}\int_{B_r(x)} u\,dx$.
--
--   A function $u$ on an open set $\Omega \subseteq \mathbb{R}^n$ has the **mean-value property** (2.3) if for every ball with $B_r(x) \Subset \Omega$ (that is, $r > 0$ and the closed ball $\overline{B}_r(x)$ lies in $\Omega$)
--   $$u(x) = ⨍_{B_r(x)} u \, dx, \qquad u(x) = ⨍_{\partial B_r(x)} u \, dS.$$
--
--   Theorem 2.1 says that harmonic functions have this property; Theorem 2.2 is the converse.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`; the ball average is Mathlib's set average `⨍ y in Metric.ball x r, u y`. The sphere average is written in polar form as the normalized integral of $\omega \mapsto u(x + r\omega)$ over the unit sphere against Mathlib's surface measure `volume.toSphere` (total mass $n\alpha_n$); since it is an average, the factor $r^{n-1}$ cancels and only the uniform (rotation-invariant) shape of the measure matters. `sphereAverage` is used only for $r > 0$. Both identities of (2.3) are required, as in the book's display.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 8, Eq. (1.3), and p. 20, Eq. (2.3)

import Mathlib

open MeasureTheory

namespace HunterPDE.Harmonic

/-- The average of `u` over the sphere `∂B_r(x) = {y : |y - x| = r}` with respect to surface
measure (Hunter, *Notes on PDEs*, Eq. (1.3)):
`⨍_{∂B_r(x)} u dS = (1 / (n αₙ r^{n-1})) ∫_{∂B_r(x)} u dS`.
It is written, via polar coordinates, as the normalized integral of `y ↦ u (x + r • y)` over the
unit sphere against Mathlib's surface measure `volume.toSphere` (whose total mass is
`n · vol(B₁(0)) = n αₙ`, the area of the unit sphere); the factor `r^{n-1}` cancels in the
average. -/
noncomputable def sphereAverage {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  ⨍ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x + r • y.1) ∂(volume.toSphere)

/-- The mean-value property (2.3) of Hunter, *Notes on PDEs*, p. 20: for every ball whose closure
lies in `Ω` (`B_r(x) ⋐ Ω`, `r > 0`), the value of `u` at the centre equals both its average over
the ball `B_r(x)` and its average over the sphere `∂B_r(x)`. -/
def HasMeanValueProperty {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → Metric.closedBall x r ⊆ Ω →
    u x = (⨍ y in Metric.ball x r, u y) ∧ u x = sphereAverage u x r

end HunterPDE.Harmonic


