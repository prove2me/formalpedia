-- Prove2me | Definitions.Def_RegretBandits_Nonlinear_Smoothing
-- name    : RegretBandits_Nonlinear_Smoothing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:21:44.382676+00:00
-- url     : https://prove2.me/theorems/dc158401-b30a-4f42-92ce-d423c0222192
-- title:
--   Spherical measure, uniform laws on the unit ball and sphere, and the smoothed loss (Ch. 6)
-- statement:
--   This file fixes the geometric and probabilistic objects of Chapter 6 on $\mathbb R^d$ with the Euclidean norm. Let $\mathbb B=\{x\in\mathbb R^d:\|x\|\le 1\}$ be the closed unit ball and $\mathbb S=\{x\in\mathbb R^d:\|x\|=1\}$ the unit sphere.
--
--   1. The **unnormalized spherical measure** $\sigma$ is the surface measure on $\mathbb S$: for a measurable $A\subseteq\mathbb S$,
--   $$\sigma(A)=d\cdot \mathrm{Vol}\big(\{ta: 0<t<1,\ a\in A\}\big).$$
--   Its total mass is $\sigma(\mathbb S)=d\,\mathrm{Vol}(\mathbb B)$, and for $d=1$ it is the counting measure on $\{-1,+1\}$.
--   2. The **uniform distribution on $\mathbb S$** is $\sigma/\sigma(\mathbb S)$.
--   3. The **uniform distribution on $\mathbb B$** is Lebesgue measure restricted to $\mathbb B$ divided by $\mathrm{Vol}(\mathbb B)$.
--   4. For $\delta>0$ and a loss $\ell:\mathbb R^d\to\mathbb R$, the **smoothed loss** is
--   $$\widetilde\ell(x)=\mathbb E\,\ell(x+\delta B),\qquad B\ \text{uniform on }\mathbb B .$$
--
--   These objects are used by every statement of the mission: the one-point and two-point gradient estimates are unbiased estimates of $\nabla\widetilde\ell$, and $\widetilde\ell$ is within $\delta G$ of a $G$-Lipschitz $\ell$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. $\sigma$ is Mathlib's `Measure.toSphere` of Lebesgue measure, pushed forward to $\mathbb R^d$ along the inclusion of the sphere. For $d=0$ the sphere is empty and the uniform law on it is the zero measure; every theorem of the mission assumes $d\ge 1$ where this matters.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 90-92, Section 6.1 (definitions of B, S, sigma in Lemma 6.1, uniform B and S in Lemma 6.2, smoothed loss on p. 92)

import Mathlib

open MeasureTheory

namespace RegretBandits.Nonlinear

/-- The unnormalized spherical (surface) measure `σ` on the unit sphere
`𝕊 = {x ∈ ℝ^d : ‖x‖ = 1}` (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 90, Lemma 6.1), viewed as
a measure on `ℝ^d` concentrated on `𝕊`. It is Mathlib's `Measure.toSphere` of Lebesgue measure,
`σ(A) = d · Vol({t a : 0 < t < 1, a ∈ A})`, pushed forward along the inclusion `𝕊 → ℝ^d`. Its total
mass is `σ(𝕊) = d · Vol(𝔹)` (p. 92); for `d = 1` it is the counting measure on `{-1, +1}`. -/
noncomputable def sphereMeasure (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).map Subtype.val

/-- The uniform distribution on the unit sphere `𝕊` of `ℝ^d` (p. 90): `σ` normalized to total
mass one. It is a probability measure for `d ≥ 1` (for `d = 0` the sphere is empty and this is the
zero measure). -/
noncomputable def uniformSphere (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (sphereMeasure d Set.univ)⁻¹ • sphereMeasure d

/-- The uniform distribution on the closed unit ball `𝔹 = {x ∈ ℝ^d : ‖x‖ ≤ 1}` (p. 91, Lemma 6.2):
Lebesgue measure restricted to `𝔹`, normalized by `Vol(𝔹)`. -/
noncomputable def uniformBall (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1))⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)

/-- The smoothed loss `ℓ̃(x) = E ℓ(x + δB)` with `B` uniform on the unit ball `𝔹` (p. 92). -/
noncomputable def smoothedLoss (d : ℕ) (δ : ℝ) (ℓ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ b, ℓ (x + δ • b) ∂(uniformBall d)

end RegretBandits.Nonlinear


