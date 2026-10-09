-- Prove2me | Definitions.Def_SphereSOS_Rate_SphereMeasure
-- name    : SphereSOS_Rate_SphereMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:36.366326+00:00
-- url     : https://prove2.me/theorems/36d6c096-d424-44c5-a019-12cb243b44a5
-- title:
--   §2, p. 5 — the rotation-invariant probability measure $\sigma$ on $S^{d-1}$
-- statement:
--   Let $\sigma$ be the **rotation-invariant probability measure** on the unit sphere $S^{d-1}\subset\mathbb R^d$, i.e. normalized surface measure: for a Borel set $A\subseteq S^{d-1}$, $\sigma(A)$ is the volume of the cone $\{tx:\ 0<t\le1,\ x\in A\}$ divided by the volume of the unit ball. It is the measure behind the $L^2$ inner product $\langle f,g\rangle=\int fg\,d\sigma$ on the sphere and behind the integral transforms $(Kf)(x)=\int_{S^{d-1}}K(x,y)f(y)\,d\sigma(y)$.
--
--   **Formalization Note** The measure is built from Mathlib's `Measure.toSphere` of Lebesgue measure on `EuclideanSpace ℝ (Fin d)`, transported to coordinate vectors `Fin d → ℝ` and divided by its total mass, so it is a measure on $\mathbb R^d$ concentrated on $S^{d-1}$ with total mass $1$ for $d\ge1$. For $d=0$ it is the zero measure.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 5, §2 ('dσ is the rotation-invariant probability measure on the sphere')

import Mathlib

namespace SphereSOS.Rate

open MeasureTheory

/-- The rotation-invariant probability measure `σ` on the Euclidean unit sphere `S^{d-1}`,
as a measure on `ℝ^d = Fin d → ℝ`: Mathlib's surface measure on the unit sphere of
`EuclideanSpace ℝ (Fin d)`, transported to coordinate vectors and normalized to total mass one. -/
noncomputable def sigma (d : ℕ) : Measure (Fin d → ℝ) :=
  let μ : Measure (Fin d → ℝ) :=
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).map
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        WithLp.equiv 2 (Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)))
  (μ Set.univ)⁻¹ • μ

end SphereSOS.Rate


