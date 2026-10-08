-- Prove2me | Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2
-- name    : OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:41.391074+00:00
-- url     : https://prove2.me/theorems/801509c1-8b5f-422b-aaf6-88735a640555
-- title:
--   Uniform distribution on the unit sphere (measurable, a.s. on the sphere, rotation invariant)
-- statement:
--   A random vector $U$ is uniformly distributed on the unit sphere of $\mathbb R^n$ if it is measurable, lies on the sphere almost surely, and its law is invariant under every linear isometry of $\mathbb R^n$ — the characterization of the normalized surface measure. Corrected version of `OnlineConvexOpt_BanditConvex_UniformOnUnitSphere`: measurability is required explicitly, since for a non-measurable $U$ Mathlib's `Measure.map U Prob` is the zero measure and the invariance clause held vacuously without pinning down any law.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 110 (u ∼ S, Lemma 6.7 and Algorithm 23) (PDF p. 132)

import Mathlib

namespace OnlineConvexOpt.BanditConvex

open MeasureTheory

/-- `U` is uniformly distributed on the Euclidean unit sphere `S = {u | ‖u‖ = 1}` in
`EuclideanSpace ℝ (Fin n)` (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 110, PDF p. 132, `u ∼ S` in Lemma 6.7 and Algorithm 23), operationally
characterized by: `U` is a random variable (measurable), `U` lies on the sphere almost surely,
and the law of `U` is invariant under every orthogonal (linear isometric) transformation of
`EuclideanSpace ℝ (Fin n)` — the property that pins down the unique rotation-invariant
probability measure on the sphere, the normalized surface measure the book calls `S`.
Measurability is required explicitly (it was missing from the retired version): for a
non-measurable `U` Mathlib's `Measure.map U Prob` is the zero measure, so the invariance clause
would hold vacuously and pin down no law at all. -/
def IsUniformOnUnitSphere {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω) {n : ℕ}
    (U : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  Measurable U ∧
  (∀ᵐ ω ∂Prob, U ω ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
  (∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
    Measure.map (fun ω => L (U ω)) Prob = Measure.map U Prob)

end OnlineConvexOpt.BanditConvex


