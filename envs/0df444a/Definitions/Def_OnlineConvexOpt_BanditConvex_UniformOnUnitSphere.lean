-- Prove2me | Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere
-- name    : OnlineConvexOpt_BanditConvex_UniformOnUnitSphere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:38:33.721025+00:00
-- url     : https://prove2.me/theorems/bd5823f1-b8c9-44c9-833f-836941ad007a
-- title:
--   Uniform distribution on the unit sphere (u ∼ S)
-- statement:
--   Lemma 6.7 and Algorithm 23 draw a unit vector $u \sim S$ uniformly from the Euclidean unit
--   sphere $S = \{u \mid \|u\| = 1\}$. `IsUniformOnUnitSphere Prob U` formalizes this
--   operationally: `U` lies on the sphere almost surely, and its law is invariant under every
--   orthogonal (linear isometric) transformation of the ambient space — the property that
--   pins down the unique rotation-invariant probability measure on the sphere (the normalized
--   surface measure the book calls $S$), by uniqueness of Haar measure on the orthogonal
--   group's homogeneous space.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 110, PDF p. 132 ("u ∼ S", Lemma 6.7 and Algorithm 23)

import Mathlib

namespace OnlineConvexOpt.BanditConvex

open MeasureTheory

/-- `U` is uniformly distributed on the Euclidean unit sphere `S = {u | ‖u‖ = 1}` in
`EuclideanSpace ℝ (Fin n)` (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 110, PDF p. 132, `u ∼ S` in Lemma 6.7 and Algorithm 23), operationally
characterized, as in the sphere-sampling conventions elsewhere in this workspace, by: `U` lies on
the sphere almost surely, and the law of `U` is invariant under every orthogonal (linear
isometric) transformation of `EuclideanSpace ℝ (Fin n)` — the property that pins down the unique
rotation-invariant probability measure on the sphere, the normalized surface measure the book
calls `S`. -/
def IsUniformOnUnitSphere {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω) {n : ℕ}
    (U : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ᵐ ω ∂Prob, U ω ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
  (∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
    Measure.map (fun ω => L (U ω)) Prob = Measure.map U Prob)

end OnlineConvexOpt.BanditConvex


