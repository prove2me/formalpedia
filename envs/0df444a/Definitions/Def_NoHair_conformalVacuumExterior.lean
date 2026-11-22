-- Prove2me | Definitions.Def_NoHair_conformalVacuumExterior
-- name    : NoHair_conformalVacuumExterior
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T22:24:52.838895+00:00
-- url     : https://prove2.me/theorems/7605b057-97c2-459f-842b-0d194c32a853
-- title:
--   Static vacuum exterior in Euclidean conformal coordinates
-- statement:
--   Let $U$ be a function of a point $x$ of Euclidean three-space. On the physical side of a conformal double, $x\ne 0$ and $U(x)<2$. The static lapse is $N=2/U-1$ and the spatial metric is $U^4$ times the Euclidean metric. A realization identifies this entire coordinate domain with the spacetime exterior and pulls the metric back to $-N^2dt^2+U^4(dx_1^2+dx_2^2+dx_3^2)$. The definition permits angular dependence in $U$.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987), pp. 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_spacetime

noncomputable section
open scoped ContDiff Manifold
open Set

namespace NoHair

/-- The spatial vector of a point in a Cartesian spacetime chart. -/
def conformalSpatialPoint (y : E4) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![y 1, y 2, y 3]

/-- The positive-lapse side of a punctured conformal double, where \(N=2/U-1\). -/
def conformalExteriorDomain (U : EuclideanSpace ℝ (Fin 3) → ℝ) : Set E4 :=
  {y | conformalSpatialPoint y ≠ 0 ∧ U (conformalSpatialPoint y) < 2}

/-- The static metric in Euclidean conformal coordinates, with factor \(u\). -/
def conformalStaticForm (u : ℝ) (v w : E4) : ℝ :=
  -(2 / u - 1) ^ 2 * v 0 * w 0 + u ^ 4 * (v 1 * w 1 + v 2 * w 2 + v 3 * w 3)

/-- A global realization of the physical exterior by the positive-lapse part of the double. -/
def HasConformalVacuumExterior {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (D : Set M)
    (U : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  IsOpen D ∧ ∃ ψ : E4 → M, IsDiffeoOnto ψ (conformalExteriorDomain U) D ∧
    ∀ z ∈ conformalExteriorDomain U, ∀ v w : E4,
      g (ψ z) (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) ψ z v)
        (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) ψ z w) =
        conformalStaticForm (U (conformalSpatialPoint z)) v w

end NoHair


