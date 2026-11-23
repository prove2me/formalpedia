-- Prove2me | Definitions.Def_NoHair_staticInvertedEndMetric
-- name    : NoHair_staticInvertedEndMetric
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T10:52:20.254235+00:00
-- url     : https://prove2.me/theorems/c660d64b-ec54-466f-ad73-a96afa08ab53
-- title:
--   Negative conformal sheet in inverted coordinates and its lapse monopole
-- statement:
--   Pull back the physical negative-sheet metric by unit Euclidean inversion. The first-order lapse coefficient is the limit of r(1−N) at infinity. A continuous pole of parameter μ means that all inverted coefficients tend to (μ/2)⁴δ at the puncture.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154. https://doi.org/10.1007/BF00770326. Here the negative sheet uses unit Euclidean inversion and the coefficient of the inverse-radius term of the lapse.

import Definitions.Def_NoHair_staticConformalCompletion
import Mathlib.Geometry.Euclidean.Inversion.Calculus

noncomputable section

open Filter Set
open scoped Topology

namespace NoHair

/-- The metric on the negative conformal sheet pulled back by unit Euclidean inversion. -/
def staticInvertedNegativeMetric (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (y : ADMPoint) (i j : Fin 3) : ℝ :=
  let I := EuclideanGeometry.inversion (0:ADMPoint) 1
  let w := fun k : Fin 3 => fderiv ℝ I y (EuclideanSpace.single k 1)
  ∑ a : Fin 3, ∑ b : Fin 3, staticPositiveMetric (fun z => -N z) h (I y) a b *
    w i a * w j b

/-- The coefficient of 1/r in the lapse defect as spatial infinity is approached in every direction. -/
def HasStaticLapseMonopole (N : ADMPoint → ℝ) (μ : ℝ) : Prop :=
  Tendsto (fun z : ADMPoint => ‖z‖*(1-N z)) (cocompact ADMPoint) (𝓝 μ)

/-- The punctured inverted metric has a continuous extension with the stated Euclidean value. -/
def HasContinuousStaticPole (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (μ : ℝ) : Prop :=
  ∀ i j : Fin 3, Tendsto (fun y => staticInvertedNegativeMetric N h y i j) (𝓝[≠] (0:ADMPoint))
    (𝓝 ((μ/2)^4 * (1:Matrix (Fin 3) (Fin 3) ℝ) i j))

end NoHair


