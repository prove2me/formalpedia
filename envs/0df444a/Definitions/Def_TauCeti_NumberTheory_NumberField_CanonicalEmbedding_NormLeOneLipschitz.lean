-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_NormLeOneLipschitz
-- name    : TauCeti_NumberTheory_NumberField_CanonicalEmbedding_NormLeOneLipschitz
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:48:20.186042+00:00
-- url     : https://prove2.me/theorems/1da276de-516e-41d1-8228-1b0da956c110
-- title:
--   A Lipschitz parametrization of the frontier of the norm-≤-one region
-- statement:
--   The mixed embedding of a number field is parametrized using logarithmic absolute values, signs at real places, and angles at complex places. This bundle defines the face maps and lifts used to cover the boundary of the norm-at-most-one fundamental-cone region. These maps provide the geometric data for Lipschitz parametrizations.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/NormLeOneLipschitz.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/NormLeOneLipschitz.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A Lipschitz parametrization of the frontier of the norm-≤-one region

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error, but only for regions whose frontier is Lipschitz
parametrizable: `exists_abs_ncard_smul_inter_vadd_sub_le` takes
`IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)` as a hypothesis. Mathlib proves that
`frontier (normLeOne K)` is *null* (`volume_frontier_normLeOne`), which is what a rate-free limit
needs and is strictly weaker: a null frontier does not provide a quantitative or power-saving
error bound.

This file discharges that hypothesis for `normLeOne K`. Mathlib presents the region through
`expMapBasis`, a partial homeomorphism of `realSpace K` whose image of the box
`paramSet K = univ.pi fun w ↦ if w = w₀ then Iic 0 else Ico 0 1` is the norm-≤-one region up to
`normAtAllPlaces`. The frontier of a box is the union of its faces, so a Lipschitz cover of the
image reduces to parametrizing the image of each face — which is what the maps here do.

The `w₀` face is where the unbounded `Iic 0` direction is pinned at its endpoint; the side faces
pin one of the bounded `Ico 0 1` directions, and there the substitution `t = exp (x w₀)` turns the
unbounded direction into the freed cube coordinate.

## Main results

* `isLipschitzParametrizable_frontier_normLeOne`: the frontier of `normLeOne K` is Lipschitz
  parametrizable in dimension `finrank ℝ (mixedSpace K) - 1`, one less than that of the mixed
  space.
* `frontier_normLeOne_subset_preimage`: that frontier lies over the frontier of the box image,
  through `normAtAllPlaces`.
* `isLipschitzParametrizable_frontier_image_paramSet`: the frontier of the box image is Lipschitz
  parametrizable in dimension `rank K`, one less than that of `realSpace K`.
* `contDiff_expMapBasis`: the box parametrization is smooth.
* `closure_image_paramSet_subset`: the closure of the box image adds only the origin.
* `frontier_image_paramSet_subset`: the frontier of the box image lies in the image of the box's
  frontier, together with the origin.

The face maps that decompose the box's frontier, the lifts that cover the fibres of
`normAtAllPlaces`, and the lemmas supporting them, are `private`: they implement the
parametrization and are not independently reusable.

## References

* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`, from which the face
  decomposition is adapted: `faceMapZero`, `faceMapSide`, `contDiff_faceMapZero`,
  `contDiff_faceMapSide`, `frontier_image_subset_of_closure_subset` and
  `frontier_image_paramSet_subset` follow that file's declarations of the same names.
  `isLipschitzParametrizable_frontier_normLeOne` is that file's
  `normLeOne_frontier_lipschitz_cover`, and the circle direction of `liftMap` follows its
  `lipschitzWith_exp_ofReal_mul_I`; the sign and angle bookkeeping is arranged differently here,
  through a single globally `C¹` lift rather than that file's `cubeRelabel` scaffolding.
-/

 section

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem
open scoped NumberField

namespace NumberField.mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]



open scoped Classical in
/-- The face of `paramSet K` on which the unbounded `w₀` coordinate sits at its finite endpoint
`0`, parametrized by the remaining coordinates. -/
 noncomputable def faceMapZero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩

open scoped Classical in
/-- The face of `paramSet K` on which the bounded coordinate `i` sits at the endpoint `a`,
parametrized by the remaining coordinates together with `t = exp (x w₀) ∈ (0, 1]` in the slot
that pinning `i` frees. -/
 noncomputable def faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  c i • expMapBasis fun w ↦ if hw : w = w₀ then 0 else
    if (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀}) = i then a else c ⟨w, hw⟩









variable {K}





variable (K)









/-- The lift of a point of `realSpace K` to the mixed space, given a choice of sign `s w` at each
real place and of angle at each complex place. The angles range over the unit cube and are
rescaled to `[-π, π]`, so that `liftMap` inverts `normAtAllPlaces` on the nose: every `x` is
`liftMap K s (normAtAllPlaces x, θ)` for the sign vector recording the signs of `x` at the real
places and the `θ` recording its arguments at the complex ones.

This is not `(polarSpaceCoord K).symm`: that inverts a partial homeomorphism, so it is available
only for positive radii and angles in the open interval `(-π, π)`, and it keeps the signed value
at a real place instead of its norm. The cover below needs a map defined — and `C¹` — on the whole
closed cube, and needs the real places to carry a separate choice of sign. -/
 noncomputable def liftMap (s : {w : InfinitePlace K // IsReal w} → Bool)
    (p : realSpace K × ({w : InfinitePlace K // IsComplex w} → ℝ)) : mixedSpace K :=
  (fun w ↦ (if s w then 1 else -1) * p.1 w.1,
    fun w ↦ p.1 w.1 • Complex.exp ((2 * Real.pi * p.2 w - Real.pi) • Complex.I))







end NumberField.mixedEmbedding.fundamentalCone

end
end


