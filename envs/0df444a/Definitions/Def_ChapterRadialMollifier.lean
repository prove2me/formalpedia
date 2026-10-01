-- Prove2me | Definitions.Def_ChapterRadialMollifier
-- name    : ChapterRadialMollifier
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:43:45.464696+00:00
-- url     : https://prove2.me/theorems/fca45d1a-e6c7-4f6f-86a6-7e6f71bf488e
-- title:
--   Chapter RadialMollifier
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterRadialMollifier.lean`): generated def bundle for ChapterRadialMollifier. See BookProof/ChapterRadialMollifier.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterRadialMollifier.lean

import Mathlib


/-!
# A radial smooth mollifier on `ℂ`, and the disc mean-value property

This file provides the analytic tool needed by
`BookProof/ChapterWeylCauchyRiemann.lean` — the distributional
("weak Cauchy–Riemann") version of the *Holomorphic fields* remark of `book.tex`
(line ~4105).

Mathlib's `ContDiffBump` family is only known to be *even*, not *radial*
(the abstract `ContDiffBumpBase` interface records `toFun R (-x) = toFun R x`
and nothing more), and radiality is exactly what makes a mollifier reproduce
holomorphic functions.  So we build an explicit radial mollifier on `ℂ` out of
Mathlib's `expNegInvGlue`:

* `radialBump z = expNegInvGlue (1 - ‖z‖²)` — smooth, nonnegative, supported in
  the open unit ball, and depending on `z` only through `‖z‖`;
* `moll δ` — its `L¹`-normalized rescaling, supported in `ball 0 δ` with
  `∫ moll δ = 1`.

The payoff is `integral_moll_eq_self_of_analytic`: convolving a function
holomorphic on an open set with `moll δ` reproduces the function at every point
whose closed `δ`-ball is contained in that set.  This is the disc form of the
mean value property, obtained from Mathlib's circle mean value property
(`circleAverage_of_differentiable_on_off_countable`) by integration in polar
coordinates.
-/

namespace BookProof.RadialMollifier

open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

/-- The raw radial bump on `ℂ`: `z ↦ expNegInvGlue (1 - ‖z‖²)`.  It is smooth,
nonnegative, supported exactly in the open unit ball, and radial. -/
def radialBump (z : ℂ) : ℝ := expNegInvGlue (1 - Complex.normSq z)





















/-- The total mass of the raw bump. -/
def radialMass : ℝ := ∫ z : ℂ, radialBump z



/-- The normalized radial mollifier of width `δ`: smooth, nonnegative, supported
in `ball 0 δ`, of total integral one, and radial. -/
def moll (δ : ℝ) (z : ℂ) : ℝ := radialBump (δ⁻¹ • z) / (radialMass * δ ^ 2)

































end

end BookProof.RadialMollifier


