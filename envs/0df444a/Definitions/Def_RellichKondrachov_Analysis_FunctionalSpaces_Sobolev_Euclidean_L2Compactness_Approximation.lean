-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:29.704859+00:00
-- url     : https://prove2.me/theorems/1ee4be1d-f3ae-4722-94b7-2b8c13953e65
-- title:
--   Approximation
-- statement:
--   Definitions and structural lemmas for Approximation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance instMeasurableSpaceApproximation : MeasurableSpace E := borel E
local instance instBorelSpaceApproximation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceApproximation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddApproximation : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegApproximation : MeasurableNeg E := by
  infer_instance
attribute [local instance] instMeasurableSpaceApproximation instBorelSpaceApproximation instOpensMeasurableSpaceApproximation instMeasurableAddApproximation instMeasurableNegApproximation
variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)
noncomputable def kernelMeasure : Measure E :=
  (volume : Measure E).withDensity fun x => ENNReal.ofReal (ψ x)
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


