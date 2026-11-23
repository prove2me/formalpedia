-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
-- name    : GroundTheory_GlobalFields_TateThesis_GaussianComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:30.904798+00:00
-- url     : https://prove2.me/theorems/2c6141b5-a80b-446e-b3b3-458b5ae94e34
-- title:
--   Gaussian Complex
-- statement:
--   Definitions and structural lemmas for Gaussian Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal
noncomputable section
def traceFormℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp (ContinuousLinearMap.mul ℝ ℂ)
def complexPlaceMeasure : Measure ℂ := (2 : ℝ≥0∞) • volume
def complexFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z, 𝐞 (-(2 * (z * w).re)) • f z ∂complexPlaceMeasure
def complexGaussian (m : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ m then z ^ m.natAbs else conj z ^ m.natAbs) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)
end
end GroundTheory.Global


