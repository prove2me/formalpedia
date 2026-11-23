-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
-- name    : GroundTheory_GlobalFields_TateThesis_Gaussian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:04.481818+00:00
-- url     : https://prove2.me/theorems/8626eead-d5e3-4cb5-906e-3b17c4729faf
-- title:
--   Gaussian
-- statement:
--   Definitions and structural lemmas for Gaussian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Gaussian.lean

import Mathlib
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
open Complex MeasureTheory Set Real
open scoped FourierTransform
noncomputable section
def realGaussian (x : ℝ) : ℂ := Complex.exp (-π * (x : ℂ) ^ 2)
def realGaussianOdd (x : ℝ) : ℂ := (x : ℂ) * Complex.exp (-π * (x : ℂ) ^ 2)
end
end GroundTheory.Global


