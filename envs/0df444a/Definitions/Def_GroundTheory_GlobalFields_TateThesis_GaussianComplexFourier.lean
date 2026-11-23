-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
-- name    : GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:04.058853+00:00
-- url     : https://prove2.me/theorems/42990a72-9cf3-499b-95ed-138b7081d127
-- title:
--   Gaussian Complex Fourier
-- statement:
--   Definitions and structural lemmas for Gaussian Complex Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
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
open scoped FourierTransform
noncomputable section
end
end GroundTheory.Global


