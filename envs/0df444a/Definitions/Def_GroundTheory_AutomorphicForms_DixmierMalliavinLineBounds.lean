-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:11.831696+00:00
-- url     : https://prove2.me/theorems/85410360-3bc9-4fa9-9526-e76c44ed0a06
-- title:
--   Dixmier Malliavin Line Bounds
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Line Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
namespace LineKernel
section Bounds
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
end Bounds
end LineKernel
end
end GroundTheory.Automorphic


