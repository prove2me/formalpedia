-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteIdealsIn
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteIdealsIn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:07.534452+00:00
-- url     : https://prove2.me/theorems/8ee0facf-5d6e-476f-a93f-4be2f7ca3117
-- title:
--   Finite Ideals In
-- statement:
--   Definitions and structural lemmas for Finite Ideals In, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteIdealsIn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
namespace GlobalTheory.Hk.RayConv
variable {K : Type} [Field K] [NumberField K]
variable {M : ℕ} (D : RayData K M)
end GlobalTheory.Hk.RayConv
namespace GlobalTheory.Hk
end GlobalTheory.Hk


