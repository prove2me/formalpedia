-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNhdsFixOfContinuousCoefficients
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNhdsFixOfContinuousCoefficients
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:31.233665+00:00
-- url     : https://prove2.me/theorems/fd992f8d-8339-4156-8748-c91c0b84c66d
-- title:
--   Exists Nhds Fix Of Continuous Coefficients
-- statement:
--   Definitions and structural lemmas for Exists Nhds Fix Of Continuous Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNhdsFixOfContinuousCoefficients.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
namespace GlobalTheory.SmoothFix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end GlobalTheory.SmoothFix


