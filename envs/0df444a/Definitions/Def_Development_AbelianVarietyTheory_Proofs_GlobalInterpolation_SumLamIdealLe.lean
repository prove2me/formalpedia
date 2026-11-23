-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:11.229802+00:00
-- url     : https://prove2.me/theorems/3e94c879-113b-4272-aad1-9aa6833cea56
-- title:
--   Sum Lam Ideal Le
-- statement:
--   Definitions and structural lemmas for Sum Lam Ideal Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
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
namespace GlobalTheory.Hk.LamRay
variable {K : Type} [Field K] [NumberField K]
end GlobalTheory.Hk.LamRay


