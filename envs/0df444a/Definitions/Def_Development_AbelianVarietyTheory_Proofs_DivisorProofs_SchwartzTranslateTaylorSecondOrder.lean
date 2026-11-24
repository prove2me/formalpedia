-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:34.333833+00:00
-- url     : https://prove2.me/theorems/d2ef4cba-3c3d-4e28-96d4-5ae495ddd52b
-- title:
--   Schwartz Translate Taylor Second Order
-- statement:
--   Definitions and structural lemmas for Schwartz Translate Taylor Second Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslateTaylorSecondOrder.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
namespace GlobalTheory.SchwartzTranslateUnif
open GlobalTheory.SchwartzTranslate
end GlobalTheory.SchwartzTranslateUnif


