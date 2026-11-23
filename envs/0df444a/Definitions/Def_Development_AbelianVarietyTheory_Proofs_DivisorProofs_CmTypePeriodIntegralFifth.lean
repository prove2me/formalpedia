-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifth
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:54.211568+00:00
-- url     : https://prove2.me/theorems/9c3d9cfe-16ee-4983-8259-0e7797b43897
-- title:
--   Cm Type Period Integral Fifth
-- statement:
--   Definitions and structural lemmas for Cm Type Period Integral Fifth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFifth.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
namespace GlobalTheory.EigenPair
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.EigenPair


