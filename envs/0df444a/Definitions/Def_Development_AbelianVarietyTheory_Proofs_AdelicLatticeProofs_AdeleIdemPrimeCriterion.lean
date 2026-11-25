-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdeleIdemPrimeCriterion
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdeleIdemPrimeCriterion
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:21.106036+00:00
-- url     : https://prove2.me/theorems/0a945f59-0f5f-419b-baf5-22f0c8c2cea5
-- title:
--   Adele Idem Prime Criterion
-- statement:
--   Definitions and structural lemmas for Adele Idem Prime Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdeleIdemPrimeCriterion.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory
end GlobalTheory


