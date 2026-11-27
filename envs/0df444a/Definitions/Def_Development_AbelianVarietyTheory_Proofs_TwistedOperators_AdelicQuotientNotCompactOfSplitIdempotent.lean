-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AdelicQuotientNotCompactOfSplitIdempotent
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_AdelicQuotientNotCompactOfSplitIdempotent
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:29:12.773792+00:00
-- url     : https://prove2.me/theorems/97b5ef76-1504-4945-a200-b8efae8a253c
-- title:
--   Adelic Quotient Not Compact Of Split Idempotent
-- statement:
--   Definitions and structural lemmas for Adelic Quotient Not Compact Of Split Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AdelicQuotientNotCompactOfSplitIdempotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.RegSS
end GlobalTheory.RegSS


