-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FreeGeneratorTopForm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FreeGeneratorTopForm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:24.507902+00:00
-- url     : https://prove2.me/theorems/4201fa49-965e-40f2-adc6-2ca5540e7041
-- title:
--   Free Generator Top Form
-- statement:
--   Definitions and structural lemmas for Free Generator Top Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FreeGeneratorTopForm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TopForm
namespace GlobalTheory
open KaehlerDifferential IsLocalRing Module
end GlobalTheory


