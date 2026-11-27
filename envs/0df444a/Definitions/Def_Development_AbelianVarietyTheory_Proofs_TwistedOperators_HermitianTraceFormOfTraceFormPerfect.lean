-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermitianTraceFormOfTraceFormPerfect
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermitianTraceFormOfTraceFormPerfect
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:31:16.900319+00:00
-- url     : https://prove2.me/theorems/580e3638-02ac-40d8-b53b-9390457ae38e
-- title:
--   Hermitian Trace Form Of Trace Form Perfect
-- statement:
--   Definitions and structural lemmas for Hermitian Trace Form Of Trace Form Perfect, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HermitianTraceFormOfTraceFormPerfect.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
namespace GlobalTheory.RegSS
section
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
end
end GlobalTheory.RegSS


