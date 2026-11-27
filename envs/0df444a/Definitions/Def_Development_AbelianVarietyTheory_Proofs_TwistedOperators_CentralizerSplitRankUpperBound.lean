-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralizerSplitRankUpperBound
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralizerSplitRankUpperBound
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:30:55.429127+00:00
-- url     : https://prove2.me/theorems/34052c7f-ac03-4db3-a3cd-ddbd0936d9f9
-- title:
--   Centralizer Split Rank Upper Bound
-- statement:
--   Definitions and structural lemmas for Centralizer Split Rank Upper Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CentralizerSplitRankUpperBound.lean

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
open GlobalTheory.RegSS
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
namespace GlobalTheory.RegSS.SplitRankBound
end GlobalTheory.RegSS.SplitRankBound


