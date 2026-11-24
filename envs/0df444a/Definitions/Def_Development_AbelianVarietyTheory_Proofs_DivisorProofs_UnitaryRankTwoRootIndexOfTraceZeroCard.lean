-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCard
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCard
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:56.956178+00:00
-- url     : https://prove2.me/theorems/766ce077-e49c-4a7e-8a7a-98045fee1ac5
-- title:
--   Unitary Rank Two Root Index Of Trace Zero Card
-- statement:
--   Definitions and structural lemmas for Unitary Rank Two Root Index Of Trace Zero Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankTwoRootIndexOfTraceZeroCard.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
end
end GlobalTheory.SatakeWeyl


