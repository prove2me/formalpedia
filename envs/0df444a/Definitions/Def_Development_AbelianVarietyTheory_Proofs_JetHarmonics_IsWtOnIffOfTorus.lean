-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:53.850186+00:00
-- url     : https://prove2.me/theorems/d6e7e347-58e9-4de0-956a-9fe7059cc398
-- title:
--   Is Wt On Iff Of Torus
-- statement:
--   Definitions and structural lemmas for Is Wt On Iff Of Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end Rep
end GlobalTheory.KTypeCompare


