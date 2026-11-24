-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_SqPairGlueMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_SqPairGlueMain
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:10:04.829721+00:00
-- url     : https://prove2.me/theorems/63cb1473-b94c-492b-b402-83c40e45a29f
-- title:
--   Sq Pair Glue Main
-- statement:
--   Definitions and structural lemmas for Sq Pair Glue Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/SqPairGlueMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
end PI.SqPairW


