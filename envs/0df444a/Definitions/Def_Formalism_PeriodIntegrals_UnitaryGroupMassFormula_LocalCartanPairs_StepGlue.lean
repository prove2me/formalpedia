-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_StepGlue
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_StepGlue
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:31.319251+00:00
-- url     : https://prove2.me/theorems/6882d779-6d2e-4a42-b2d6-8c0dd4da4a45
-- title:
--   Step Glue
-- statement:
--   Definitions and structural lemmas for Step Glue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/StepGlue.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.SqPair.LCP
section Lin
variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι]
end Lin
end PI.SqPair.LCP


