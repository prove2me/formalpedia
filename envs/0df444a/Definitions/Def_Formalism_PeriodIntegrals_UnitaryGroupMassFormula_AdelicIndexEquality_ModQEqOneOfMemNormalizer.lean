-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:57.25905+00:00
-- url     : https://prove2.me/theorems/2c9cd8f7-20e6-4941-9970-88ec1021e628
-- title:
--   Mod QEq One Of Mem Normalizer
-- statement:
--   Definitions and structural lemmas for Mod QEq One Of Mem Normalizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
section Delta
variable {G : Type} [Group G]
def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / (A.relIndex B : ℚ)
end Delta
end PI.UnitaryGroupMassFormula.AdIndexEq


