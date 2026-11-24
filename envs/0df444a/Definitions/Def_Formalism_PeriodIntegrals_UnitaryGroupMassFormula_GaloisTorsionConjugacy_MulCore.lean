-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulCore
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulCore
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:14.714587+00:00
-- url     : https://prove2.me/theorems/72b11216-5db8-40b3-bf90-04261a8c1be0
-- title:
--   Mul Core
-- statement:
--   Definitions and structural lemmas for Mul Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulCore.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeierstrassUniformization_PairIsLat
import Theorems.Thm_Formalism_L2_Th1_F_EtaEis_core
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GalTorsConj.W
open PI.GalTorsConj Formalism.L2.Th1.F
section core
variable {L L' : PeriodPair} {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}
end core
end PI.GalTorsConj.W
end


