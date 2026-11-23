-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:20.01398+00:00
-- url     : https://prove2.me/theorems/453787b1-99f6-493a-b3e5-56c9e69650ee
-- title:
--   Finrank Eq Two
-- statement:
--   Definitions and structural lemmas for Finrank Eq Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDegreeEquality/FinrankEqTwo.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace CMDeg
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
def sigma (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : E ≃ₐ[F] E :=
  AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => by simpa using hfix x)
end CMDeg


