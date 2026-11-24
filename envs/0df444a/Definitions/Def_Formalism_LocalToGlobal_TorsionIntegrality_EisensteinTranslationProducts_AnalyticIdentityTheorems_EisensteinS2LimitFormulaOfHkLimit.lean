-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:06.532264+00:00
-- url     : https://prove2.me/theorems/457c9856-511e-4658-809f-3c7b18451ac1
-- title:
--   Eisenstein S2 Limit Formula Of Hk Limit
-- statement:
--   Definitions and structural lemmas for Eisenstein S2 Limit Formula Of Hk Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EisensteinS2LimitFormulaOfHkLimit.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter Topology
namespace Formalism.L2.Th1.F
namespace Hk4
def cellOff (τ : ℂ) (s : ℝ) (p : ℤ × ℤ) : ℂ := if p.2 = 0 then 0 else hkCell τ s p
end Hk4
namespace Hk4
end Hk4
end Formalism.L2.Th1.F


