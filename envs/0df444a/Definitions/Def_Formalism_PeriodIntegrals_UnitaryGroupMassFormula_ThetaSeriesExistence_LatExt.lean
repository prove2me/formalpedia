-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:45.020263+00:00
-- url     : https://prove2.me/theorems/ee76d1f5-6275-4564-8cc8-08dd57ec189e
-- title:
--   Lat Ext
-- statement:
--   Definitions and structural lemmas for Lat Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/LatExt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
namespace PI.SSE
def Rel (G : ℂ → ℂ) (A v₁ v₂ : ℂ) (m n : ℤ) : Prop :=
  ∀ z, G (z + (m * v₁ + n * v₂)) = (-1 : ℂ) ^ (m + n + m * n) * (qf A (m * v₁ + n * v₂) z * G z)
end PI.SSE
end


