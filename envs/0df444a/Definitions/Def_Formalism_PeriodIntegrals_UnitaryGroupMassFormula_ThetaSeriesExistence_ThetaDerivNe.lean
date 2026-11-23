-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:08.610748+00:00
-- url     : https://prove2.me/theorems/0a2c546a-f0fe-4e03-93c6-1910683612cd
-- title:
--   Theta Deriv Ne
-- statement:
--   Definitions and structural lemmas for Theta Deriv Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaDerivNe.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
import Definitions.Def_Formalism_PeriodIntegrals_SigmaStarEx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
namespace PI.SSE
def th (τ u : ℂ) : ℂ := cexp (Real.pi * I * u) * jacobiTheta₂ (u + (1 / 2 + τ / 2)) τ
def ThetaDerivNe : Prop :=
  ∀ τ : ℂ, 0 < τ.im → 3 ≤ 4 * τ.im ^ 2 → jacobiTheta₂' (1 / 2 + τ / 2) τ ≠ 0
def ReduceBasis : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∃ v₁ v₂ : ℂ, v₁ ≠ 0 ∧
    PI.lat2 v₁ v₂ = PI.lat2 w₁ w₂ ∧ 0 < (v₂ / v₁).im ∧ 3 ≤ 4 * (v₂ / v₁).im ^ 2
end PI.SSE
end


