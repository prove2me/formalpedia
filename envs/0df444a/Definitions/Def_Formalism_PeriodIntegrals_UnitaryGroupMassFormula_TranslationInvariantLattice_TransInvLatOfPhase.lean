-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TranslationInvariantLattice_TransInvLatOfPhase
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TranslationInvariantLattice_TransInvLatOfPhase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:54.784843+00:00
-- url     : https://prove2.me/theorems/702678ca-833a-476c-b65e-7f1d2c35c98d
-- title:
--   Trans Inv Lat Of Phase
-- statement:
--   Definitions and structural lemmas for Trans Inv Lat Of Phase, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TranslationInvariantLattice/TransInvLatOfPhase.lean

import Definitions.Def_Formalism_PeriodIntegrals_TransInvLat
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical Complex
namespace PI.TransInvLatW
def PhaseOne : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∀ (x ω : ℂ) (m : ℕ), 0 < m →
    (m : ℂ) * (x / 2) ∈ lat2 w₁ w₂ → ω ∈ lat2 w₁ w₂ →
      exp ((Real.pi : ℂ) * (x * (starRingEnd ℂ) (2 * (m : ℂ) * ω) -
        (2 * (m : ℂ) * ω) * (starRingEnd ℂ) x) / (2 * (area (lat2 w₁ w₂) : ℂ))) = 1
end PI.TransInvLatW


