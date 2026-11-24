-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:57.79846+00:00
-- url     : https://prove2.me/theorems/1917a29f-dd63-45e5-a30e-ae4c357912b4
-- title:
--   Is KTheta
-- statement:
--   Definitions and structural lemmas for Is KTheta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
section IsKsec
variable (b : ℤ) (d : ℕ)
def IsK (t : ℂ) : Prop := ∃ p q r : ℤ, r ≠ 0 ∧ (r : ℂ) * t = p + q * cmTheta b d
variable {b d}
variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn
end IsKsec
end PI.UnitaryGroupMassFormula.UnimodLocStd


