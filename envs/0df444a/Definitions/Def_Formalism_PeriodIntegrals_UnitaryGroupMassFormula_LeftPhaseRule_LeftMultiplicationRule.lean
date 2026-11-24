-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:33.632611+00:00
-- url     : https://prove2.me/theorems/f29acae3-c6fc-4608-8da6-4e99574e5ba3
-- title:
--   Left Multiplication Rule
-- statement:
--   Definitions and structural lemmas for Left Multiplication Rule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/LeftMultiplicationRule.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
section Cases
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
  {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} {c : ℂ} {g₁ : Mx k r}
end Cases
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule


