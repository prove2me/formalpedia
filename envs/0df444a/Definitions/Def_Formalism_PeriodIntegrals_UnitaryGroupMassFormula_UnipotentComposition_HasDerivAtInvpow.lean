-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:06:23.59355+00:00
-- url     : https://prove2.me/theorems/aa1cf56c-3f6c-4ea8-b402-32507ea40e0d
-- title:
--   Has Deriv At Invpow
-- statement:
--   Definitions and structural lemmas for Has Deriv At Invpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end PI.UnitaryGroupMassFormula.UsCompose


