-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:04:54.058558+00:00
-- url     : https://prove2.me/theorems/cd47d444-2c11-46be-8f54-8bf57347e989
-- title:
--   Deg Pderiv Mul
-- statement:
--   Definitions and structural lemmas for Deg Pderiv Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
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
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U
end PI.UnitaryGroupMassFormula.UsCompose


