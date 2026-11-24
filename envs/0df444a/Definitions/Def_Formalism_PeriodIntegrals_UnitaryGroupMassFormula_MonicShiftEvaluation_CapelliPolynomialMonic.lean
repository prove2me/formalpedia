-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:40:57.735659+00:00
-- url     : https://prove2.me/theorems/526878f6-0df7-453e-9b12-5446dbff71d8
-- title:
--   Capelli Polynomial Monic
-- statement:
--   Definitions and structural lemmas for Capelli Polynomial Monic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonicShiftEvaluation/CapelliPolynomialMonic.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
open Formalism.QuantumDeterminants
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation


