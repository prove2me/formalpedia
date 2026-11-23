-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:55.059057+00:00
-- url     : https://prove2.me/theorems/6e6e0aac-09b0-45d0-8c75-5b4de1e6bd24
-- title:
--   Eval Second Zero At Variable Zero
-- statement:
--   Definitions and structural lemmas for Eval Second Zero At Variable Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)
section
variable {K : Type} [Field K] [CharZero K]
theorem hasSubst_eval_second_zero : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries K), 0] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s
    · first
        | exact PowerSeries.constantCoeff_X
        | exact MvPowerSeries.constantCoeff_X ()
        | (simp [PowerSeries.X]; done)
        | rfl
    · simp
end
section
variable {K : Type} [Field K] [CharZero K]
end
end Formalism.L2.Th1.B


