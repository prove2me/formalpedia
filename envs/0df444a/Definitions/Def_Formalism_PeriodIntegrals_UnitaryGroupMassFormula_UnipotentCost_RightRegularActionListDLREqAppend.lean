-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:52:06.769699+00:00
-- url     : https://prove2.me/theorems/c282612b-4411-4f32-893f-dbc1ab086313
-- title:
--   Right Regular Action List DLREq Append
-- statement:
--   Definitions and structural lemmas for Right Regular Action List DLREq Append, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
noncomputable local instance clmNACG : NormedAddCommGroup (B.Mat k r →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance clmNS : NormedSpace ℝ (B.Mat k r →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
namespace PI.UnitaryGroupMassFormula.UsCost
end PI.UnitaryGroupMassFormula.UsCost


