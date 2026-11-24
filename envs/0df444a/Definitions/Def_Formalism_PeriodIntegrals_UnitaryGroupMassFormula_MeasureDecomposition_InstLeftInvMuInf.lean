-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:00:33.239142+00:00
-- url     : https://prove2.me/theorems/7639adf4-4e2f-4165-9771-a1e0e1da7576
-- title:
--   Inst Left Inv Mu Inf
-- statement:
--   Definitions and structural lemmas for Inst Left Inv Mu Inf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstLeftInvMuInf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace PI.ScMuExists.UnitaryGroupMassFormula
instance instSFiniteMuInf (I : Formalism.MainNotions.S.AutInst) : SFinite (muInf I) := by
  unfold muInf; infer_instance
instance instLeftInvMuInf (I : Formalism.MainNotions.S.AutInst) : (muInf I).IsMulLeftInvariant := by
  unfold muInf; infer_instance
end PI.ScMuExists.UnitaryGroupMassFormula


