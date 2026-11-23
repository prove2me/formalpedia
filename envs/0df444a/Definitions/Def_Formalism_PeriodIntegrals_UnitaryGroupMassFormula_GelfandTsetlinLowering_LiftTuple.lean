-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTuple
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTuple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:17.168695+00:00
-- url     : https://prove2.me/theorems/9127c4cd-43c9-4c1f-8f16-6e998e109dd9
-- title:
--   Lift Tuple
-- statement:
--   Definitions and structural lemmas for Lift Tuple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTuple.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace LTF
open PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE
end LTF
end PI.WGL


