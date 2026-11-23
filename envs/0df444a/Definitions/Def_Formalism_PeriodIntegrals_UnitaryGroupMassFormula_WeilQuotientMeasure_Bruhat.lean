-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_Bruhat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_Bruhat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:39.15917+00:00
-- url     : https://prove2.me/theorems/c3b69ff9-995b-46d6-a203-f339e6f6008e
-- title:
--   Bruhat
-- statement:
--   Definitions and structural lemmas for Bruhat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/Bruhat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
namespace PI.WeilQuotMeas.UnitaryGroupMassFormula
end PI.WeilQuotMeas.UnitaryGroupMassFormula


