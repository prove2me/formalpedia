-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiBigCellForm_BigCellEqW0BMulTM
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiBigCellForm_BigCellEqW0BMulTM
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:01:02.333869+00:00
-- url     : https://prove2.me/theorems/de45c90d-d083-41b6-b13d-83e89f509790
-- title:
--   Big Cell Eq W0 BMul TM
-- statement:
--   Definitions and structural lemmas for Big Cell Eq W0 BMul TM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiBigCellForm/BigCellEqW0BMulTM.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.SwBig.PhiFormProof
open PI.SwBig
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
end PI.SwBig.PhiFormProof


