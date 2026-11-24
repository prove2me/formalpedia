-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:38.336444+00:00
-- url     : https://prove2.me/theorems/89c4f7a6-c344-423f-abb1-d8f7945556d1
-- title:
--   Det Transpose Apply
-- statement:
--   Definitions and structural lemmas for Det Transpose Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/DetTransposeApply.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
end AAInvW


