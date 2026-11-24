-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:16.140822+00:00
-- url     : https://prove2.me/theorems/aa81a00c-e26e-4dfd-a5d8-be92d95fa641
-- title:
--   Valuation Le One Of Denom
-- statement:
--   Definitions and structural lemmas for Valuation Le One Of Denom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ValuationLeOneOfDenom.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace PI.KerDetFinW
open PI.KerIso
end PI.KerDetFinW


