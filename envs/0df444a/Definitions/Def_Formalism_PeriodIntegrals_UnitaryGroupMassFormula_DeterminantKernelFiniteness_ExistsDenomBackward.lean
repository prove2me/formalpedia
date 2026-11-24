-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:57.877811+00:00
-- url     : https://prove2.me/theorems/32b440ad-c439-4b10-9571-aea32347ee28
-- title:
--   Exists Denom Backward
-- statement:
--   Definitions and structural lemmas for Exists Denom Backward, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsDenomBackward.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
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


