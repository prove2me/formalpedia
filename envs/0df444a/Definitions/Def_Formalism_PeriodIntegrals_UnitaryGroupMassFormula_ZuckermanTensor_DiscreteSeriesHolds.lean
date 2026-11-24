-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DiscreteSeriesHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DiscreteSeriesHolds
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:41.779197+00:00
-- url     : https://prove2.me/theorems/2bfa3f86-5967-4da4-bf30-3cfc7e630505
-- title:
--   Discrete Series Holds
-- statement:
--   Definitions and structural lemmas for Discrete Series Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DiscreteSeriesHolds.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_DSExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ZuckDualOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_RevNum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_SquareIntegrableConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.ZuckTensorWork
open PI.ZuckTensor
end PI.ZuckTensorWork


