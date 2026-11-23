-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:55.048087+00:00
-- url     : https://prove2.me/theorems/4a60047c-2b45-421b-bc81-45b45ab6990f
-- title:
--   Incl RAlgebra Map
-- statement:
--   Definitions and structural lemmas for Incl RAlgebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/InclRAlgebraMap.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [Field E] [Algebra F E]
end SlopeTestRemainingChoices
end PIW.AdelicOrbitU


