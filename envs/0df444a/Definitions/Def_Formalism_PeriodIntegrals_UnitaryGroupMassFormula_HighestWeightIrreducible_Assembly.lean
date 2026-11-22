-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_Assembly
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_Assembly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:47.2861+00:00
-- url     : https://prove2.me/theorems/f7d5b847-2286-4b86-a4a8-da676d764701
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/Assembly.lean

import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
end PI.WHw


