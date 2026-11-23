-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:49.79205+00:00
-- url     : https://prove2.me/theorems/dc4de29c-61fb-46d1-87a3-0dc43d49f9a9
-- title:
--   Core Gen Ideal
-- statement:
--   Definitions and structural lemmas for Core Gen Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/CoreGenIdeal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
namespace PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PI.LocLatEq.W


