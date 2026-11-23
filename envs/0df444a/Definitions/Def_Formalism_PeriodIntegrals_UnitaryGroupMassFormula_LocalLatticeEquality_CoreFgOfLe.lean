-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:06.915722+00:00
-- url     : https://prove2.me/theorems/5d528e6f-dae2-44ae-9242-2fef2f3be0be
-- title:
--   Core Fg Of Le
-- statement:
--   Definitions and structural lemmas for Core Fg Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/CoreFgOfLe.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
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
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
end PI.LocLatEq.W


