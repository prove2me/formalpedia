-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:40.349807+00:00
-- url     : https://prove2.me/theorems/5f5444ca-cdfd-4040-bb2e-67ff724f54e6
-- title:
--   Dual At LMul Unit
-- statement:
--   Definitions and structural lemmas for Dual At LMul Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/DualAtLMulUnit.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
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
namespace PI.LocDualGen.Part2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
end PI.LocDualGen.Part2


