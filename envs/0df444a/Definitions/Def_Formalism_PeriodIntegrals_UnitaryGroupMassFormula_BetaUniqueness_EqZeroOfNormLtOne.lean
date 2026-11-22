-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:53.897091+00:00
-- url     : https://prove2.me/theorems/1898eec5-499e-43b4-b84f-6ca4edc64e6e
-- title:
--   Eq Zero Of Norm Lt One
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Norm Lt One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BetaUniqueness/EqZeroOfNormLtOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA
variable {E : Type} [Field E] [NumberField E]
def InO (x : E) : Prop := ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = x
end PI.UnitaryGroupMassFormula.BetaLUniq.EigA


