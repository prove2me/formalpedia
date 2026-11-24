-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:52.016287+00:00
-- url     : https://prove2.me/theorems/c9c0adda-94f9-4fb3-b11f-de1355b127ca
-- title:
--   Is Open Adic Completion Integers
-- statement:
--   Definitions and structural lemmas for Is Open Adic Completion Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleUnitsOpen/IsOpenAdicCompletionIntegers.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace PI.IdeleUnitsOpenW
variable (L : Type) [Field L] [NumberField L]
def integralAdeles : Set (AdeleRing (𝓞 L) L) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 L), Valued.v (x.2 v) ≤ 1}
end PI.IdeleUnitsOpenW


