-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:58.138859+00:00
-- url     : https://prove2.me/theorems/6eb77c34-9235-4aae-9884-41825e60e4a3
-- title:
--   Norm One
-- statement:
--   Definitions and structural lemmas for Norm One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
namespace PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]
theorem map_integral (c : E →+* E) (y : 𝓞 E) : IsIntegral ℤ (c (y : E)) :=
  (RingOfIntegers.isIntegral_coe y).map c.toIntAlgHom
noncomputable def σ (c : E →+* E) (y : 𝓞 E) : 𝓞 E := ⟨c (y : E), map_integral c y⟩
end PI.DIP.NormOne


