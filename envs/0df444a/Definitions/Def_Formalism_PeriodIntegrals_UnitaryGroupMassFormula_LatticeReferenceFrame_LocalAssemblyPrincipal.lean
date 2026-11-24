-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocalAssemblyPrincipal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocalAssemblyPrincipal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:36.910055+00:00
-- url     : https://prove2.me/theorems/69583a00-a09b-4be1-bcf0-d466c635a720
-- title:
--   Local Assembly Principal
-- statement:
--   Definitions and structural lemmas for Local Assembly Principal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_SpanSmulInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
namespace PI.ScRefExists.PPA
open PI.ScRefExists.Sk
def IsInt (I : Formalism.MainNotions.S.AutInst) (x : I.E) : Prop := ∃ a : 𝓞 I.E, (a : I.E) = x
section Int
variable (I : Formalism.MainNotions.S.AutInst)
end Int
end PI.ScRefExists.PPA


