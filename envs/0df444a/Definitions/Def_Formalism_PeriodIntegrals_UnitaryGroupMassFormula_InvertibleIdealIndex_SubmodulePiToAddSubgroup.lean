-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:07.653885+00:00
-- url     : https://prove2.me/theorems/c4d3bb03-99a9-4002-9b8c-1a8065577fa3
-- title:
--   Submodule Pi To Add Subgroup
-- statement:
--   Definitions and structural lemmas for Submodule Pi To Add Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
abbrev idS (I : Ideal (𝓞 E)) : AddSubgroup E :=
  ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).toAddSubgroup
end PI.InvIdealIdxPiWork
end


