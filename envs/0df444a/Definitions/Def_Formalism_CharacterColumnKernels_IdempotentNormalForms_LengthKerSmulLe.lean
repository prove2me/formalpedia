-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:00.031452+00:00
-- url     : https://prove2.me/theorems/54b9e7b6-6e86-413c-9048-712f1d6b8d3e
-- title:
--   Length Ker Smul Le
-- statement:
--   Definitions and structural lemmas for Length Ker Smul Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerSmulLe.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
namespace KernelLengthBounds
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end KernelLengthBounds
end Formalism.NG


