-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:51.817854+00:00
-- url     : https://prove2.me/theorems/e92dea91-79f9-4564-973d-66146535be9a
-- title:
--   Block Chi One Triv
-- statement:
--   Definitions and structural lemmas for Block Chi One Triv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockChiOneTriv.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
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
namespace TrivialCharacterBlockLength
section Triv
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]
end Triv
end TrivialCharacterBlockLength
end Formalism.NG


