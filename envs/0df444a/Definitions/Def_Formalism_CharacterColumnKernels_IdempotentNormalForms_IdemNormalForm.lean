-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IdemNormalForm
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_IdemNormalForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:30.106955+00:00
-- url     : https://prove2.me/theorems/0430020a-1c95-4435-9794-823206938d46
-- title:
--   Idem Normal Form
-- statement:
--   Definitions and structural lemmas for Idem Normal Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IdemNormalForm.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.NG
section RankMod
variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]
end RankMod
end Formalism.NG


