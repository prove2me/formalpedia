-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
-- name    : Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:25.472537+00:00
-- url     : https://prove2.me/theorems/ffbd8592-ed8a-4052-be7c-93ea06edc256
-- title:
--   Complete Of Basis
-- statement:
--   Definitions and structural lemmas for Complete Of Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CompleteOfBasis.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Lemmata_MiscLemmasH_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
section Complete
variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)
end Complete
section Lift
variable {A : Type} [CommRing A] (I : Ideal A)
end Lift
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl


