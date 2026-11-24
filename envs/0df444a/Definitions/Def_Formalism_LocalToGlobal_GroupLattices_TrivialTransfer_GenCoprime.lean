-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_GenCoprime
-- name    : Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_GenCoprime
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:43.95925+00:00
-- url     : https://prove2.me/theorems/edce6310-2246-4f0d-8068-24c9bf6edd78
-- title:
--   Gen Coprime
-- statement:
--   Definitions and structural lemmas for Gen Coprime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/GenCoprime.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions
namespace Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
end Formalism.L2.G.Triv
end


