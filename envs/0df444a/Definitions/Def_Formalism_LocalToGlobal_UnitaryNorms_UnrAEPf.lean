-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf
-- name    : Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:45.875398+00:00
-- url     : https://prove2.me/theorems/70161430-81da-4e0e-bbf0-75b24dd13f3d
-- title:
--   Unr AEPf
-- statement:
--   Definitions and structural lemmas for Unr AEPf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]
end Formalism.L2.Host


