-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
-- name    : Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:25.54974+00:00
-- url     : https://prove2.me/theorems/5ed7ce34-81b5-452a-8528-54ffaf32bda9
-- title:
--   Fix All
-- statement:
--   Definitions and structural lemmas for Fix All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/FixAll.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
noncomputable section
open Classical
namespace Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
end Data
end
end Formalism.BaseCaseIdentities


