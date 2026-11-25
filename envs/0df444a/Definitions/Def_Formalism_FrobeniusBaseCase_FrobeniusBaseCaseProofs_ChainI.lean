-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
-- name    : Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:54.675174+00:00
-- url     : https://prove2.me/theorems/2dba4d38-1ab5-4ae2-9c1e-c1977b196abb
-- title:
--   Chain I
-- statement:
--   Definitions and structural lemmas for Chain I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
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
variable {k : Type*} [Field k] {Z C : Type*}
namespace Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
end Data
end
end Formalism.BaseCaseIdentities


