-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGen
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGen
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:30:46.736703+00:00
-- url     : https://prove2.me/theorems/4f63f62f-485c-4e33-aeaa-76b076aaaf46
-- title:
--   Bridge Level Gen
-- statement:
--   Definitions and structural lemmas for Bridge Level Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGen.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLatticeOfRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLevelGen
open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct
end Formalism.MainNotions.BridgeLevelGen
end


