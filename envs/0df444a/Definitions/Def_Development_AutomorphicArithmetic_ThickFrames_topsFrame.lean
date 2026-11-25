-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsFrame
-- name    : Development_AutomorphicArithmetic_ThickFrames_topsFrame
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T17:13:34.221853+00:00
-- url     : https://prove2.me/theorems/dd525166-b0b9-598a-ac23-6ab2e70d396c
-- title:
--   tops Frame
-- statement:
--   Definitions and structural lemmas for tops Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/topsFrame.lean

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsGroup
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_topsGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0


