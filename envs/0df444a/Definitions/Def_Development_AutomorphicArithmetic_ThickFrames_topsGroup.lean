-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsGroup
-- name    : Development_AutomorphicArithmetic_ThickFrames_topsGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:29:04.008619+00:00
-- url     : https://prove2.me/theorems/3a0af27f-0bfc-42fb-ba46-a729412df83e
-- title:
--   tops Group
-- statement:
--   Definitions and structural lemmas for tops Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/topsGroup.lean

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_select
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitSum
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_SharesOfCounts
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitTerms
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_NotGoodLe
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_select

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical


