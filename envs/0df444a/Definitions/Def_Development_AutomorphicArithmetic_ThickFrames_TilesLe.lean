-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_TilesLe
-- name    : Development_AutomorphicArithmetic_ThickFrames_TilesLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:17.387171+00:00
-- url     : https://prove2.me/theorems/e2f08179-2a92-4532-af74-f2a1abbaa5b6
-- title:
--   Tiles Le
-- statement:
--   Definitions and structural lemmas for Tiles Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/TilesLe.lean

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_marked_congr
import Theorems.Thm_GlobalTheory_RandomTops_tile_disjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open GlobalTheory.RandomTops (tile tile_disjoint marked_congr)


