-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitTerms
-- name    : Development_AutomorphicArithmetic_ThickFrames_orbitTerms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:56.347958+00:00
-- url     : https://prove2.me/theorems/c16a79a0-b879-4752-a889-eb62a47de387
-- title:
--   orbit Terms
-- statement:
--   Definitions and structural lemmas for orbit Terms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/orbitTerms.lean

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLowBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0


