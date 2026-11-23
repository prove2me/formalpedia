-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_CountBad
-- name    : Development_AutomorphicArithmetic_MeanSquareBounds_CountBad
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:19.137853+00:00
-- url     : https://prove2.me/theorems/16599e1a-5fed-4c98-a638-0da0543a271b
-- title:
--   Count Bad
-- statement:
--   Definitions and structural lemmas for Count Bad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZAll
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_CountBadCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
end QH


