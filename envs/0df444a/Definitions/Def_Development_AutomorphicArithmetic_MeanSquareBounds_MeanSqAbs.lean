-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_MeanSqAbs
-- name    : Development_AutomorphicArithmetic_MeanSquareBounds_MeanSqAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:28.662801+00:00
-- url     : https://prove2.me/theorems/5924ac99-25e0-4b43-a4dd-f3de887e1f5d
-- title:
--   Mean Sq Abs
-- statement:
--   Definitions and structural lemmas for Mean Sq Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMain
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


