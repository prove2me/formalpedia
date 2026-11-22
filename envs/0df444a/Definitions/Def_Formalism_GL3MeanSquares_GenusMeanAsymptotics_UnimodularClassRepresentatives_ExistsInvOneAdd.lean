-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsInvOneAdd
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsInvOneAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:11.893912+00:00
-- url     : https://prove2.me/theorems/047eeed0-2b50-4bd8-b8aa-f7947c822f23
-- title:
--   Exists Inv One Add
-- statement:
--   Definitions and structural lemmas for Exists Inv One Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsInvOneAdd.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
end Formalism.HermitianLattices.Ext.L3.HU


