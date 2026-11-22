-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:25.30967+00:00
-- url     : https://prove2.me/theorems/4f996f79-f170-43b5-9776-ec55bd328f2d
-- title:
--   Exists Unitary Near
-- statement:
--   Definitions and structural lemmas for Exists Unitary Near, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsUnitaryNear.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StepIdentity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsInvOneAdd
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


