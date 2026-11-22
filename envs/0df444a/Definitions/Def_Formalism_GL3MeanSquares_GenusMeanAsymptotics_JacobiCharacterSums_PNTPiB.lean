-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:04.852646+00:00
-- url     : https://prove2.me/theorems/a134165c-4e15-4382-ab6a-1b39cde23459
-- title:
--   PNTPi B
-- statement:
--   Definitions and structural lemmas for PNTPi B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
def Fm (K θ β t : ℝ) : ℝ := K * (t - θ * t ^ β / β)
end Formalism.HermitianLattices.Ext.PrimesInProgressions


