-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:04.503673+00:00
-- url     : https://prove2.me/theorems/feed79c4-ce83-49aa-9750-d41b36ff5d04
-- title:
--   One Add Form Eq Iff
-- statement:
--   Definitions and structural lemmas for One Add Form Eq Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/OneAddFormEqIff.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
section Abstract
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
def phiH (H Y : Matrix m m A) : Matrix m m A := Y + Yᴴ + Yᴴ * H * Y
end Abstract
end Formalism.L2.SG.Pf.discriminantGroupCounts


