-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_PhiCountingHolds
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_PhiCountingHolds
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:08.383154+00:00
-- url     : https://prove2.me/theorems/106a3061-3b7e-55be-8039-51bb52d268ad
-- title:
--   Phi Counting Holds
-- statement:
--   Definitions and structural lemmas for Phi Counting Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/PhiCountingHolds.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]
end Formalism.L2.SG.Pf.LocalizedFibreSets


