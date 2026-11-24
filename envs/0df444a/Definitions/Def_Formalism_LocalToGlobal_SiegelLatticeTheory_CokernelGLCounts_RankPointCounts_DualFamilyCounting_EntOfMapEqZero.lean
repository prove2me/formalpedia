-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:37.474799+00:00
-- url     : https://prove2.me/theorems/c06ebfd6-894b-4de5-9012-9767683c40f8
-- title:
--   Ent Of Map Eq Zero
-- statement:
--   Definitions and structural lemmas for Ent Of Map Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EntOfMapEqZero.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
namespace Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]
def Ent (J : Ideal (𝓞 K)) (A : Matrix c c (𝓞 K)) : Prop := ∀ i j, A i j ∈ J
variable [Fact (IsFixF K F)]
end Formalism.L2.SG.Pf.discriminantNormShapes


