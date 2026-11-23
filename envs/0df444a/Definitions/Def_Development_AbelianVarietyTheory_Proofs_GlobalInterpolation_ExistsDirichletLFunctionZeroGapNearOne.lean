-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:21.558431+00:00
-- url     : https://prove2.me/theorems/3ee53634-e071-426a-9d23-e1dc2bd3026f
-- title:
--   Exists Dirichlet LFunction Zero Gap Near One
-- statement:
--   Definitions and structural lemmas for Exists Dirichlet LFunction Zero Gap Near One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsDirichletLFunctionZeroGapNearOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.ZeroGapNearOne
end GlobalTheory.ZeroGapNearOne


