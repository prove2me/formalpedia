-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExceptionalDirichletZeroUniqueZeroFreeRegion
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExceptionalDirichletZeroUniqueZeroFreeRegion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:20.918776+00:00
-- url     : https://prove2.me/theorems/52426c54-b783-4761-9cdf-0bf366f07b95
-- title:
--   Exceptional Dirichlet Zero Unique Zero Free Region
-- statement:
--   Definitions and structural lemmas for Exceptional Dirichlet Zero Unique Zero Free Region, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExceptionalDirichletZeroUniqueZeroFreeRegion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLZerosEqPrimitiveCharacterZerosStatement
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
namespace GlobalTheory.ExceptionalPair
end GlobalTheory.ExceptionalPair


