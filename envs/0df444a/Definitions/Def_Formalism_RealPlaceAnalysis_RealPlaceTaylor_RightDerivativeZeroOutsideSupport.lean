-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:23:31.958718+00:00
-- url     : https://prove2.me/theorems/7be18e5b-ab1d-43b4-a6f3-f15265b71356
-- title:
--   Right Derivative Zero Outside Support
-- statement:
--   Definitions and structural lemmas for Right Derivative Zero Outside Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/RightDerivativeZeroOutsideSupport.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
section F4ALinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end F4ALinfty
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.REAL


