-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:39.928197+00:00
-- url     : https://prove2.me/theorems/04a0ea0d-aaa8-4d4b-9308-62fa39161d40
-- title:
--   Norm Le Tsum Of Cube Fourier Coeff Le
-- statement:
--   Definitions and structural lemmas for Norm Le Tsum Of Cube Fourier Coeff Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
namespace GlobalTheory
namespace Koecher
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
end Koecher
end GlobalTheory


