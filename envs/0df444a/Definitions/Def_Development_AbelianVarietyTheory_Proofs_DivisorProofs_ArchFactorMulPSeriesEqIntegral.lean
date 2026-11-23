-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ArchFactorMulPSeriesEqIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ArchFactorMulPSeriesEqIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:47.684482+00:00
-- url     : https://prove2.me/theorems/b211cfbf-a072-46db-854d-bb31d8febdad
-- title:
--   Arch Factor Mul PSeries Eq Integral
-- statement:
--   Definitions and structural lemmas for Arch Factor Mul PSeries Eq Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ArchFactorMulPSeriesEqIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitUnfoldIntegralPartitionOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNonzeroIntegersPrincipalIdealsUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIntegralThetaMellinInterchangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegralNonzeroIntegerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
namespace GlobalTheory.HeckeMellin
end GlobalTheory.HeckeMellin


