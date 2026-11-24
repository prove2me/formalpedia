-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudy
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:08.318956+00:00
-- url     : https://prove2.me/theorems/d56cf746-f38f-486e-a4d4-75475b97b92d
-- title:
--   Complex Hessian Log Fubini Study
-- statement:
--   Definitions and structural lemmas for Complex Hessian Log Fubini Study, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComplexHessianLogFubiniStudy.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton Filter Topology
open scoped ENNReal ComplexConjugate
namespace GlobalTheory.CompanionTheory.FSCrofton
variable {n : ℕ}
end GlobalTheory.CompanionTheory.FSCrofton


