-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:10.370628+00:00
-- url     : https://prove2.me/theorems/cb4d1993-c4da-472d-809f-cfa9d8bc75b0
-- title:
--   APrime DA
-- statement:
--   Definitions and structural lemmas for APrime DA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeDA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
namespace LeviFormQuadraticSums
variable {n : ℕ}
section Main
variable {d : ℕ} (p : V n → V d) (U : Set (V n)) (c : ℝ)
variable {p U}
end Main
end LeviFormQuadraticSums
end
end ReciprocityTheory.L2DbarEstimates.Y


