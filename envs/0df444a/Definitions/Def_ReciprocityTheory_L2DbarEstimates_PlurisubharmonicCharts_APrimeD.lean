-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeD
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:20.602942+00:00
-- url     : https://prove2.me/theorems/b5ac9e48-36d9-439e-be79-1ce4d203b5e6
-- title:
--   APrime D
-- statement:
--   Definitions and structural lemmas for APrime D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeD.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
namespace LeviFormQuadraticSums
variable {n d : ℕ} {p : V n → V d} {U : Set (V n)}
end LeviFormQuadraticSums
end
end ReciprocityTheory.L2DbarEstimates.Y


