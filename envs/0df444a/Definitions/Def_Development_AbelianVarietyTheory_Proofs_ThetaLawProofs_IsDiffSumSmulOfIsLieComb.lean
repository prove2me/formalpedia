-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsDiffSumSmulOfIsLieComb
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsDiffSumSmulOfIsLieComb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:07.648855+00:00
-- url     : https://prove2.me/theorems/854361d4-07d3-4d43-80a0-a1017ba37ef6
-- title:
--   Is Diff Sum Smul Of Is Lie Comb
-- statement:
--   Definitions and structural lemmas for Is Diff Sum Smul Of Is Lie Comb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsDiffSumSmulOfIsLieComb.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory
namespace DiffLin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)
variable {R : Type} [CommRing R] {n : ℕ}
end DiffLin
end GlobalTheory


