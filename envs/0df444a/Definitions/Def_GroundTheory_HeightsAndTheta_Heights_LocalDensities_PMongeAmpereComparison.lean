-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:28.3358+00:00
-- url     : https://prove2.me/theorems/3c6a8632-a8af-4dc1-a46f-fee2adc1f4de
-- title:
--   PMonge Ampere Comparison
-- statement:
--   Definitions and structural lemmas for PMonge Ampere Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace MongeAmpereComparison
def cutoff (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, Real.smoothTransition u
end MongeAmpereComparison
end
end GroundTheory.Heights₂.Heights.FourB


