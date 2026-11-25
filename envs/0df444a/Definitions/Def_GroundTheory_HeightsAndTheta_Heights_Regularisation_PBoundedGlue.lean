-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedGlue
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedGlue
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:45.346398+00:00
-- url     : https://prove2.me/theorems/14054a90-60f8-5e31-a328-d10c5b8ed621
-- title:
--   PBounded Glue
-- statement:
--   Definitions and structural lemmas for PBounded Glue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedGlue.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli regMax shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)
noncomputable section
namespace PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)
end PotentialCharts
namespace BoundedPshData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)
end BoundedPshData
end
end GroundTheory.Heights₂.Heights.Regular


