-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:05.458276+00:00
-- url     : https://prove2.me/theorems/772e6bdb-9a29-4c7c-9224-e462ca3934c8
-- title:
--   Glue Charts
-- statement:
--   Definitions and structural lemmas for Glue Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
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
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
section ChangeOfChart
variable {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
end ChangeOfChart
namespace RegChartData
variable (R : RegChartData A)
end RegChartData
end
end GroundTheory.Heights₂.Heights.Regular


