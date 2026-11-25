-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:16:19.587625+00:00
-- url     : https://prove2.me/theorems/3c71f5d6-c133-5c33-883c-dbdf78670916
-- title:
--   St Chart Levi Th Ge
-- statement:
--   Definitions and structural lemmas for St Chart Levi Th Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/StChartLeviThGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
def ChartLeviThGe.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (P : PotentialCharts A) (om : LocPot X), IsPotential A om → IsPosPot A om →
    ∃ c : ℝ, 0 < c ∧ ∀ (f : X → ℝ) (a : ℝ), 0 ≤ a → A.Smooth f →
      (∀ k : Fin P.N, ∀ x ∈ P.mid k, ∀ w : Fin D → ℂ,
        -a * ‖w‖ ^ 2 ≤ levi (P.chartFun f k) (P.chart k x) w) →
      ThGe A P.th f om (-(a / c))
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular


