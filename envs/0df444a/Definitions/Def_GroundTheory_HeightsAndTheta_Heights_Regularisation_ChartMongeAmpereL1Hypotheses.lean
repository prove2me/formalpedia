-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:07.22381+00:00
-- url     : https://prove2.me/theorems/20efef51-8c2a-44a2-91ad-5a287dd19acb
-- title:
--   Chart Monge Ampere L1 Hypotheses
-- statement:
--   Definitions and structural lemmas for Chart Monge Ampere L1 Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ChartMongeAmpereL1Hypotheses.lean

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
open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
def ChartMongeAmpereL1Measure.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (P : PotentialCharts A) (om : LocPot X),
    IsPotential A om → IsPosPot A om → ∀ (g : ℝ → X → ℝ) (t₀ : ℝ), 0 < t₀ →
      (∀ k : Fin P.N,
        (∀ t : ℝ, 0 < t → t < t₀ → IntegrableOn (fun y => g t ((P.chart k).symm y)) (P.chartMid k)) ∧
        Tendsto (fun t => ∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) (𝓝[>] 0) (𝓝 0)) →
      (∀ t : ℝ, 0 < t → t < t₀ → Integrable (g t) (maMeasure A (fun _ : Fin D => om))) ∧
        Tendsto (fun t => ∫ x, |g t x| ∂(maMeasure A (fun _ : Fin D => om))) (𝓝[>] 0) (𝓝 0)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular


