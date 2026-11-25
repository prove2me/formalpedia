-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:08:12.042679+00:00
-- url     : https://prove2.me/theorems/5b0750cc-197c-4a8e-ab01-f05e8d3f509d
-- title:
--   Ma Measure B
-- statement:
--   Definitions and structural lemmas for Ma Measure B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
def chartMeasure {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) :
    Measure X :=
  ((volume.restrict (A.chart j).target).withDensity fun y =>
    ENNReal.ofReal (P.χ j ((A.chart j).symm y) * locDens A Φ j y)).map (A.chart j).symm
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
end
end ReciprocityTheory.AnForm.M


