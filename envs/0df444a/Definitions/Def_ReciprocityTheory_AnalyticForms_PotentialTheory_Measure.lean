-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Measure
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_Measure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:45.066739+00:00
-- url     : https://prove2.me/theorems/f1f5b651-468d-496b-af5c-986344e587cb
-- title:
--   Measure
-- statement:
--   Definitions and structural lemmas for Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Measure.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
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
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
def chartPartMeasure (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (s : ℝ) (j : Fin A.n) : Measure X :=
  ((volume.restrict (A.chart j).target).withDensity fun y =>
    ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))).map (A.chart j).symm
end
end ReciprocityTheory.AnForm.M


