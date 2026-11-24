-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsChartPartition
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsChartPartition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:03.840704+00:00
-- url     : https://prove2.me/theorems/5798e633-b268-44fc-b8e2-3deb38783712
-- title:
--   Statements Chart Partition
-- statement:
--   Definitions and structural lemmas for Statements Chart Partition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/StatementsChartPartition.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
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
open ReciprocityTheory.AnForm.M
def ChartPartitionExists.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (A : FinHolAtlas e X),
    Nonempty (ChartPartition A)
end GroundTheory.Heights₂.Heights.FourB


