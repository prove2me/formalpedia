-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:41.898956+00:00
-- url     : https://prove2.me/theorems/b7281f13-0a5b-4887-ade2-ae5e210882f7
-- title:
--   Haar Exp A
-- statement:
--   Definitions and structural lemmas for Haar Exp A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
def QInv (nu : Measure V) (ε δ : ℝ) : Prop :=
  ∀ X : V, ‖X‖ < δ → ∀ r, 0 < r → r < δ →
    nu (closedBall X ((1 - ε) * r)) ≤ nu (closedBall 0 r) ∧
      nu (closedBall 0 r) ≤ nu (closedBall X ((1 + ε) * r))
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
end ReciprocityTheory.ChartRestriction.DS.HExp


