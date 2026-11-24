-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:59.78245+00:00
-- url     : https://prove2.me/theorems/97a7da0a-df61-4cc3-9071-6cd42fc79ce0
-- title:
--   Statements Closed Point Chart
-- statement:
--   Definitions and structural lemmas for Statements Closed Point Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsClosedPointChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def ClosedPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a
end
end GroundTheory.Heights₂.Heights


