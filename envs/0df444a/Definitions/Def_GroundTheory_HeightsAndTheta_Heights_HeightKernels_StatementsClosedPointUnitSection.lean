-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:54.965836+00:00
-- url     : https://prove2.me/theorems/16c0950c-58bf-4366-81e0-6881cf865ae7
-- title:
--   Statements Closed Point Unit Section
-- statement:
--   Definitions and structural lemmas for Statements Closed Point Unit Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsClosedPointUnitSection.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
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
def ClosedPointUnitSection.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        ∃ (e : ℕ) (g : K'), 1 ≤ e ∧ g ≠ 0 ∧ g ∈ chartLat y 1 e ∧
          ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
            (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) →
              ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W
end
end GroundTheory.Heights₂.Heights


