-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:41.304492+00:00
-- url     : https://prove2.me/theorems/1477c3e8-a82f-40a5-bb7f-e6826ec6963c
-- title:
--   PClosed Point Unit Section
-- statement:
--   Definitions and structural lemmas for PClosed Point Unit Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
namespace ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
def IsUnitAt (P : HeightOneSpectrum (𝓞 K')) (d : ℕ) (g : K') : Prop :=
  ∀ u : T, P.valuation K' (y ⟨(), u⟩) ^ d ≤ P.valuation K' g
end ClosedPointUnitSectionAlt
end
end GroundTheory.Heights₂.Heights


