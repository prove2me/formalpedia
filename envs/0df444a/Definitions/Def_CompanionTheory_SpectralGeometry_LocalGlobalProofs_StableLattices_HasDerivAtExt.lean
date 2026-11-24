-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:25:28.446257+00:00
-- url     : https://prove2.me/theorems/f52a6fb7-9e36-4a56-8ec1-e99357bd2413
-- title:
--   Has Deriv At Ext
-- statement:
--   Definitions and structural lemmas for Has Deriv At Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExt.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace GlobalTheory.CompanionTheory.SmBracket
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
end GlobalTheory.CompanionTheory.SmBracket


