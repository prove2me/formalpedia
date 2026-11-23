-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:26.388911+00:00
-- url     : https://prove2.me/theorems/f7e7e868-324b-42c3-8ada-e605acae0bb4
-- title:
--   Hw Map Of Low Span
-- statement:
--   Definitions and structural lemmas for Hw Map Of Low Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.CompanionTheory.DSICHWMap
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def diagOp (A : Module.End ℂ T) (B : Module.End ℂ V) : Module.End ℂ (WithLp 2 (T × V)) :=
  (WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ (A.prodMap B) ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap
end GlobalTheory.CompanionTheory.DSICHWMap


