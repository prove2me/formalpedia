-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WlemOfGfacts
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WlemOfGfacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:44.175483+00:00
-- url     : https://prove2.me/theorems/587da3b4-95af-4ed7-869e-f129065f11d4
-- title:
--   Wlem Of Gfacts
-- statement:
--   Definitions and structural lemmas for Wlem Of Gfacts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WlemOfGfacts.lean

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
open Finset
noncomputable section
namespace GlobalTheory.CompanionTheory.DSICWLem
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
def ht {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) * w c
end GlobalTheory.CompanionTheory.DSICWLem


