-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:57.224054+00:00
-- url     : https://prove2.me/theorems/0a894286-b3d8-4bcc-9d46-d9803f6e59b8
-- title:
--   Sum Insert Erase
-- statement:
--   Definitions and structural lemmas for Sum Insert Erase, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SumInsertErase.lean

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
open scoped InnerProductSpace
namespace GlobalTheory.CompanionTheory.DSChainAdj
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
end GlobalTheory.CompanionTheory.DSChainAdj


