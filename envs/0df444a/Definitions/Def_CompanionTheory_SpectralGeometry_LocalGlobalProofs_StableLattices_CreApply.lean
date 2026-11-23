-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:40.242394+00:00
-- url     : https://prove2.me/theorems/3ae05ef5-1612-4114-9081-358c9dd55dda
-- title:
--   Cre Apply
-- statement:
--   Definitions and structural lemmas for Cre Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean

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
open Finset CompanionTheory.D.DSIC
noncomputable section
namespace GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}
def tw (i j : NC ε) : ℂ := if key j < key i then -1 else 1
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end GlobalTheory.CompanionTheory.ChainCAR


