-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MulMemUJset
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MulMemUJset
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:25:29.574526+00:00
-- url     : https://prove2.me/theorems/7334e848-b218-4361-a4de-f9b9301ec91e
-- title:
--   Mul Mem UJset
-- statement:
--   Definitions and structural lemmas for Mul Mem UJset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MulMemUJset.lean

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
open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm
namespace GlobalTheory.CompanionTheory.DSSmLin
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end GlobalTheory.CompanionTheory.DSSmLin


