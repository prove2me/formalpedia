-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesLinear
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesLinear
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:24:08.445559+00:00
-- url     : https://prove2.me/theorems/e051365b-df90-4e18-a7d8-2c21635b749c
-- title:
--   Derived Series Linear
-- statement:
--   Definitions and structural lemmas for Derived Series Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesLinear.lean

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm
namespace GlobalTheory.CompanionTheory.BesselMapSm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end GlobalTheory.CompanionTheory.BesselMapSm


