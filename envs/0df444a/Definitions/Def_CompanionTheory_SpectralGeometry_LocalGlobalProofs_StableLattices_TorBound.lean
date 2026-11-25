-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorBound
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorBound
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:17:07.160342+00:00
-- url     : https://prove2.me/theorems/4d2d387e-131c-5b00-97da-504353096c3a
-- title:
--   Tor Bound
-- statement:
--   Definitions and structural lemmas for Tor Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorBound.lean

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
open Matrix CompanionTheory.Bmu Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
noncomputable section
namespace GlobalTheory.CompanionTheory.BmuTorBound
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end GlobalTheory.CompanionTheory.BmuTorBound


