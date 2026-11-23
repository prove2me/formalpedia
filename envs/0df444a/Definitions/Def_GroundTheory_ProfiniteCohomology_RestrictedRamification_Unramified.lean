-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:43.410807+00:00
-- url     : https://prove2.me/theorems/dea02a3f-6945-465f-8a64-a0283273e7f0
-- title:
--   Unramified
-- statement:
--   Definitions and structural lemmas for Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]
end GroundTheory.ProfCoh


