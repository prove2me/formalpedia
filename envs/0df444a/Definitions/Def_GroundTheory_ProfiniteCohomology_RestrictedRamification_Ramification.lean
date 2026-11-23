-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:55.179669+00:00
-- url     : https://prove2.me/theorems/c11f1407-ee1e-470d-b0d1-fe8ba8fbc971
-- title:
--   Ramification
-- statement:
--   Definitions and structural lemmas for Ramification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean

import Mathlib
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
section Tower
variable {F L M : Type*} [Field F] [Field L] [Field M] [NumberField F] [NumberField L]
  [NumberField M] [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]
end Tower
section Inertia
variable {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]
variable [NumberField F] [NumberField E] [NumberField M] [IsGalois F M]
end Inertia
end GroundTheory.ProfCoh


