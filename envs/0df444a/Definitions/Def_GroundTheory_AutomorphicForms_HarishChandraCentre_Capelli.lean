-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:58.618821+00:00
-- url     : https://prove2.me/theorems/ecfa642d-b684-43d6-ba9f-0ccee1dc7e51
-- title:
--   Capelli
-- statement:
--   Definitions and structural lemmas for Capelli, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
variable {n : ℕ}
noncomputable def capelliMatrix : Matrix (Fin n) (Fin n) (U n) := fun i j => e (i, j)
noncomputable def capelli (k : ℕ) : U n := Matrix.trace (capelliMatrix ^ k)
end GroundTheory.Automorphic.HarishChandra


