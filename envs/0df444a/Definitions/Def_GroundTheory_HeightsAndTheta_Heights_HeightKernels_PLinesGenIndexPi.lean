-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:32.617564+00:00
-- url     : https://prove2.me/theorems/fc4fa145-e9ae-4fb4-8f09-8304de6c593e
-- title:
--   PLines Gen Index Pi
-- statement:
--   Definitions and structural lemmas for PLines Gen Index Pi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexPi.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace KLinesGenIndexPi
open AddSubgroup
variable {η : Type} {G : Type} [AddCommGroup G]
def piIncl (K : η → AddSubgroup G) : (∀ i, K i) →+ AddSubgroup.pi Set.univ K where
  toFun x := ⟨fun i => (x i : G), by simp [AddSubgroup.mem_pi]⟩
  map_zero' := rfl
  map_add' _ _ := rfl
end KLinesGenIndexPi
end GroundTheory.Heights₂.Heights


