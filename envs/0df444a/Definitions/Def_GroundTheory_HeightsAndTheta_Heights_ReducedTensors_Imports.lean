-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_Imports
-- name    : GroundTheory_HeightsAndTheta_Heights_ReducedTensors_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:38.463056+00:00
-- url     : https://prove2.me/theorems/125caa89-a730-4bee-bb43-9593ef60e513
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ReducedTensors/Imports.lean

import Mathlib
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
open TensorProduct
namespace SectionsLattice
def BaseChangeReduced.Statement : Prop :=
  ∀ (k L A : Type) [Field k] [CharZero k] [Field L] [Algebra k L] [CommRing A] [Algebra k A],
    IsReduced A → IsReduced (L ⊗[k] A)
end SectionsLattice
end GroundTheory.Heights₂.Heights


