-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:09.593816+00:00
-- url     : https://prove2.me/theorems/1ba4fc7b-de0d-4750-a492-48c534da402e
-- title:
--   PLength Finite Algebra
-- statement:
--   Definitions and structural lemmas for PLength Finite Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
open IsLocalRing
noncomputable section
namespace LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
end LengthFiniteAlgebra
end
end GroundTheory.Heights₂.Heights


