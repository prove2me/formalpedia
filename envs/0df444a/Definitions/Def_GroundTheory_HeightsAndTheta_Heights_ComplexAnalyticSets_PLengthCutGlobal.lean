-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:03.783016+00:00
-- url     : https://prove2.me/theorems/4f869a71-d78b-4f64-949b-5f6dabbba9d0
-- title:
--   PLength Cut Global
-- statement:
--   Definitions and structural lemmas for PLength Cut Global, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
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
open scoped Pointwise
universe u v
namespace LengthCutGlobal
section Layers
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
end Layers
end LengthCutGlobal
end GroundTheory.Heights₂.Heights


