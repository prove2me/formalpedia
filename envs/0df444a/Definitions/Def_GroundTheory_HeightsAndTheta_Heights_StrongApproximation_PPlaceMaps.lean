-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
-- name    : GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:51.263798+00:00
-- url     : https://prove2.me/theorems/d1bbe1f7-21e4-4e59-9181-c74ce6d8e8dc
-- title:
--   PPlace Maps
-- statement:
--   Definitions and structural lemmas for PPlace Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
namespace PlaceMaps
section Lemmas
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
end Lemmas
end PlaceMaps
end StrongApprox
end GroundTheory.Heights₂.Heights


