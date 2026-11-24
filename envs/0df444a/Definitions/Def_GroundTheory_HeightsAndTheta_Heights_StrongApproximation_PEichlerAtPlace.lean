-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:19.735328+00:00
-- url     : https://prove2.me/theorems/2e793772-0f8b-4863-bfde-ceac6cde8312
-- title:
--   PEichler At Place
-- statement:
--   Definitions and structural lemmas for PEichler At Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean

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
namespace EichlerAtPlace
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end EichlerAtPlace
end StrongApprox
end GroundTheory.Heights₂.Heights


