-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAETopologicalRing
-- name    : GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAETopologicalRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:07.170909+00:00
-- url     : https://prove2.me/theorems/78cbf728-cbd3-4d5b-91b5-5a14bbd5aa31
-- title:
--   PAETopological Ring
-- statement:
--   Definitions and structural lemmas for PAETopological Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAETopologicalRing.lean

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
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def AETopologicalRing.sigALinear (c : E ≃ₐ[F] E) :
    AE F E →ₗ[FiniteAdeleRing (𝓞 F) F] AE F E :=
  LinearMap.baseChange (FiniteAdeleRing (𝓞 F) F) c.toLinearMap
end
end StrongApprox
end GroundTheory.Heights₂.Heights


