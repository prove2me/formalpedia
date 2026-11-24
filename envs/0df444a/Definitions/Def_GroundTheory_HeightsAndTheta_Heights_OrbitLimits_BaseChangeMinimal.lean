-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:30.761555+00:00
-- url     : https://prove2.me/theorems/5a4d50ba-31a5-46e3-8fd0-91f79f6652b3
-- title:
--   Base Change Minimal
-- statement:
--   Definitions and structural lemmas for Base Change Minimal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
namespace BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
section GD
attribute [local instance] MvPolynomial.algebraMvPolynomial
end GD
end BaseChangeMin
end GroundTheory.Heights₂.Heights.Targets


