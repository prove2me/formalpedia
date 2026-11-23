-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:53.361247+00:00
-- url     : https://prove2.me/theorems/b41d1139-1bd3-46a2-bc8a-bf88045b2939
-- title:
--   Exists Group Quotient Pullback
-- statement:
--   Definitions and structural lemmas for Exists Group Quotient Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGroupQuotientPullback.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace GlobalTheory
namespace CosetQuotient
universe v u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
end CosetQuotient
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory


