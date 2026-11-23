-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:36.851843+00:00
-- url     : https://prove2.me/theorems/9e8b71da-4112-4ea9-87f8-d6c12916731c
-- title:
--   Unique Factorization Monoid Of Is Regular Ring Of Is Loca
-- statement:
--   Definitions and structural lemmas for Unique Factorization Monoid Of Is Regular Ring Of Is Loca, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/UniqueFactorizationMonoidOfIsRegularRingOfIsLoca.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace RegularFactorial
open IsLocalRing
end RegularFactorial
end GlobalTheory


