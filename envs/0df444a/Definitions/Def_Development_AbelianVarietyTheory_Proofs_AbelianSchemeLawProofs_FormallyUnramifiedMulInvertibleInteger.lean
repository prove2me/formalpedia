-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FormallyUnramifiedMulInvertibleInteger
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FormallyUnramifiedMulInvertibleInteger
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:47.58139+00:00
-- url     : https://prove2.me/theorems/117dc4da-296f-485f-995b-0e71a7b20852
-- title:
--   Formally Unramified Mul Invertible Integer
-- statement:
--   Definitions and structural lemmas for Formally Unramified Mul Invertible Integer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FormallyUnramifiedMulInvertibleInteger.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
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
end GlobalTheory


