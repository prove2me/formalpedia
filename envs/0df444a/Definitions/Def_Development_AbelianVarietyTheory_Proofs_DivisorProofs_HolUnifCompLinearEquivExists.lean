-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HolUnifCompLinearEquivExists
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HolUnifCompLinearEquivExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:49:09.788379+00:00
-- url     : https://prove2.me/theorems/1c380885-6179-41af-85f6-dd3252f9c7fa
-- title:
--   Hol Unif Comp Linear Equiv Exists
-- statement:
--   Definitions and structural lemmas for Hol Unif Comp Linear Equiv Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HolUnifCompLinearEquivExists.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
namespace GlobalTheory.KeyFam
end GlobalTheory.KeyFam


