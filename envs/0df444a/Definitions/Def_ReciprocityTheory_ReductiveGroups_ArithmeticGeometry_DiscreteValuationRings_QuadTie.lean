-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:40.25492+00:00
-- url     : https://prove2.me/theorems/69cd08d9-cdea-462c-b853-e5015662e733
-- title:
--   Quad Tie
-- statement:
--   Definitions and structural lemmas for Quad Tie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/QuadTie.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.DVR
variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]
def qf (B : LinearMap.BilinForm 𝕜 W) (w : W) : 𝕜 := B w w / 2
variable {B : LinearMap.BilinForm 𝕜 W}
end ReciprocityTheory.ChartRestriction.G.DVR


