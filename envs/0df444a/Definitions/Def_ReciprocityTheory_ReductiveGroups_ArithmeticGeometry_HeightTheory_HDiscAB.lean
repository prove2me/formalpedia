-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:39.345124+00:00
-- url     : https://prove2.me/theorems/7d088f88-fe9e-4053-b879-e95147d9fa64
-- title:
--   HDisc AB
-- statement:
--   Definitions and structural lemmas for HDisc AB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
namespace HDiscLat
open Module
variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]
end HDiscLat
end ReciprocityTheory.ChartRestriction.G.T0


