-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:07.68586+00:00
-- url     : https://prove2.me/theorems/9ccb0904-b8af-4004-8d67-f2c5f7c5b27f
-- title:
--   Has Gen
-- statement:
--   Definitions and structural lemmas for Has Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
def HasGen (F : (Y ⟶ X) →₀ ℤ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), fsum φ ε = F ∧
    ∃ g : LB.Gen (LB.LinComb L φ ε), g.IsGen
variable {L}
end ReciprocityTheory.ChartRestriction.G.DVR


