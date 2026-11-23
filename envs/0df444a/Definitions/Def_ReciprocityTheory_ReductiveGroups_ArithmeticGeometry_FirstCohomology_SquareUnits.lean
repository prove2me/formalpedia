-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:05.763476+00:00
-- url     : https://prove2.me/theorems/bd2ca99d-655a-4fff-b1de-2ae20c5a4683
-- title:
--   Square Units
-- statement:
--   Definitions and structural lemmas for Square Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SquareUnits.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
variable {X Y Z : Scheme.{0}}
def UnitAt (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) : Prop :=
  ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ J, Good L y J → IsUnit (sval s (𝟙 Y) y J)
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
section Square
variable {k : Type} [Field k]
end Square
end ReciprocityTheory.ChartRestriction.G.H1.SquareUnits


