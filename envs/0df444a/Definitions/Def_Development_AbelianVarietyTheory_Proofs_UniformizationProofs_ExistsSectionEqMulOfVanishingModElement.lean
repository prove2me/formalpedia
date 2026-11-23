-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:45.65143+00:00
-- url     : https://prove2.me/theorems/0da16be2-880e-480a-a711-57c37c40a82f
-- title:
--   Exists Section Eq Mul Of Vanishing Mod Element
-- statement:
--   Definitions and structural lemmas for Exists Section Eq Mul Of Vanishing Mod Element, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSectionEqMulOfVanishingModElement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SectionKernel
variable {X Y : Scheme.{0}}
variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}
end GlobalTheory.SectionKernel


