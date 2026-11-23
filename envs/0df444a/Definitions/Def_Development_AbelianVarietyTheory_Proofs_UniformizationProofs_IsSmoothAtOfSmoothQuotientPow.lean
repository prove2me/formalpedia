-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSmoothAtOfSmoothQuotientPow
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSmoothAtOfSmoothQuotientPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:04.517409+00:00
-- url     : https://prove2.me/theorems/25b09eb0-7aa2-4b49-b484-3d3600a1c738
-- title:
--   Is Smooth At Of Smooth Quotient Pow
-- statement:
--   Definitions and structural lemmas for Is Smooth At Of Smooth Quotient Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSmoothAtOfSmoothQuotientPow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SmoothLimit
section Ring
open TensorProduct IsLocalRing
variable {V A S C : Type} [CommRing V] [CommRing A] [CommRing S] [CommRing C] [Algebra V A]
  [Algebra A S] [Algebra V S] [IsScalarTower V A S] [Algebra V C]
end Ring
end GlobalTheory.SmoothLimit


