-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:51.103592+00:00
-- url     : https://prove2.me/theorems/e59cc53a-8380-4508-b8b1-69a1b5ba76d8
-- title:
--   Is Affine Hom Of Flat Quotient Of Affine Kernel
-- statement:
--   Definitions and structural lemmas for Is Affine Hom Of Flat Quotient Of Affine Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomOfFlatQuotientOfAffineKernel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
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
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
universe u
section Descent
set_option backward.isDefEq.respectTransparency.types false
end Descent
end GlobalTheory


