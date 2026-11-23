-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothIsMultiplicative
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothIsMultiplicative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:50.876026+00:00
-- url     : https://prove2.me/theorems/3a3b238a-7fa4-4378-aa0b-9c5207c3a832
-- title:
--   Smooth Is Multiplicative
-- statement:
--   Definitions and structural lemmas for Smooth Is Multiplicative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SmoothIsMultiplicative.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.PowGrp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
theorem smooth_isMultiplicative : MorphismProperty.IsMultiplicative (C := Scheme.{0}) @Smooth where
  id_mem _ := inferInstance
  comp_mem f g (_ : Smooth f) (_ : Smooth g) := inferInstance
attribute [local instance] smooth_isMultiplicative
end GlobalTheory.PowGrp


