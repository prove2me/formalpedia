-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:10.766743+00:00
-- url     : https://prove2.me/theorems/166630c6-728c-4c19-b108-4870e914b920
-- title:
--   Dvr Admissible Base And Power Series Eval Uniformiser
-- statement:
--   Definitions and structural lemmas for Dvr Admissible Base And Power Series Eval Uniformiser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/DvrAdmissibleBaseAndPowerSeriesEvalUniformiser.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsPrincipalIdealRingOfIsLocalization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Theorems.Thm_GlobalTheory_ChartRing_X_mem_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UniformiserEval
open GlobalTheory.ChartRing
variable {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
omit [IsAdicComplete (IsLocalRing.maximalIdeal V) V] in
theorem C_add_X_mem {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (PowerSeries.C a + PowerSeries.X : PowerSeries V) ∈ IsLocalRing.maximalIdeal (PowerSeries V) :=
  add_mem (C_mem_maximalIdeal_iff.2 ha) X_mem_maximalIdeal
def translate {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) : PowerSeries V →ₐ[V] PowerSeries V :=
  evalAdic V (IsLocalRing.maximalIdeal (PowerSeries V)) (C_add_X_mem ha)
end GlobalTheory.UniformiserEval


