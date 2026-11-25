-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalGroupSeriesToricPointExtension
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalGroupSeriesToricPointExtension
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:19.395168+00:00
-- url     : https://prove2.me/theorems/0fd210f5-385a-5dcd-9610-96896bfcbef6
-- title:
--   Exists Formal Group Series Toric Point Extension
-- statement:
--   Definitions and structural lemmas for Exists Formal Group Series Toric Point Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalGroupSeriesToricPointExtension.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSeriesEqOfEvalAtNilpotentPointsEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPoints
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
def pairAlg (R : Type) {S : Type} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S) :
    Subalgebra R (S × S) where
  carrier := {p | p.2 - p.1 ∈ J}
  mul_mem' := fun {a b} ha hb => by
    have : (a * b).2 - (a * b).1 = a.2 * (b.2 - b.1) + (a.2 - a.1) * b.1 := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hb) (J.mul_mem_right _ ha)
  add_mem' := fun {a b} ha hb => by
    have : (a + b).2 - (a + b).1 = (a.2 - a.1) + (b.2 - b.1) := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem ha hb
  algebraMap_mem' := fun c => by
    change _ ∈ J
    simp
end GlobalTheory.ChF


