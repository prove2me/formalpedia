-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:38.735157+00:00
-- url     : https://prove2.me/theorems/d507330d-a22f-44ea-affa-4f124e4127ff
-- title:
--   Rosati Adj Of Points
-- statement:
--   Definitions and structural lemmas for Rosati Adj Of Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RosatiAdjOfPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace IntAct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
theorem comp_id_zpow {T : Over S} (w : T ⟶ A) (a : ℤ) : w ≫ (𝟙 A) ^ a = w ^ a := by
  rw [GrpObj.comp_zpow, Category.comp_id]
theorem isMonHom_id_zpow (a : ℤ) : IsMonHom ((𝟙 A : A ⟶ A) ^ a) where
  one_hom := by
    rw [comp_id_zpow]
    have o : η[A] = 1 := by simp [Hom.one_def]
    rw [o, one_zpow]
  mul_hom := by
    have o : μ[A] = fst A A * snd A A := by simp [Hom.mul_def]
    rw [comp_id_zpow, o, mul_zpow, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, comp_id_zpow, comp_id_zpow]
variable (A) in

def intRingAct : RingAct A ℤ where
  act a := (𝟙 A) ^ a
  hom := isMonHom_id_zpow
  map_one := zpow_one _
  map_mul a b := by rw [comp_id_zpow, ← zpow_mul, _root_.mul_comm]
  map_add a b := zpow_add _ a b
end IntAct
end GlobalTheory


