-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T17:18:04.585467+00:00
-- url     : https://prove2.me/theorems/c3b15daa-43a3-53ef-aa36-ce3128ba8e5f
-- title:
--   Mem Range App LEChart Iff
-- statement:
--   Definitions and structural lemmas for Mem Range App LEChart Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemRangeAppLEChartIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Theorems.Thm_GlobalTheory_ZJ_charUnit_zero_val
import Theorems.Thm_GlobalTheory_ZJ_hasWt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
namespace GlobalTheory.ZJ
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs
def wtZeroSubring {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) : Subring Γ(H.left, V) where
  carrier := {u | HasWt i V u 0}
  one_mem' := hasWt_one i V
  zero_mem' := fun Y t g h h' => by rw [map_zero, map_zero, mul_zero]
  mul_mem' := fun {a b} ha hb Y t g h h' => by
    have h₁ := ha Y t g h h'
    have h₂ := hb Y t g h h'
    rw [charUnit_zero_val, map_one, _root_.one_mul] at h₁ h₂ ⊢
    rw [map_mul, map_mul, h₁, h₂]
  add_mem' := fun {a b} ha hb Y t g h h' => by
    rw [map_add, map_add, ha Y t g h h', hb Y t g h h', mul_add]
  neg_mem' := fun {a} ha Y t g h h' => by
    rw [map_neg, map_neg, ha Y t g h h', mul_neg]
end GlobalTheory.ZJ
end


