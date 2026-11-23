-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:26.141121+00:00
-- url     : https://prove2.me/theorems/a57dfa57-7f7d-4586-9987-87b9ce5da2bd
-- title:
--   Exists Der Of Is Pushout
-- statement:
--   Definitions and structural lemmas for Exists Der Of Is Pushout, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.ProdLift
def derHom {S B : Type} [CommRing S] [CommRing B] (a : S →+* B) (δ : S → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = a x * δ y + a y * δ x) :
    S →+* DualNumber B where
  toFun x := TrivSqZeroExt.inl (a x) + TrivSqZeroExt.inr (δ x)
  map_one' := by
    have h' := hmul 1 1
    rw [_root_.mul_one, map_one, _root_.one_mul] at h'
    have h : δ 1 = 0 := left_eq_add.mp h'
    ext <;> simp [h]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero, left_eq_add] at h
    ext <;> simp [h]
  map_add' x y := by ext <;> simp [hadd]
  map_mul' x y := by ext <;> simp [hmul, mul_comm]
end GlobalTheory.KS.ProdLift
end


