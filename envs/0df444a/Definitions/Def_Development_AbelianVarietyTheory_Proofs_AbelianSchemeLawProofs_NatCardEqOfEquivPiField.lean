-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NatCardEqOfEquivPiField
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NatCardEqOfEquivPiField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:08.926497+00:00
-- url     : https://prove2.me/theorems/3e522df9-97eb-46df-ab0e-fe9aa7f83500
-- title:
--   Nat Card Eq Of Equiv Pi Field
-- statement:
--   Definitions and structural lemmas for Nat Card Eq Of Equiv Pi Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NatCardEqOfEquivPiField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace MulLaw
noncomputable def basePointsEquiv {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    [GrpObj A] [GrpObj A'] {g : A'.left ⟶ A.left} (hg : IsPullback g A'.hom A.hom f)
    (hmul : ∀ (T : Over S') (x y : T ⟶ A'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    (T ⟶ A') ≃* (Over.mk (T.hom ≫ f) ⟶ A) where
  toFun x := toBase hg.w x
  invFun y := Over.homMk (hg.lift y.left T.hom (Over.w y)) (hg.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply hg.hom_ext
    · exact hg.lift_fst _ _ _
    · exact (hg.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := by
    apply Over.OverMorphism.ext
    exact hg.lift_fst _ _ _
  map_mul' x y := hmul T x y
end MulLaw
end GlobalTheory


