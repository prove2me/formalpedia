-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:32.766238+00:00
-- url     : https://prove2.me/theorems/76c28aaa-c023-41d0-b60f-191b4c6ac500
-- title:
--   Exists Gen Of Quotient Of Rigid
-- statement:
--   Definitions and structural lemmas for Exists Gen Of Quotient Of Rigid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfQuotientOfRigid.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__4da20663a66f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace GenDescent
variable {Y Y' Z : Scheme.{0}}
def Compat (N : LB Z) (f : Y ⟶ Z) (a : ∀ i, Γ(Y, f ⁻¹ᵁ N.U i)ˣ) : Prop :=
  ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i j : N.ι), f (k w) ∈ N.U i → f (k w) ∈ N.U j →
    gm k w _ (a i) = gm (k ≫ f) w _ (N.g i j) * gm k w _ (a j)
theorem gm_pullU_eq_gm_comp {X Y W : Scheme.{0}} (h : Y ⟶ X) (k : W ⟶ Y) (w : W) (V : X.Opens)
    (u : Γ(X, V)ˣ) : gm k w (h ⁻¹ᵁ V) (pullU h V u) = gm (k ≫ h) w V u := by
  by_cases hw : k w ∈ h ⁻¹ᵁ V
  · rw [← gm_rp₁ k w (h ⁻¹ᵁ V) (k ⁻¹ᵁ (h ⁻¹ᵁ V)) le_rfl hw, gm_rp₂ k h w V _ le_rfl hw]
  · have hw' : ¬ (k ≫ h) w ∈ V := hw
    simp only [gm, dif_neg hw, dif_neg hw', MonoidHom.one_apply]
theorem Compat.pull {N : LB Z} {f : Y ⟶ Z} {a} (ha : Compat N f a) (h : Y' ⟶ Y) (f' : Y' ⟶ Z)
    (hf : h ≫ f = f') :
    ∃ a', Compat N f' a' ∧ ∀ (W : Scheme.{0}) (k : W ⟶ Y') (w : W) (i : N.ι), f' (k w) ∈ N.U i →
      gm k w _ (a' i) = gm (k ≫ h) w _ (a i) := by
  subst hf
  refine ⟨fun i => pullU h _ (a i), fun W k w i j hi hj => ?_, fun W k w i _ => gm_pullU_eq_gm_comp h k w _ (a i)⟩
  calc _ = gm (k ≫ h) w _ (a i) := gm_pullU_eq_gm_comp h k w _ (a i)
    _ = gm ((k ≫ h) ≫ f) w _ (N.g i j) * gm (k ≫ h) w _ (a j) := ha W (k ≫ h) w i j hi hj
    _ = _ := by
      rw [Category.assoc]
      congr 1
      exact (gm_pullU_eq_gm_comp h k w _ (a j)).symm
end GenDescent
end GlobalTheory


