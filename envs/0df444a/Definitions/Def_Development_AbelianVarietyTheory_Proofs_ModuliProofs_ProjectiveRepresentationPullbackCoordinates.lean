-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:07:25.965589+00:00
-- url     : https://prove2.me/theorems/6127bd61-fc52-5d89-b26b-0226bd0236e8
-- title:
--   Projective Representation Pullback Coordinates
-- statement:
--   Definitions and structural lemmas for Projective Representation Pullback Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}
theorem r_appLE (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V) (a : Γ(X, U)) :
    resG Y h ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← f.appLE_map e (homOfLE h).op]; rfl
theorem appLE_r (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(X, U')) :
    (f.appLE U V e).hom (resG X h a) = (f.appLE U' V (e.trans (fun _ hy => h hy))).hom a := by
  rw [← f.map_appLE e (homOfLE h).op]; rfl
theorem pull_le (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j PUnit.unit) :=
  LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit
theorem pull_g (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (e : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    ((M.pull f).g j j').val = (f.appLE _ _ e).hom (M.g (j PUnit.unit) (j' PUnit.unit)).val := by
  show ((∏ _k : PUnit, (res e (pullU f _ (M.g (j PUnit.unit) (j' PUnit.unit)))) ^ (1 : ℤ) :
    Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl
theorem pull_inf_le (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι) :
    (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :=
  fun _ h => ⟨pull_le M f j h.1, pull_le M f j' h.2⟩
def secPull (M : LB X) (f : Y ⟶ X) (s : M.Sec) : (M.pull f).Sec where
  f j := (f.appLE _ _ (pull_le M f j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h := congrArg (f.appLE _ _ (pull_inf_le M f j j')).hom (s.compat (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul] at h
    erw [← pull_g M f j j'] at h
    erw [appLE_r, appLE_r] at h
    erw [r_appLE, r_appLE]
    exact h
end GlobalTheory.ZM.RepBC
end


