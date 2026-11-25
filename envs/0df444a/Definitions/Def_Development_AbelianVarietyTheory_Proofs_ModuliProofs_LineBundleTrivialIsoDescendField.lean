-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:09:34.39733+00:00
-- url     : https://prove2.me/theorems/5fd8c7b1-748c-4496-a6c7-8e43e8796504
-- title:
--   Line Bundle Trivial Iso Descend Field
-- statement:
--   Definitions and structural lemmas for Line Bundle Trivial Iso Descend Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleTrivialIsoDescendField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

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
noncomputable section
namespace GlobalTheory
namespace FieldDescentGen
variable {X₀ X : Scheme.{0}}
theorem pull_le (M : LB X₀) (φ : X ⟶ X₀) (j : PUnit → M.ι) : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit) :=
  fun _ hy => mem_pull.1 hy
def secPull (M : LB X₀) (φ : X ⟶ X₀) (s : M.Sec) : (M.pull φ).Sec where
  f j := (φ.appLE _ _ (pull_le M φ j)).hom (s.f (j PUnit.unit))
  compat i j := by
    have h : (M.pull φ).U i ⊓ (M.pull φ).U j ≤ φ ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
      fun _ hy => ⟨pull_le M φ i hy.1, pull_le M φ j hy.2⟩
    have e := congrArg (φ.appLE _ _ h).hom (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at e
    have g : ((M.pull φ).g i j : Γ(X, (M.pull φ).U i ⊓ (M.pull φ).U j)) =
        (φ.appLE _ _ h).hom (M.g (i PUnit.unit) (j PUnit.unit)) := by
      have gu : (M.pull φ).g i j = res h (pullU φ _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
        (Fintype.prod_unique fun k : PUnit => (res h (pullU φ _ (M.g (i k) (j k)))) ^ (1 : ℤ)).trans (zpow_one _)
      exact congrArg Units.val gu
    rw [g]
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at e ⊢
    exact e
def chartDiv (M N : LB X₀) (φ : X ⟶ X₀) :
    ChartPull ((LB.div N M).pull φ) (LB.div (N.pull φ) (M.pull φ)) (𝟙 X) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have a' := mem_pull.1 hj'
    refine (gm_pull_g (LB.div N M) φ (𝟙 X) y J J' hj hj').trans
      ((gm_div M N (𝟙 X ≫ φ) y (J PUnit.unit) (J' PUnit.unit) ⟨a, a'⟩).trans (Eq.symm ?_))
    refine (gm_div (M.pull φ) (N.pull φ) (𝟙 X) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, mem_pull.2 a'.1, mem_pull.2 a'.2⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹)
      (gm_pull_g N φ (𝟙 X) y _ _ (mem_pull.2 a.1) (mem_pull.2 a'.1))
      (gm_pull_g M φ (𝟙 X) y _ _ (mem_pull.2 a.2) (mem_pull.2 a'.2))
end FieldDescentGen
end GlobalTheory


