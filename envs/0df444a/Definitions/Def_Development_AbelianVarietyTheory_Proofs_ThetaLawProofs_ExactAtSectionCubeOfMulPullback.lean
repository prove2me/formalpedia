-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:37:26.330185+00:00
-- url     : https://prove2.me/theorems/4e196d1a-ec60-4589-9251-11db54663f0e
-- title:
--   Exact At Section Cube Of Mul Pullback
-- statement:
--   Definitions and structural lemmas for Exact At Section Cube Of Mul Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExactAtSectionCubeOfMulPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_congr
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_pb
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_rs
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_rs_pb
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_rs_pull_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
namespace GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish
variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)
theorem le_deck {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) (j : (M.pull f).ι) :
    W' ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U j) := fun y hy =>
  ⟨e hy.1, mem_pull.2 (by
    have := mem_pull.1 hy.2
    rwa [← hτ] at this)⟩
def act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) :
    SecOn (M.pull f) W →+ SecOn (M.pull f) W' where
  toFun s := GlobalTheory.LB.mkSec (fun j => pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j)) fun i j => by
    have e₀ : W' ⊓ (M.pull f).U i ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U i ⊓ (M.pull f).U j) :=
      le_deck f M hτ (le_deck f M hτ e i) j
    have h := congrArg (pb τ e₀) (GlobalTheory.LB.coord_mem s i j)
    have g₁ : ∀ (O : Y.Opens) (e : O ≤ (M.pull f).U i ⊓ (M.pull f).U j),
        rs Y e ((M.pull f).g i j).val = pb f (pre_pull M f (i PUnit.unit) (j PUnit.unit) e)
          (M.g (i PUnit.unit) (j PUnit.unit)).val :=
      fun O e => rs_pull_g M f (i PUnit.unit) (j PUnit.unit) (W := O) e
    exact (rs_pb τ _ _ _).trans ((pb_rs τ e₀ _ _).symm.trans (h.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ((congrArg (pb τ e₀) (g₁ _ _)).trans ((pb_pb τ f _ e₀ _).trans
        ((pb_congr hτ _ _).trans (g₁ _ _).symm))) ((pb_rs τ e₀ _ _).trans (rs_pb τ _ _ _).symm)))))
  map_zero' := GlobalTheory.LB.sec_ext fun j => map_zero (pb τ _)
  map_add' s t := GlobalTheory.LB.sec_ext fun j => map_add (pb τ _) _ _
variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal
end GlobalTheory.TraceDescent


