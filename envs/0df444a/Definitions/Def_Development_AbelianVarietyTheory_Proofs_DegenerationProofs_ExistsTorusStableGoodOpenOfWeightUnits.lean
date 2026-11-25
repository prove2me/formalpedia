-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:35.766141+00:00
-- url     : https://prove2.me/theorems/3308ed9f-2918-425a-b11f-2d27bb7c9eb4
-- title:
--   Exists Torus Stable Good Open Of Weight Units
-- statement:
--   Definitions and structural lemmas for Exists Torus Stable Good Open Of Weight Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
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
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.TorusSlice
variable {S : Scheme.{0}}
def shearIso {T G : Over S} [GrpObj G] (i : T ⟶ G) : T ⊗ G ≅ T ⊗ G where
  hom := lift (fst T G) ((fst T G ≫ i) * snd T G)
  inv := lift (fst T G) ((fst T G ≫ i)⁻¹ * snd T G)
  hom_inv_id := by ext1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  inv_hom_id := by ext1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
def Equivar {T G Y : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) (j : Y ⟶ G) (σ : Y ⟶ T) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ T) (y y' : Z ⟶ Y), y' ≫ j = (t ≫ i) * (y ≫ j) → y' ≫ σ = t * (y ≫ σ)
variable {X : Type} [AddCommGroup X]
def ch {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) : Γ(Z.left, ⊤) := t.left.appTop.hom (charUnit S X χ).val
end GlobalTheory.SS.TorusSlice
namespace GlobalTheory.SS
open TorusSlice
end GlobalTheory.SS
end


