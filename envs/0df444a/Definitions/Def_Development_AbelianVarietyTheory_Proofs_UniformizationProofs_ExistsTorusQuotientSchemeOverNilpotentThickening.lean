-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:02:13.710494+00:00
-- url     : https://prove2.me/theorems/a7593cc8-d4e6-4323-8157-f40f1db1d148
-- title:
--   Exists Torus Quotient Scheme Over Nilpotent Thickening
-- statement:
--   Definitions and structural lemmas for Exists Torus Quotient Scheme Over Nilpotent Thickening, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorusQuotientSchemeOverNilpotentThickening.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_add
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_mul
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_add
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul
import Theorems.Thm_GlobalTheory_AffineThickening_rs_rs
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_isWt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
namespace GlobalTheory.TorusQuotientLift
abbrev baseMap {A : Type} [CommRing A] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of A)) (V : G.Opens) :
    A →+* Γ(G, V) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ V le_top).hom
def subPresheaf {G B₀ : Scheme.{0}} (R : ∀ V : G.Opens, Subring Γ(G, V))
    (hres : ∀ (V V' : G.Opens) (h : V' ≤ V), ∀ a ∈ R V, rs h a ∈ R V') (W : B₀.Opens → G.Opens) (hW : Monotone W) :
    B₀.Opensᵒᵖ ⥤ CommRingCat.{0} where
  obj U := .of (R (W U.unop))
  map {V U} i := CommRingCat.ofHom ((rs (hW i.unop.le)).restrict _ _ (hres _ _ _))
  map_id U := by
    ext x
    exact congr($(G.presheaf.map_id (op (W U.unop))).hom x.1)
  map_comp i j := by
    ext x
    exact (rs_rs _ _ _).symm
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
section Weights
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
def wtSub (i : splitTorus S X ⟶ G) (V : G.left.Opens) (χ : X) : AddSubgroup Γ(G.left, V) where
  carrier := {a | IsWt i V a χ}
  add_mem' := IsWt.add
  zero_mem' := isWt_zero χ
  neg_mem' := fun {a} ha Z t g h₁ h₂ => by rw [map_neg, map_neg, ha Z t g h₁ h₂, mul_neg]
def wtZero (i : splitTorus S X ⟶ G) (V : G.left.Opens) : Subring Γ(G.left, V) :=
  { wtSub i V 0 with
    one_mem' := isWt_one
    mul_mem' := fun ha hb => _root_.add_zero (0 : X) ▸ IsWt.mul ha hb }
def Graded (i : splitTorus S X ⟶ G) (V : G.left.Opens) : Prop :=
  (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
    ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0
variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}
def unitWts (i : splitTorus S X ⟶ G) (V : G.left.Opens) : AddSubgroup X where
  carrier := {χ | ∃ u : Γ(G.left, V)ˣ, IsWt i V u.val χ}
  add_mem' := fun ⟨u, hu⟩ ⟨v, hv⟩ => ⟨u * v, hu.mul hv⟩
  zero_mem' := ⟨1, isWt_one⟩
  neg_mem' := fun ⟨u, hu⟩ => ⟨u⁻¹, hu.inv⟩
end Weights
end GlobalTheory.TorusQuotientLift
end


