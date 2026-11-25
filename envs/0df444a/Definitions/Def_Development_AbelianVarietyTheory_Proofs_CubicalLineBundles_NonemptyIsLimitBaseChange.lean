-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:05.841542+00:00
-- url     : https://prove2.me/theorems/bcb14a05-edd4-56ec-83e1-48ae95fd481d
-- title:
--   Nonempty Is Limit Base Change
-- statement:
--   Definitions and structural lemmas for Nonempty Is Limit Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory
section Refine
variable {Y : Scheme.{0}}
end Refine
section Limit
variable {I : Type} [SmallCategory I] [IsCofiltered I]
def schemeConeOfFamily (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
    (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) : Cone D :=
  ⟨X, π, fun _ _ f => (Category.id_comp _).trans (w f).symm⟩
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] in
include w in
theorem cone_preimage_le {i j : I} (f : j ⟶ i) (U : (D.obj i).Opens) :
    π i ⁻¹ᵁ U ≤ π j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, w]
end Limit
section Tower
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
abbrev FGAbove (R₀ : Subalgebra k C) : Type := {R : Subalgebra k C // R.FG ∧ R₀ ≤ R}
variable {R₀ : Subalgebra k C}
theorem spMap_comp_ring {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A')
    (g : A' →+* A'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)
def baseChangeMap {A A' : Type} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] (f : A →ₐ[k] A') :
    pullback pB (spMap (algebraMap k A')) ⟶ pullback pB (spMap (algebraMap k A)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f.toRingHom) (by
    rw [pullback.condition, Category.assoc, spMap_comp_ring]
    congr 2
    exact f.comp_algebraMap.symm)
section
variable {A A' A'' : Type} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [CommRing A''] [Algebra k A'']
@[reassoc]
theorem baseChangeMap_fst (f : A →ₐ[k] A') :
    baseChangeMap pB f ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
@[reassoc]
theorem baseChangeMap_snd (f : A →ₐ[k] A') :
    baseChangeMap pB f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f.toRingHom := pullback.lift_snd _ _ _
theorem baseChangeMap_comp (f : A →ₐ[k] A') (g : A' →ₐ[k] A'') :
    baseChangeMap pB g ≫ baseChangeMap pB f = baseChangeMap pB (g.comp f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeMap_fst, baseChangeMap_fst, baseChangeMap_fst]
  · rw [Category.assoc, baseChangeMap_snd, baseChangeMap_snd_assoc, baseChangeMap_snd, spMap_comp_ring]
    rfl
theorem baseChangeMap_id : baseChangeMap pB (AlgHom.id k A) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [baseChangeMap_fst, Category.id_comp]
  · rw [baseChangeMap_snd, Category.id_comp]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
end
variable (R₀) in

def baseChangeDiagram : (FGAbove R₀)ᵒᵖ ⥤ Scheme.{0} where
  obj R := pullback pB (spMap (algebraMap k R.unop.1))
  map {R T} f := baseChangeMap pB (Subalgebra.inclusion (show T.unop.1 ≤ R.unop.1 from leOfHom f.unop))
  map_id _ := baseChangeMap_id pB
  map_comp {R S T} f g := (baseChangeMap_comp pB
    (Subalgebra.inclusion (show T.unop.1 ≤ S.unop.1 from leOfHom g.unop))
    (Subalgebra.inclusion (show S.unop.1 ≤ R.unop.1 from leOfHom f.unop))).symm
end Tower
end GlobalTheory


