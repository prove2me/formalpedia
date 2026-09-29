-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.hasValue_placeOfPoint_of_sub_algebraMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1f3dc1a7-b6af-52b9-b4b0-028be9350d87

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_hasValue_placeOfPoint_of_sub_algebraMap_mem

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_hasValue_placeOfPoint_of_sub_algebraMap_mem.AlgebraicCurve"
open scoped TensorProduct

universe u v

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel Place Place.coe_algebraMap Place.residue_algebraMap"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "placeOfPoint toBase C range_stalk_eq ffEquiv ffEquiv_algebraMap mk"
namespace PlaceRead
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

theorem algebraMap_stalk_injective {X : Scheme.{u}} [IsIntegral X] (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨U, hxU, s', rfl⟩ := X.presheaf.germ_exist (x := x) s
  have hξU : genericPoint X ∈ U := (genericPoint_specializes x).mem_open U.2 hxU
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hxU s') =
      X.presheaf.germ U (genericPoint X) hξU s' := by
    rw [RingHom.algebraMap_toAlgebra]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [h1] at hs
  have : s' = 0 := germ_injective_of_isIntegral _ (genericPoint X) hξU (by rw [hs, map_zero])
  rw [this, map_zero]

theorem not_isUnit_germ_appIso_inv_of_mem {X : Scheme.{u}} {B : CommRingCat.{u}} (G : Spec B ⟶ X) [IsOpenImmersion G]
    (z : ↥(Spec B)) (f : B) (hf : f ∈ z.asIdeal) :
    ¬ IsUnit (X.presheaf.germ (G ''ᵁ ⊤) (G.base z) ⟨z, trivial, rfl⟩ ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv f))) := by
  intro hu
  have hmem : G.base z ∈ X.basicOpen ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv f)) :=
    (X.mem_basicOpen _ _ _).mpr hu
  rw [← Scheme.image_basicOpen, basicOpen_eq_of_affine] at hmem
  obtain ⟨z', hz', hzz'⟩ := hmem
  have : z' = z := G.isOpenEmbedding.injective hzz'
  subst this
  exact (PrimeSpectrum.mem_basicOpen f z').mp hz' hf

theorem germToFunctionField_appIso_inv_base {Y : Scheme.{u}} [IsIntegral Y] {B : CommRingCat.{u}} (G : Spec B ⟶ Y)
    [IsOpenImmersion G] {K : Type u} [Field K] (y : Y ⟶ Spec (CommRingCat.of K)) (c : CommRingCat.of K ⟶ B)
    (hc : G ≫ y = Spec.map c) [Nonempty ((G ''ᵁ ⊤ : Y.Opens) : Scheme.{u})] (k : K) :
    Y.germToFunctionField (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (c k))) =
      baseToFunctionField y k := by
  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality c) k
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  rw [e6, ← hc, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2k := CategoryTheory.ConcreteCategory.congr_hom (G.app_appIso_inv ⊤) (y.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k))
  rw [CategoryTheory.comp_apply] at h2k
  erw [h2k]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

theorem hasValue_placeOfPoint_of_sub_algebraMap_mem (M : CurveModel K L)
    {B : Type u} [CommRing B] [Algebra K B] (G : Spec (CommRingCat.of B) ⟶ M.C) [IsOpenImmersion G]
    (hG : G ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    [Nonempty ((G ''ᵁ ⊤ : M.C.Opens) : Scheme.{u})]
    (z : ↥(Spec (CommRingCat.of B))) (hz : G.base z ∈ closedPoints M.C)
    (f : B) (a : K) (hfa : f - algebraMap K B a ∈ z.asIdeal) :
    (M.placeOfPoint ⟨G.base z, hz⟩).HasValue
      (M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤)
        ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv f)))) a := by
  classical
  set v := M.placeOfPoint ⟨G.base z, hz⟩ with hv

  let φ : M.C.presheaf.stalk (G.base z) →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap (M.C.presheaf.stalk (G.base z)) M.C.functionField)
  have hφrange : φ.range = v.toValuationSubring.toSubring := M.range_stalk_eq ⟨G.base z, hz⟩
  have hφinj : Function.Injective φ := M.ffEquiv.symm.injective.comp (algebraMap_stalk_injective (G.base z))

  have hzW : G.base z ∈ (G ''ᵁ ⊤ : M.C.Opens) := ⟨z, trivial, rfl⟩
  let sec : B → Γ(M.C, G ''ᵁ ⊤) := fun b => (G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  have hsec : ∀ b, M.C.germToFunctionField (G ''ᵁ ⊤) (sec b) =
      algebraMap (M.C.presheaf.stalk (G.base z)) M.C.functionField (M.C.presheaf.germ (G ''ᵁ ⊤) (G.base z) hzW (sec b)) := by
    intro b
    rw [RingHom.algebraMap_toAlgebra]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  have hread : ∀ b, M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤) (sec b)) =
      φ (M.C.presheaf.germ (G ''ᵁ ⊤) (G.base z) hzW (sec b)) := by
    intro b
    rw [hsec]
    rfl

  have hconst : M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤) (sec (algebraMap K B a))) = algebraMap K L a := by
    apply M.ffEquiv.injective
    rw [RingEquiv.apply_symm_apply, M.ffEquiv_algebraMap]
    exact germToFunctionField_appIso_inv_base G M.toBase (CommRingCat.ofHom (algebraMap K B)) hG a

  have hmem : ∀ b, M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤) (sec b)) ∈ v.toValuationSubring := by
    intro b
    rw [hread, ← ValuationSubring.mem_toSubring, ← hφrange]
    exact ⟨_, rfl⟩
  refine ⟨hmem f, ?_⟩

  rw [← Place.residue_algebraMap]
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨e, he⟩ := hu.exists_right_inv
  obtain ⟨t, ht⟩ : ∃ t, φ t = (e : L) := by
    have : (e : L) ∈ φ.range := by rw [hφrange]; exact e.2
    exact this
  have hsecsub : sec (f - algebraMap K B a) = sec f - sec (algebraMap K B a) := by
    show (G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f - algebraMap K B a)) = _
    rw [map_sub, map_sub]
  have hd : (((⟨_, hmem f⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring a : v.toValuationSubring) : L) =
      φ (M.C.presheaf.germ (G ''ᵁ ⊤) (G.base z) hzW (sec (f - algebraMap K B a))) := by
    rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap, ← hconst, ← hread, hsecsub, map_sub, map_sub]
  have h2 := congrArg Subtype.val he
  rw [Subring.coe_mul, hd, ← ht, ← map_mul, OneMemClass.coe_one, ← map_one φ] at h2
  have h3 := hφinj h2
  exact not_isUnit_germ_appIso_inv_of_mem G z (f - algebraMap K B a) hfa (IsUnit.of_mul_eq_one _ h3)

end AlgebraicCurve.CurveModel.PlaceRead

open AlgebraicCurve.CurveModel.PlaceRead in
theorem solution
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    {B : Type u} [CommRing B] [Algebra K B] (G : Spec (CommRingCat.of B) ⟶ M.C) [IsOpenImmersion G]
    (hG : G ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    [Nonempty (Scheme.Opens.toScheme (G ''ᵁ ⊤))]
    (z : ↥(Spec (CommRingCat.of B))) (hz : G.base z ∈ closedPoints M.C)
    (f : B) (a : K) (hfa : f - algebraMap K B a ∈ z.asIdeal) :
    (M.placeOfPoint ⟨G.base z, hz⟩).HasValue
      (M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤)
        ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv f)))) a :=
  AlgebraicCurve.CurveModel.PlaceRead.hasValue_placeOfPoint_of_sub_algebraMap_mem M G hG z hz f a hfa

#print axioms solution

end
end S_AlgebraicCurve_CurveModel_hasValue_placeOfPoint_of_sub_algebraMap_mem
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_hasValue_placeOfPoint_of_sub_algebraMap_mem (solution)
