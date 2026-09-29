-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1fd22ed7-93bc-5699-aa66-6e152105deb5

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul
import Theorems.Thm_AlgebraicGeometry_RelPicard_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_surjective
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace PicTanSurj

section RingSide

theorem map01_fst_oneAddEpsMul {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (A : Type u)
    [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).map01 (oneAddEpsMul A 𝒱 c f) = 1 := by
  have h1 : oneAddEpsMul A 𝒱 c f = 1 + (DualNumber.eps : DualNumber A) • (dualNumberThickening A 𝒱 c).map01 f := by
    simp only [oneAddEpsMul, Algebra.smul_def]
  rw [h1, map_add, LinearMap.map_smulₛₗ]
  have h2 : (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 := by simp
  rw [h2, zero_smul, add_zero, HomOver.map01_apply, map_one]

theorem nonempty_iso_unit_of_isFrameOn_of_map_eq {X : Scheme.{u}} {L : X.Modules} {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {sU : Γ(L, U)} {sV : Γ(L, V)} (hsU : Scheme.Modules.IsFrameOn sU U) (hsV : Scheme.Modules.IsFrameOn sV V)
    (h : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU =
      L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by
  refine Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul hUV hsU hsV
    (Scheme.Modules.isFrameOn_unitSection U) (Scheme.Modules.isFrameOn_unitSection V) 1 ?_ ?_
  · rw [h]; exact (one_smul _ _).symm
  · change (𝟙_ X.Modules).presheaf.map (homOfLE _).op (Scheme.Modules.unitSection U) =
      (1 : Γ(X, U ⊓ V)) • (𝟙_ X.Modules).presheaf.map (homOfLE _).op (Scheme.Modules.unitSection V)
    rw [Scheme.Modules.map_unitSection, Scheme.Modules.map_unitSection]
    exact ((Scheme.Modules.smul_unitSection _).trans rfl).symm

theorem isInvertible_of_isFrameOn_two {X : Scheme.{u}} {L : X.Modules} {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {sU : Γ(L, U)} {sV : Γ(L, V)} (hsU : Scheme.Modules.IsFrameOn sU U) (hsV : Scheme.Modules.IsFrameOn sV V) :
    Scheme.Modules.IsInvertible L := by
  apply Scheme.Modules.isInvertible_of_forall_exists_isFrameOn
  intro x
  have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
  rcases TopologicalSpace.Opens.mem_sup.1 hx with hxU | hxV
  · exact ⟨U, sU, hxU, hsU⟩
  · exact ⟨V, sV, hxV, hsV⟩

end RingSide

section Yoga

variable {X Y Z : Scheme.{u}}

theorem pullback_comp_unit (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (g ≫ f)).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackComp g f).app M).symm ≪≫ (Scheme.Modules.pullback g).mapIso h.some ≪≫
    Scheme.Modules.pullbackUnitIso g⟩

theorem pullback_congr_unit {f f' : Y ⟶ X} (hf : f = f') (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f').obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackCongr hf).app M).symm ≪≫ h.some⟩

theorem unit_of_pullback_comp (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback (g ≫ f)).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M) ≅ SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackComp g f).app M) ≪≫ h.some⟩

end Yoga

section SchemeSide

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

theorem stage_fstHom_hom :
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom = RelPicard.baseChangeSnd c (dualNumberReductionOver R A) := by
  change RelPicard.baseChangeSnd c (LFP.stageHom R (TrivSqZeroExt.fstHom R A A)) = _
  congr 1

theorem nonempty_pullback_red_iso_unit (M : (Limits.pullback c (specMap R (DualNumber A))).Modules)
    (a : Γ(M, (𝒱.pullback c (DualNumber A)).U0)) (b : Γ(M, (𝒱.pullback c (DualNumber A)).U1))
    (ha : Scheme.Modules.IsFrameOn a (𝒱.pullback c (DualNumber A)).U0)
    (hb : Scheme.Modules.IsFrameOn b (𝒱.pullback c (DualNumber A)).U1)
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01)
    (hab : M.presheaf.map (homOfLE inf_le_right).op b =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c f) •
        M.presheaf.map (homOfLE inf_le_left).op a) :
    Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R A))).obj M ≅
      SheafOfModules.unit (Limits.pullback c (specMap R A)).ringCatSheaf) := by
  obtain ⟨a', b', ha', hb', hab'⟩ :=
    Scheme.TwoAffineOpenCover.exists_isFrameOn_pullback_stage_of_map_eq_smul 𝒱 c (TrivSqZeroExt.fstHom R A A)
      M a b ha hb _ hab
  dsimp only at hab'
  rw [map01_fst_oneAddEpsMul] at hab'
  have h1 : ((Scheme.Modules.pullback (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom).obj M).presheaf.map
      (homOfLE (inf_le_left : (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1 ≤ _)).op a' =
      ((Scheme.Modules.pullback (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom).obj M).presheaf.map
      (homOfLE (inf_le_right : (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1 ≤ _)).op b' := by
    rw [hab']
    exact (one_smul _ _).symm
  obtain ⟨e⟩ := nonempty_iso_unit_of_isFrameOn_of_map_eq (𝒱.pullback c A).sup_eq_top ha' hb' h1
  rw [stage_fstHom_hom] at e
  exact ⟨e⟩

theorem nonempty_pullback_rigSection_iso_unit (M : (Limits.pullback c (specMap R (DualNumber A))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (hker : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R A))).obj M ≅
      SheafOfModules.unit (Limits.pullback c (specMap R A)).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (RelPicard.rigSection c (specMap R (DualNumber A)) ε)).obj M ≅
      SheafOfModules.unit (Spec (CommRingCat.of (DualNumber A))).ringCatSheaf) := by
  have hN : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (RelPicard.rigSection c (specMap R (DualNumber A)) ε)).obj M) := hM.pullback _
  refine Scheme.Modules.IsInvertible.nonempty_iso_unit_of_dualNumber_of_reduction A _ hN ?_

  have hsq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫
      RelPicard.rigSection c (specMap R (DualNumber A)) ε =
      RelPicard.rigSection c (specMap R A) ε ≫ RelPicard.baseChangeSnd c (dualNumberReductionOver R A) := by
    rw [RelPicard.rigSection_baseChangeSnd]
    rfl
  apply unit_of_pullback_comp
  apply pullback_congr_unit hsq.symm
  exact pullback_comp_unit _ _ M hker

end SchemeSide

end PicTanSurj

namespace PicTanSurj
section Units
variable {R : Type u} [CommRing R] {C : Scheme.{u}} (A : Type u) [CommRing A] [Algebra R A]
  (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

theorem oneAddEpsMul_add (f f' : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    oneAddEpsMul A 𝒱 c (f + f') = oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c f' := by
  simp only [oneAddEpsMul, map_add]
  have he : algebraMap (DualNumber A)
      ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 DualNumber.eps *
      algebraMap (DualNumber A) _ DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  linear_combination (-((dualNumberThickening A 𝒱 c).map01 f * (dualNumberThickening A 𝒱 c).map01 f')) * he

theorem isUnit_oneAddEpsMul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    IsUnit (oneAddEpsMul A 𝒱 c f) := by
  refine isUnit_iff_exists_inv.2 ⟨oneAddEpsMul A 𝒱 c (-f), ?_⟩
  rw [← oneAddEpsMul_add, add_neg_cancel]
  simp [oneAddEpsMul]

end Units
end PicTanSurj

open PicTanSurj in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    Function.Surjective δ := by
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have ht : IsUnit (show Γ(Limits.pullback c (specMap R (DualNumber A)),
      (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c f) :=
    isUnit_oneAddEpsMul A 𝒱 c f
  obtain ⟨M, a, b, ha, hb, hab⟩ := Scheme.Modules.exists_isFrameOn_of_isUnit
    (𝒱.pullback c (DualNumber A)).U0 (𝒱.pullback c (DualNumber A)).U1 _ ht
  have hM : Scheme.Modules.IsInvertible M :=
    isInvertible_of_isFrameOn_two (𝒱.pullback c (DualNumber A)).sup_eq_top ha hb
  have hker := nonempty_pullback_red_iso_unit c A 𝒱 M a b ha hb f hab
  have hrig := nonempty_pullback_rigSection_iso_unit c ε A M hM hker
  let Mr : RigidifiedLineBundle c ε (specMap R (DualNumber A)) := ⟨M, hM, hrig⟩
  have hmem : Nonempty ((Mr.pullbackAlong (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (specMap R A)).L) := hker
  exact ⟨Quotient.mk _ ⟨Mr, hmem⟩, hδ ⟨Mr, hmem⟩ a b f ha hb hab⟩

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_surjective (solution)
