-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.of_pullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/bd4b650c-1b15-5fe8-8a90-a2455d554696

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply"
p2m_attr_erase "simp" "IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

noncomputable section

namespace E24D4

theorem isPullback_of_lift {C : Type*} [Category C] {A A' B B' T T₁ : C} {f : A ⟶ B} {f' : A' ⟶ B'} {gA : A' ⟶ A}
    {b : B' ⟶ B} (hg : IsPullback gA f' f b) (ι'' : T ⟶ B') (ι₁ : T₁ ⟶ B) (j : T ⟶ T₁) (hbase : ι'' ≫ b = j ≫ ι₁)
    [HasPullback f' ι''] [HasPullback f ι₁]
    (u₁ : pullback f' ι'' ⟶ pullback f ι₁) (h1 : u₁ ≫ pullback.fst f ι₁ = pullback.fst f' ι'' ≫ gA)
    (h2 : u₁ ≫ pullback.snd f ι₁ = pullback.snd f' ι'' ≫ j) :
    IsPullback u₁ (pullback.snd f' ι'') (pullback.snd f ι₁) j := by
  have big := (IsPullback.of_hasPullback f' ι'').paste_horiz hg
  rw [← h1, hbase] at big
  exact IsPullback.of_right big h2 (IsPullback.of_hasPullback f ι₁)

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem one_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s') :
    (L.one s).1 = (L.one s').1 := by
  subst hs; rfl

theorem inv_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s')
    (P : SchemeHomOver s f) (Q : SchemeHomOver s' f) (hPQ : P.1 = Q.1) : (L.inv s P).1 = (L.inv s' Q).1 := by
  subst hs; cases Subtype.ext hPQ; rfl

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

def transitionHom (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') :
    letI := G.pointGroup t; letI := G.pointGroup t''; SchemeHomOver t f →* SchemeHomOver t'' f :=
  letI := G.pointGroup t; letI := G.pointGroup t''
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := G.one_natural t t'' ψ hψ
    map_mul' := fun x y => G.mul_natural t t'' ψ hψ x y }

theorem inv_natural (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t'' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t; letI := G.pointGroup t''
  exact map_inv (transitionHom G t t'' ψ hψ) x

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

def pushAlong (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ ψ) f :=
  ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushAlong_val (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A)
    (hu : u ≫ f = f' ≫ ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    (pushAlong ψ u hu t' P).1 = P.1 ≫ u := rfl

section Hom

variable (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ u =
      (L.mul (t' ≫ ψ)
        ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, Q.2]⟩).1)

def pushHom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ ψ)
    SchemeHomOver t' f' →* SchemeHomOver (t' ≫ ψ) f :=
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  MonoidHom.mk' (fun P => pushAlong ψ u hu t' P) (fun P Q => Subtype.ext (hom T t' P Q))

include hom in
theorem pushAlong_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.mul t' P Q) = L.mul (t' ≫ ψ) (pushAlong ψ u hu t' P) (pushAlong ψ u hu t' Q) :=
  Subtype.ext (hom T t' P Q)

include hom in
theorem pushAlong_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    pushAlong ψ u hu t' (L'.one t') = L.one (t' ≫ ψ) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_one (pushHom L L' ψ u hu hom t')

include hom in
theorem pushAlong_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.inv t' P) = L.inv (t' ≫ ψ) (pushAlong ψ u hu t' P) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_inv (pushHom L L' ψ u hu hom t') P

include hom in

theorem one_val_comp {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ u = (L.one (t' ≫ ψ)).1 :=
  congrArg Subtype.val (pushAlong_one L L' ψ u hu hom t')

include hom in

theorem negMor_comp : negMor f' L' ≫ u = u ≫ negMor f L := by
  have h1 : negMor f' L' ≫ u = (L.inv _ (pushAlong ψ u hu f' (idPt f'))).1 := by
    change (pushAlong ψ u hu f' (L'.inv f' (idPt f'))).1 = _
    rw [pushAlong_inv L L' ψ u hu hom]
  have h2 : u ≫ negMor f L = (L.inv (u ≫ f) (GoodReductionJacobian.schemeHomOverComp u rfl (idPt f))).1 := by
    change (GoodReductionJacobian.schemeHomOverComp u rfl (L.inv f (idPt f))).1 = _
    rw [inv_natural]
  rw [h1, h2]
  exact inv_val_congr L hu.symm _ _ (by simp [idPt])

include hom in

theorem addMor_comp :
    addMor f' L' ≫ u = pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ addMor f L := by
  have lhs := hom _ (pullback.fst f' f' ≫ f') ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩
  have rhs := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ pullback.fst f f ≫ f)
      (pullback.map f' f' f f u u ψ hu.symm hu.symm) rfl ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
  rw [addMor, addMor, lhs, rhs]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst_assoc, hu]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_snd]

include hom in
theorem nonempty_mumfordBundleIso (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.map f' f' f f u u ψ hu.symm hu.symm)).obj (mumfordBundle f L 𝓛)) := by
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have hadd : addMor f' L' ≫ u = pp ≫ addMor f L := addMor_comp L L' ψ u hu hom
  have hfst : pullback.fst f' f' ≫ u = pp ≫ pullback.fst f f := by simp only [pp, pullback.lift_fst]
  have hsnd : pullback.snd f' f' ≫ u = pp ≫ pullback.snd f f := by simp only [pp, pullback.lift_snd]
  obtain ⟨D⟩ := hinv.pullback_dual_monoidalV2 u
  let J1 : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (addMor f' L') u).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hadd).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pp (addMor f L)).app 𝓛).symm
  let J2 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.fst f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.fst f f)).app _).symm
  let J3 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.snd f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hsnd).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.snd f f)).app _).symm
  exact ⟨(J1 ⊗ᵢ (J2 ⊗ᵢ J3)) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso pp _ _).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso pp _ _).symm⟩

end Hom

end E24D4
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat.E24D4"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat.E24D4"

open E24D4 in

theorem solution
    {S W : Type u} [CommRing S] [CommRing W] [Algebra S W] [Module.FaithfullyFlat S W]
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of W)} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (L' : RelativeGroupLaw W f')
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of W)) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback g).obj 𝓛)) :
    KernelIsTwoTorsion f L 𝓛 := by
  classical
  intro R _ t x
  let ι : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S W))
  have hw : g ≫ f = f' ≫ ι := hg.w
  have hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of W)) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ ι)
          ⟨P.1 ≫ g, by rw [Category.assoc, hw, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hw, ← Category.assoc, Q.2]⟩).1 :=
    fun T t' P Q => hmul t' P Q

  obtain ⟨τ, hτ⟩ : ∃ τ : S →+* R, Spec.map (CommRingCat.ofHom τ) = t :=
    ⟨(Spec.preimage t).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  letI : Algebra S R := τ.toAlgebra
  let R' : Type u := R ⊗[S] W
  let u : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of W) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := S) (A := R) (B := W)).toRingHom)
  have hbase : t' ≫ ι = u ≫ t := by
    have hc : (Algebra.TensorProduct.includeRight (R := S) (A := R) (B := W)).toRingHom.comp (algebraMap S W) =
        (algebraMap R R').comp τ := by
      rw [← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]; rfl
    calc t' ≫ ι = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := S) (A := R) (B := W)).toRingHom.comp
            (algebraMap S W))) := by rw [CommRingCat.ofHom_comp, Spec.map_comp]
      _ = Spec.map (CommRingCat.ofHom ((algebraMap R R').comp τ)) := by rw [hc]
      _ = u ≫ t := by rw [CommRingCat.ofHom_comp, Spec.map_comp, hτ]

  have hff : (CommRingCat.ofHom (algebraMap R R')).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]; infer_instance
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr hff
  haveI : Flat u := hflat
  haveI : Surjective u := hsurj
  haveI : Epi u := Flat.epi_of_flat_of_surjective u

  have hxt : (u ≫ x.1) ≫ f = t' ≫ ι := by rw [Category.assoc, x.2, hbase]
  let x' : SchemeHomOver t' f' := ⟨hg.lift (u ≫ x.1) t' hxt, hg.lift_snd _ _ _⟩
  have hx' : x'.1 ≫ g = u ≫ x.1 := hg.lift_fst _ _ _

  let ux : SchemeHomOver (u ≫ t) f := ⟨u ≫ x.1, by rw [Category.assoc, x.2]⟩

  have hm : u ≫ (L.mul t x x).1 = (L.mul (u ≫ t) ux ux).1 :=
    congrArg Subtype.val (L.mul_natural t (u ≫ t) u rfl x x)
  have ho : u ≫ (L.one t).1 = (L.one (u ≫ t)).1 :=
    congrArg Subtype.val (L.one_natural t (u ≫ t) u rfl)
  have eM : (L'.mul t' x' x').1 ≫ g = (L.mul (u ≫ t) ux ux).1 := by
    rw [hom _ t' x' x']
    exact mul_val_congr L hbase _ _ _ _ (by simp [hx', ux]) (by simp [hx', ux])
  have eO : (L'.one t').1 ≫ g = (L.one (u ≫ t)).1 := by
    rw [one_val_comp L L' ι g hw hom t']
    exact one_val_congr L hbase
  have hRHS : (L'.mul t' x' x' = L'.one t') ↔ (u ≫ (L.mul t x x).1 = u ≫ (L.one t).1) := by
    constructor
    · intro h2
      rw [hm, ho, ← eM, ← eO, h2]
    · intro h2
      apply Subtype.ext
      apply hg.hom_ext
      · rw [eM, eO, ← hm, ← ho, h2]
      · rw [(L'.mul t' x' x').2, (L'.one t').2]

  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f g g ι hw.symm hw.symm

  let j : pullback f' t' ⟶ pullback f t :=
    pullback.lift (pullback.fst f' t' ≫ g) (pullback.snd f' t' ≫ u)
      (by rw [Category.assoc, Category.assoc, hw, ← hbase, pullback.condition_assoc])
  have hj2 : j ≫ pullback.snd f t = pullback.snd f' t' ≫ u := pullback.lift_snd _ _ _
  have hslice : j ≫ sliceAt f x = sliceAt f' x' ≫ pp := by
    apply pullback.hom_ext
    · simp only [sliceAt, j, pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [sliceAt, j, pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hx']

  have hkc : pullback.fst f (u ≫ t) ≫ f = (pullback.snd f (u ≫ t) ≫ t') ≫ ι := by
    rw [Category.assoc, hbase, pullback.condition]
  let k : pullback f (u ≫ t) ⟶ pullback f' t' :=
    pullback.lift (hg.lift (pullback.fst f (u ≫ t)) (pullback.snd f (u ≫ t) ≫ t') hkc) (pullback.snd f (u ≫ t))
      (hg.lift_snd _ _ _)
  have hk2 : k ≫ pullback.snd f' t' = pullback.snd f (u ≫ t) ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact pullback.lift_snd _ _ _
  have hkslice : k ≫ sliceAt f' x' ≫ pp = sliceAt f ux := by
    apply pullback.hom_ext
    · simp only [sliceAt, k, pp, ux, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hg.lift_fst]
    · simp only [sliceAt, k, pp, ux, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hx']
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ι g hw hom 𝓛 h𝓛

  have hK : Nonempty ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) ≅
      (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback g).obj 𝓛))) :=
    ⟨(Scheme.Modules.pullbackComp j (sliceAt f x)).app _ ≪≫ (Scheme.Modules.pullbackCongr hslice).app _ ≪≫
      ((Scheme.Modules.pullbackComp (sliceAt f' x') pp).app _).symm ≪≫
      (Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso.symm⟩

  have hK' : Nonempty ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback (sliceAt f' x')).obj
      (mumfordBundle f' L' ((Scheme.Modules.pullback g).obj 𝓛))) ≅
      (Scheme.Modules.pullback (sliceAt f ux)).obj (mumfordBundle f L 𝓛)) :=
    ⟨(Scheme.Modules.pullback k).mapIso ((Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso) ≪≫
      ((Scheme.Modules.pullbackComp k (sliceAt f' x')).app _) ≪≫
      (Scheme.Modules.pullbackComp (k ≫ sliceAt f' x') pp).app _ ≪≫
      (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact hkslice)).app _⟩
  constructor
  ·
    intro H
    apply Subtype.ext
    rw [← cancel_epi u]
    refine hRHS.mp ((h R' t' x').mp ?_)
    have H1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f' t') j u hj2 H
    obtain ⟨e⟩ := hK
    have E := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.snd f' t')
    exact E.trans (locIsoOnBase_of_iso _ e.symm)
      (E.trans H1 (locIsoOnBase_of_iso _ (Scheme.Modules.pullbackTensorUnitObjIso j)))
  ·
    intro heq
    have H2 : LocIsoOnBase (pullback.snd f' t')
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback g).obj 𝓛))) (𝟙_ _) :=
      (h R' t' x').mpr (hRHS.mpr (by rw [heq]))

    have H3 : LocIsoOnBase (pullback.snd f (u ≫ t))
        ((Scheme.Modules.pullback (sliceAt f ux)).obj (mumfordBundle f L 𝓛)) (𝟙_ _) := by
      have H1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f (u ≫ t)) k (𝟙 _) hk2 H2
      obtain ⟨e⟩ := hK'
      have E := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.snd f (u ≫ t))
      exact E.trans (locIsoOnBase_of_iso _ e.symm)
        (E.trans H1 (locIsoOnBase_of_iso _ (Scheme.Modules.pullbackTensorUnitObjIso k)))

    haveI : IsProper f := hA.proper
    have hAR : AbelianSchemePropertyBundle R (pullback.snd f t) := hA.of_isPullback (IsPullback.of_hasPullback f t)

    let jR : pullback f (u ≫ t) ⟶ pullback f t :=
      pullback.lift (pullback.fst f (u ≫ t)) (pullback.snd f (u ≫ t) ≫ u) (by rw [pullback.condition, Category.assoc])
    have hjR : IsPullback jR (pullback.snd f (u ≫ t)) (pullback.snd f t) u :=
      IsPullback.of_right (by
        have := IsPullback.of_hasPullback f (u ≫ t)
        rwa [← show jR ≫ pullback.fst f t = pullback.fst f (u ≫ t) from pullback.lift_fst _ _ _] at this)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f t)
    have hjRslice : jR ≫ sliceAt f x = sliceAt f ux := by
      apply pullback.hom_ext
      · simp only [sliceAt, jR, ux, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [sliceAt, jR, ux, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

    have hΛ : Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) :=
      (h𝓛.pullback _).tensor_monoidalV2
        (((Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).1.pullback _).tensor_monoidalV2
          ((Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).1.pullback _))
    have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) :=
      hΛ.pullback _
    have h1 : Scheme.Modules.IsInvertible (𝟙_ (pullback f t).Modules) := Scheme.Modules.isInvertible_unit _

    have H4 : LocIsoOnBase (pullback.snd f (u ≫ t))
        ((Scheme.Modules.pullback jR).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)))
        ((Scheme.Modules.pullback jR).obj (𝟙_ (pullback f t).Modules)) := by
      have E := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.snd f (u ≫ t))
      refine E.trans (locIsoOnBase_of_iso _ ((Scheme.Modules.pullbackComp jR (sliceAt f x)).app _ ≪≫
        (Scheme.Modules.pullbackCongr hjRslice).app _)) (E.trans H3 (locIsoOnBase_of_iso _ ?_))
      exact (Scheme.Modules.pullbackTensorUnitObjIso jR).symm

    have hH0 : ∀ (T : Type u) [CommRing T] [Algebra R T],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd (pullback.snd f t) (Scheme.TwoAffineOpenCover.specMap R T)) ⊤
        Function.Bijective (algebraMap T Γ(pullback (pullback.snd f t) (Scheme.TwoAffineOpenCover.specMap R T), ⊤)) := by
      intro T _ _
      have hb := hAR.bijective_specIso_inv_comp_appTop_of_isPullback (algebraMap R T)
        (pullback.snd (pullback.snd f t) (Scheme.TwoAffineOpenCover.specMap R T))
        (pullback.fst (pullback.snd f t) (Scheme.TwoAffineOpenCover.specMap R T))
        (IsPullback.of_hasPullback _ _)
      convert hb using 2
      ext r
      rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE]
      rfl
    exact AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated R' (pullback.snd f t)
      (pullback.snd f (u ≫ t)) jR hjR hH0 _ _ hN h1 H4

end S_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat (solution)
