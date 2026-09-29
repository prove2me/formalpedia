-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/57bde749-ae21-52ad-b0f4-5fc200126b0d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange
import Theorems.Thm_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace P2mSeesawLocalRep

section Notation

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A))

abbrev XB (B : Type u) [CommRing B] [Algebra A B] : Scheme.{u} := Limits.pullback c (specMap A B)

abbrev fB (B : Type u) [CommRing B] [Algebra A B] : XB c B ⟶ X := Limits.pullback.fst c (specMap A B)

abbrev sB (B : Type u) [CommRing B] [Algebra A B] : XB c B ⟶ Spec (.of B) := Limits.pullback.snd c (specMap A B)

abbrev NB (N : X.Modules) (B : Type u) [CommRing B] [Algebra A B] : (XB c B).Modules :=
  (Scheme.Modules.pullback (fB c B)).obj N

end Notation

section ModuleTools

variable {Y : Scheme.{u}}

lemma app_map {N N' : Y.Modules} (φ : N ⟶ N') {W W' : Y.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma inv_app_hom_app {N N' : Y.Modules} (e : N ≅ N') (W : Y.Opens) (n : Γ(N, W)) :
    e.inv.app W (e.hom.app W n) = n := by
  change (e.hom.app W ≫ e.inv.app W) n = n
  rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl

lemma hom_app_inv_app {N N' : Y.Modules} (e : N ≅ N') (W : Y.Opens) (n : Γ(N', W)) :
    e.hom.app W (e.inv.app W n) = n := by
  change (e.inv.app W ≫ e.hom.app W) n = n
  rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl

variable {R : Type u} [CommRing R] (π : Y ⟶ Spec (.of R))

def sectionsEquivOfIso {M N : Y.Modules} (e : M ≅ N) :
    letI := moduleSectionsOfHom π M ⊤
    letI := moduleSectionsOfHom π N ⊤
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) :=
  letI := algebraOfHom π ⊤
  letI := moduleSectionsOfHom π M ⊤
  letI := moduleSectionsOfHom π N ⊤
  { toFun := fun x => e.hom.app ⊤ x
    invFun := fun y => e.inv.app ⊤ y
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      show e.hom.app ⊤ ((algebraMap R Γ(Y, ⊤) r) • x) = (algebraMap R Γ(Y, ⊤) r) • e.hom.app ⊤ x
      exact Scheme.Modules.Hom.app_smul _ _ _
    left_inv := fun x => inv_app_hom_app e ⊤ x
    right_inv := fun y => hom_app_inv_app e ⊤ y }

variable (Y) in

def unitSectionsEquiv :
    letI := moduleSectionsOfHom π (SheafOfModules.unit Y.ringCatSheaf) ⊤
    letI := algebraOfHom π ⊤
    Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) ≃ₗ[R] Γ(Y, ⊤) :=
  letI := moduleSectionsOfHom π (SheafOfModules.unit Y.ringCatSheaf) ⊤
  letI := algebraOfHom π ⊤
  { toFun := fun x => (x : Γ(Y, ⊤))
    invFun := fun y => (y : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem algebraMap_top_eq (r : R) :
    letI := algebraOfHom π ⊤
    algebraMap R Γ(Y, ⊤) r = π.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := by
  change (π.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv r) = _
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop]
  change (Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ π ⁻¹ᵁ ⊤)).op) (π.app ⊤ _) = _
  have : (homOfLE (le_top : (⊤ : Y.Opens) ≤ π ⁻¹ᵁ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, op_id, Y.presheaf.map_id]
  rfl

def functionsEquivOfBijective (h : Function.Bijective π.appTop) :
    letI := algebraOfHom π ⊤
    Γ(Y, ⊤) ≃ₗ[R] R :=
  letI := algebraOfHom π ⊤
  (LinearEquiv.ofBijective (Algebra.linearMap R Γ(Y, ⊤)) (by
    have : (Algebra.linearMap R Γ(Y, ⊤) : R → Γ(Y, ⊤)) = π.appTop ∘ (Scheme.ΓSpecIso (.of R)).inv := by
      funext r; exact algebraMap_top_eq π r
    rw [this]
    exact h.comp (ConcreteCategory.bijective_of_isIso _))).symm

theorem isIso_unit_of_isIso {Y' : Scheme.{u}} (e : Y' ≅ Y) :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit := by
  let E : Y.Modules ≌ Y'.Modules := CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId Y).symm ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id.symm ≪≫
        (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫ Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
        Scheme.Modules.pullbackId Y')
  haveI : (Scheme.Modules.pullback e.hom).IsEquivalence := E.isEquivalence_functor
  exact (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit_isIso_of_L_fully_faithful

def isoUnitOfPullbackIsoUnit {Y' : Scheme.{u}} (θ : Y' ≅ Y) (M : Y.Modules)
    (e : (Scheme.Modules.pullback θ.hom).obj M ≅ SheafOfModules.unit Y'.ringCatSheaf) :
    M ≅ SheafOfModules.unit Y.ringCatSheaf :=
  ((Scheme.Modules.pullbackId Y).symm ≪≫ Scheme.Modules.pullbackCongr θ.inv_hom_id.symm ≪≫
      (Scheme.Modules.pullbackComp θ.inv θ.hom).symm).app M ≪≫
    (Scheme.Modules.pullback θ.inv).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso θ.inv

def isoUnitOfFac {Y' Y'' : Scheme.{u}} (l : Y'' ⟶ Y') (ι : Y' ⟶ Y) (g : Y'' ⟶ Y) (h : l ≫ ι = g)
    (M : Y.Modules) (e : (Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y'.ringCatSheaf) :
    (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y''.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr h.symm).app M ≪≫ ((Scheme.Modules.pullbackComp l ι).app M).symm ≪≫
    (Scheme.Modules.pullback l).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso l

end ModuleTools

section Tower

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A))
variable (B C : Type u) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

theorem specMap_comp : specMap B C ≫ specMap A B = specMap A C := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A B C]

abbrev XBC : Scheme.{u} := Limits.pullback (sB c B) (specMap B C)

def θ : XBC c B C ≅ XB c C :=
  pullbackLeftPullbackSndIso c (specMap A B) (specMap B C) ≪≫ pullback.congrHom rfl (specMap_comp B C)

@[reassoc]
theorem θ_hom_fst : (θ c B C).hom ≫ fB c C = Limits.pullback.fst _ _ ≫ fB c B := by
  change ((pullbackLeftPullbackSndIso c (specMap A B) (specMap B C)).hom ≫
    (pullback.congrHom rfl (specMap_comp B C)).hom) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

@[reassoc]
theorem θ_hom_snd : (θ c B C).hom ≫ sB c C = Limits.pullback.snd _ _ := by
  change ((pullbackLeftPullbackSndIso c (specMap A B) (specMap B C)).hom ≫
    (pullback.congrHom rfl (specMap_comp B C)).hom) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

theorem snd_eq : Limits.pullback.snd (sB c B) (specMap B C) = (θ c B C).hom ≫ sB c C := (θ_hom_snd c B C).symm

def μ (N : X.Modules) :
    (Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B) ≅
      (Scheme.Modules.pullback (θ c B C).hom).obj (NB c N C) :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr (θ_hom_fst c B C).symm).app N ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N).symm

theorem algebraMap_XBC (r : C) :
    letI := algebraOfHom (Limits.pullback.snd (sB c B) (specMap B C)) ⊤
    letI := algebraOfHom (sB c C) ⊤
    algebraMap C Γ(XBC c B C, ⊤) r = (θ c B C).hom.appTop (algebraMap C Γ(XB c C, ⊤) r) := by
  rw [algebraMap_top_eq, algebraMap_top_eq, snd_eq, Scheme.Hom.comp_appTop]
  rfl

def unitTop (M : (XB c C).Modules) (m : Γ(M, (⊤ : Scheme.Opens _))) : Γ((Scheme.Modules.pullback (θ c B C).hom).obj M, (⊤ : Scheme.Opens _)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (θ c B C).hom).unit.app M).app ⊤ m

theorem unitTop_add (M : (XB c C).Modules) (m m' : Γ(M, (⊤ : Scheme.Opens _))) :
    unitTop c B C M (m + m') = unitTop c B C M m + unitTop c B C M m' := map_add _ _ _

theorem unitTop_smul (M : (XB c C).Modules) (a : Γ(XB c C, (⊤ : Scheme.Opens _))) (m : Γ(M, (⊤ : Scheme.Opens _))) :
    unitTop c B C M (a • m) = (θ c B C).hom.appTop a • unitTop c B C M m :=
  Scheme.Modules.Hom.app_smul _ a m

theorem bijective_unitTop (M : (XB c C).Modules) : Function.Bijective (unitTop c B C M) := by
  haveI := isIso_unit_of_isIso (θ c B C)
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (θ c B C).hom).unit.app M) := inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackPushforwardAdjunction (θ c B C).hom).unit.app M).app ⊤)

def transfer (N : X.Modules) (m : Γ(NB c N C, (⊤ : Scheme.Opens _))) :
    Γ((Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B), (⊤ : Scheme.Opens _)) :=
  (μ c B C N).inv.app ⊤ (unitTop c B C (NB c N C) m)

theorem transfer_add (N : X.Modules) (m m' : Γ(NB c N C, (⊤ : Scheme.Opens _))) :
    transfer c B C N (m + m') = transfer c B C N m + transfer c B C N m' := by
  rw [transfer, unitTop_add, map_add]; rfl

theorem transfer_smul (N : X.Modules) (r : C) (m : Γ(NB c N C, (⊤ : Scheme.Opens _))) :
    letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤
    letI := moduleSectionsOfHom (Limits.pullback.snd (sB c B) (specMap B C))
      ((Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B)) ⊤
    transfer c B C N (r • m) = r • transfer c B C N m := by
  letI := algebraOfHom (Limits.pullback.snd (sB c B) (specMap B C)) ⊤
  letI := algebraOfHom (sB c C) ⊤
  change transfer c B C N ((algebraMap C Γ(XB c C, (⊤ : Scheme.Opens _)) r) • m) =
    (algebraMap C Γ(XBC c B C, (⊤ : Scheme.Opens _)) r) • transfer c B C N m
  rw [transfer, unitTop_smul, Scheme.Modules.Hom.app_smul, algebraMap_XBC]
  rfl

theorem bijective_transfer (N : X.Modules) : Function.Bijective (transfer c B C N) :=
  (ConcreteCategory.bijective_of_isIso ((μ c B C N).inv.app ⊤)).comp (bijective_unitTop c B C (NB c N C))

def secTransfer (N : X.Modules) :
    letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤
    letI := moduleSectionsOfHom (Limits.pullback.snd (sB c B) (specMap B C))
      ((Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B)) ⊤
    Γ(NB c N C, (⊤ : Scheme.Opens _)) ≃ₗ[C]
      Γ((Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B), (⊤ : Scheme.Opens _)) :=
  letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤
  letI := moduleSectionsOfHom (Limits.pullback.snd (sB c B) (specMap B C))
    ((Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B)) ⊤
  LinearEquiv.ofBijective
    { toFun := transfer c B C N
      map_add' := transfer_add c B C N
      map_smul' := transfer_smul c B C N }
    (bijective_transfer c B C N)

def isoUnitOfIsoUnit (N : X.Modules)
    (e : (Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B) ≅
      SheafOfModules.unit (XBC c B C).ringCatSheaf) :
    NB c N C ≅ SheafOfModules.unit (XB c C).ringCatSheaf :=
  isoUnitOfPullbackIsoUnit (θ c B C) (NB c N C) ((μ c B C N).symm ≪≫ e)

def isoUnitOfIsoUnit' (N : X.Modules) (e : NB c N C ≅ SheafOfModules.unit (XB c C).ringCatSheaf) :
    (Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B) ≅
      SheafOfModules.unit (XBC c B C).ringCatSheaf :=
  μ c B C N ≪≫ (Scheme.Modules.pullback (θ c B C).hom).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _

theorem forall_isUnit_XBC (h : ∀ t : Γ(XB c C, ⊤), t ≠ 0 → IsUnit t) :
    ∀ t : Γ(XBC c B C, ⊤), t ≠ 0 → IsUnit t := by
  intro t ht
  haveI : IsIso ((θ c B C).hom.app ⊤) := inferInstance
  have hbij : Function.Bijective ((θ c B C).hom.app ⊤) := ConcreteCategory.bijective_of_isIso _
  obtain ⟨t', rfl⟩ := hbij.2 t
  have ht' : t' ≠ 0 := by rintro rfl; exact ht (map_zero _)
  exact RingHom.isUnit_map _ (h t' ht')

end Tower

section Away

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A))
variable (B : Type u) [CommRing B] [Algebra A B] (g : B)

abbrev VB : (XB c B).Opens := sB c B ⁻¹ᵁ PrimeSpectrum.basicOpen g

theorem range_fst_away :
    Set.range (Limits.pullback.fst (sB c B) (specMap B (Localization.Away g))) = (VB c B g : Set (XB c B)) := by
  rw [Scheme.Pullback.range_fst]
  have : Set.range (specMap B (Localization.Away g)) = (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B)) := by
    change Set.range (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))).base = _
    rw [Spec.map_base]
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  rw [this]
  rfl

def ρ : XBC c B (Localization.Away g) ≅ (VB c B g : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst (sB c B) (specMap B (Localization.Away g))) (VB c B g).ι
    ((range_fst_away c B g).trans (Scheme.Opens.range_ι _).symm)

theorem ρ_hom_ι : (ρ c B g).hom ≫ (VB c B g).ι = Limits.pullback.fst (sB c B) (specMap B (Localization.Away g)) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

def isoUnitAway (N : X.Modules)
    (e : (Scheme.Modules.pullback (VB c B g).ι).obj (NB c N B) ≅ SheafOfModules.unit (VB c B g : Scheme.{u}).ringCatSheaf) :
    NB c N (Localization.Away g) ≅ SheafOfModules.unit (XB c (Localization.Away g)).ringCatSheaf :=
  isoUnitOfIsoUnit c B (Localization.Away g) N (isoUnitOfFac (ρ c B g).hom (VB c B g).ι _ (ρ_hom_ι c B g) _ e)

end Away

section Algebra

theorem ideal_eq_bot_of_annihilator_equiv {C : Type u} [CommRing C] (I : Ideal C)
    (e : I.annihilator ≃ₗ[C] C) : I = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun i hi => ?_
  have h1 : i • e.symm 1 = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_zero]
    have := (Submodule.mem_annihilator.mp (e.symm 1).2) i hi
    rwa [smul_eq_mul, mul_comm] at this
  have h2 := congrArg e h1
  rw [map_smul, LinearEquiv.apply_symm_apply, map_zero, smul_eq_mul, mul_one] at h2
  exact h2

theorem eq_zero_of_forall_prime {B : Type u} [CommRing B] (b : B)
    (h : ∀ 𝔮 : PrimeSpectrum B, ∃ g : B, g ∉ 𝔮.asIdeal ∧ ∃ n : ℕ, g ^ n * b = 0) : b = 0 := by
  let I : Ideal B := Submodule.annihilator (Submodule.span B {b})
  by_contra hb
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
    have := Submodule.mem_annihilator_span_singleton b 1 |>.mp h1
    rw [one_smul] at this
    exact hb this
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨g, hg, n, hn⟩ := h ⟨𝔪, h𝔪.isPrime⟩
  apply hg
  have hgn : g ^ n ∈ 𝔪 := hI𝔪 ((Submodule.mem_annihilator_span_singleton b (g ^ n)).mpr hn)
  exact h𝔪.isPrime.mem_of_pow_mem n hgn

theorem map_eq_bot_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) :
    J.map (algebraMap A B) = ⊥ ↔ ∀ j ∈ J, algebraMap A B j = 0 := by
  rw [Ideal.map, Ideal.span_eq_bot]
  simp

end Algebra

section Backward

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) (N : X.Modules)

theorem exists_away_iso_unit (B : Type u) [CommRing B] [Algebra A B]
    (hloc : Scheme.Modules.LocallyIsoOver (sB c B) (NB c N B) (SheafOfModules.unit (XB c B).ringCatSheaf))
    (𝔮 : PrimeSpectrum B) :
    ∃ g : B, g ∉ 𝔮.asIdeal ∧
      Nonempty (NB c N (Localization.Away g) ≅ SheafOfModules.unit (XB c (Localization.Away g)).ringCatSheaf) := by
  obtain ⟨U, h𝔮U, ⟨eU⟩⟩ := hloc 𝔮
  obtain ⟨_, ⟨g, rfl⟩, hg𝔮, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔮U U.2
  refine ⟨g, hg𝔮, ⟨?_⟩⟩
  have hle : (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of B)).Opens) ≤ U := fun x hx => hgU hx
  exact isoUnitAway c B g N
    (Scheme.Modules.LocallyIsoOver.restrict (q := sB c B) hle eU ≪≫ Scheme.Modules.pullbackUnitIso _)

variable (hH0 : ∀ (B : Type u) [CommRing B] [Algebra A B], Function.Bijective (sB c B).appTop)
include hH0

def secEquivOfIsoUnit (C : Type u) [CommRing C] [Algebra A C]
    (e : NB c N C ≅ SheafOfModules.unit (XB c C).ringCatSheaf) :
    letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤
    Γ(NB c N C, ⊤) ≃ₗ[C] C :=
  letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤
  letI := moduleSectionsOfHom (sB c C) (SheafOfModules.unit (XB c C).ringCatSheaf) ⊤
  letI := algebraOfHom (sB c C) ⊤
  sectionsEquivOfIso (sB c C) e ≪≫ₗ unitSectionsEquiv (XB c C) (sB c C) ≪≫ₗ functionsEquivOfBijective (sB c C) (hH0 C)

variable (G : CoherentBaseChange.TwoTermComplex.{u, u} A)
variable (ε : ∀ (B : Type u) [CommRing B] [Algebra A B],
  letI := moduleSectionsOfHom (sB c B) (NB c N B) ⊤
  Γ(NB c N B, ⊤) ≃ₗ[B] G.H0 B)
include ε

section WithJ

variable (h₁ : A) (J : Ideal A)
variable (hA1 : ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h₁) →
  Nonempty (G.H0 B ≃ₗ[B] (J.map (algebraMap A B)).annihilator))
include hA1

theorem map_eq_bot_of_iso_unit (C : Type u) [CommRing C] [Algebra A C] (hu : IsUnit (algebraMap A C h₁))
    (e : NB c N C ≅ SheafOfModules.unit (XB c C).ringCatSheaf) : J.map (algebraMap A C) = ⊥ := by
  obtain ⟨e1⟩ := hA1 C hu
  letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤

  exact ideal_eq_bot_of_annihilator_equiv _ (e1.symm ≪≫ₗ (ε C).symm ≪≫ₗ secEquivOfIsoUnit c N hH0 C e)

theorem map_eq_bot_of_locallyIsoOver (B : Type u) [CommRing B] [Algebra A B] (hu : IsUnit (algebraMap A B h₁))
    (hloc : Scheme.Modules.LocallyIsoOver (sB c B) (NB c N B) (SheafOfModules.unit (XB c B).ringCatSheaf)) :
    J.map (algebraMap A B) = ⊥ := by
  rw [map_eq_bot_iff]
  intro j hj
  apply eq_zero_of_forall_prime
  intro 𝔮
  obtain ⟨g, hg𝔮, ⟨eC⟩⟩ := exists_away_iso_unit c N B hloc 𝔮
  refine ⟨g, hg𝔮, ?_⟩
  have huC : IsUnit (algebraMap A (Localization.Away g) h₁) := by
    rw [IsScalarTower.algebraMap_apply A B (Localization.Away g)]
    exact RingHom.isUnit_map _ hu
  have h1 := map_eq_bot_of_iso_unit c N hH0 G ε h₁ J hA1 (Localization.Away g) huC eC
  rw [map_eq_bot_iff] at h1
  have h2 := h1 j hj
  rw [IsScalarTower.algebraMap_apply A B (Localization.Away g), IsLocalization.map_eq_zero_iff (Submonoid.powers g)]
    at h2
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := h2
  exact ⟨n, hn⟩

end WithJ

theorem exists_forall_subsingleton_of_fibreH0_eq_zero (𝔭 : PrimeSpectrum A) (h0 : G.fibreH0 𝔭 = 0) :
    ∃ h : A, h ∉ 𝔭.asIdeal ∧ ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h) →
      Scheme.Modules.LocallyIsoOver (sB c B) (NB c N B) (SheafOfModules.unit (XB c B).ringCatSheaf) →
        Subsingleton B := by
  set κ := 𝔭.asIdeal.ResidueField
  obtain ⟨h', J', h'𝔭, hA1'⟩ :=
    CoherentBaseChange.TwoTermComplex.exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one G 𝔭 (by omega)

  have hu' : IsUnit (algebraMap A κ h') := by
    rw [isUnit_iff_ne_zero, ne_eq, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    exact h'𝔭
  obtain ⟨e1⟩ := hA1' κ hu'
  haveI : Subsingleton (G.H0 κ) := by
    have h1 : Module.finrank κ (G.H0 κ) = 0 := h0
    exact Module.finrank_zero_iff.mp h1 |> fun h => h
  have hJ' : ¬ (J'.map (algebraMap A κ) = ⊥) := by
    intro hbot
    have hone : (1 : κ) ∈ (J'.map (algebraMap A κ)).annihilator := by
      rw [hbot, Submodule.annihilator_bot]; exact Submodule.mem_top
    have h2 : (⟨1, hone⟩ : (J'.map (algebraMap A κ)).annihilator) = 0 :=
      e1.symm.injective (Subsingleton.elim _ _)
    exact one_ne_zero (congrArg Subtype.val h2)
  rw [map_eq_bot_iff] at hJ'
  push Not at hJ'
  obtain ⟨j, hjJ', hj0⟩ := hJ'
  have hj𝔭 : j ∉ 𝔭.asIdeal := by
    rwa [ne_eq, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] at hj0
  refine ⟨h' * j, 𝔭.isPrime.mul_notMem h'𝔭 hj𝔭, fun B _ _ hu hloc => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hu

  have hzero : ∀ (C : Type u) [CommRing C] [Algebra A C], IsUnit (algebraMap A C h') → IsUnit (algebraMap A C j) →
      Subsingleton (G.H0 C) := by
    intro C _ _ huh huj
    obtain ⟨eC⟩ := hA1' C huh
    have htop : J'.map (algebraMap A C) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hjJ') huj
    haveI : Subsingleton (J'.map (algebraMap A C)).annihilator := by
      rw [htop]
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx := (Submodule.mem_annihilator.mp x.2) 1 Submodule.mem_top
      have hy := (Submodule.mem_annihilator.mp y.2) 1 Submodule.mem_top
      rw [smul_eq_mul, mul_one] at hx hy
      rw [hx, hy]
    exact eC.toEquiv.subsingleton

  by_contra hB
  rw [not_subsingleton_iff_nontrivial] at hB
  obtain ⟨𝔮⟩ := (inferInstance : Nonempty (PrimeSpectrum B))
  obtain ⟨g, hg𝔮, ⟨eC⟩⟩ := exists_away_iso_unit c N B hloc 𝔮
  set C := Localization.Away g
  letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤
  haveI : Subsingleton (G.H0 C) := hzero C
    (by rw [IsScalarTower.algebraMap_apply A B C]; exact RingHom.isUnit_map _ hu.1)
    (by rw [IsScalarTower.algebraMap_apply A B C]; exact RingHom.isUnit_map _ hu.2)
  haveI : Subsingleton C := ((ε C).symm ≪≫ₗ secEquivOfIsoUnit c N hH0 C eC).symm.toEquiv.subsingleton
  have h1 : (algebraMap B C 1) = 0 := Subsingleton.elim _ _
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g)] at h1
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := h1
  rw [mul_one] at hn
  have hgn : g ^ n ∈ 𝔮.asIdeal := by
    have : (g ^ n : B) = 0 := hn
    rw [this]; exact 𝔮.asIdeal.zero_mem
  exact hg𝔮 (𝔮.isPrime.mem_of_pow_mem n hgn)

end Backward

section FieldChange

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) (N : X.Modules)

def mapAlg (K₁ K₂ : Type u) [CommRing K₁] [Algebra A K₁] [CommRing K₂] [Algebra A K₂] (φ : K₁ →ₐ[A] K₂) :
    XB c K₂ ⟶ XB c K₁ :=
  pullback.map c (specMap A K₂) c (specMap A K₁) (𝟙 X) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      rw [Category.comp_id]
      change _ = Spec.map _ ≫ Spec.map _
      have hφ : φ.toRingHom.comp (algebraMap A K₁) = algebraMap A K₂ := RingHom.ext φ.commutes
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ])

theorem mapAlg_fst (K₁ K₂ : Type u) [CommRing K₁] [Algebra A K₁] [CommRing K₂] [Algebra A K₂] (φ : K₁ →ₐ[A] K₂) :
    mapAlg c K₁ K₂ φ ≫ fB c K₁ = fB c K₂ := by
  rw [mapAlg, fB, pullback.lift_fst, Category.comp_id]

def isoUnitOfAlgHom (K₁ K₂ : Type u) [CommRing K₁] [Algebra A K₁] [CommRing K₂] [Algebra A K₂] (φ : K₁ →ₐ[A] K₂)
    (e : NB c N K₁ ≅ SheafOfModules.unit (XB c K₁).ringCatSheaf) :
    NB c N K₂ ≅ SheafOfModules.unit (XB c K₂).ringCatSheaf :=
  isoUnitOfFac (mapAlg c K₁ K₂ φ) (fB c K₁) (fB c K₂) (mapAlg_fst c K₁ K₂ φ) N e

end FieldChange

section CaseT

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A))
  [IsProper c] [Flat c] (N : X.Modules) (hN : Scheme.Modules.IsInvertible N)
variable (hH0 : ∀ (B : Type u) [CommRing B] [Algebra A B], Function.Bijective (sB c B).appTop)
variable (G : CoherentBaseChange.TwoTermComplex.{u, u} A)
variable (ε : ∀ (B : Type u) [CommRing B] [Algebra A B],
  letI := moduleSectionsOfHom (sB c B) (NB c N B) ⊤
  Γ(NB c N B, ⊤) ≃ₗ[B] G.H0 B)
include hN hH0 ε

omit [IsNoetherianRing A] [IsProper c] [Flat c] hN ε in

theorem forall_isUnit (K : Type u) [Field K] [Algebra A K] : ∀ t : Γ(XB c K, ⊤), t ≠ 0 → IsUnit t := by
  letI := algebraOfHom (sB c K) ⊤
  intro t ht
  obtain ⟨x, rfl⟩ := (functionsEquivOfBijective (sB c K) (hH0 K)).symm.surjective t
  have hx : x ≠ 0 := by rintro rfl; exact ht (map_zero _)
  change IsUnit (algebraMap K Γ(XB c K, ⊤) x)
  exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr hx)

omit [IsNoetherianRing A] in

theorem caseT_core (h₁ : A) (J : Ideal A)
    (hA1 : ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h₁) →
      Nonempty (G.H0 B ≃ₗ[B] (J.map (algebraMap A B)).annihilator))
    (B₀ : Type u) [CommRing B₀] [IsNoetherianRing B₀] [Algebra A B₀]
    (hu₁B₀ : IsUnit (algebraMap A B₀ h₁)) (hJB₀ : J.map (algebraMap A B₀) = ⊥)
    (𝔭₀ : PrimeSpectrum B₀) (K₁ : Type u) [CommRing K₁] [Algebra A K₁]
    (φ : K₁ →ₐ[A] 𝔭₀.asIdeal.ResidueField)
    (eκ : NB c N K₁ ≅ SheafOfModules.unit (XB c K₁).ringCatSheaf) :
    ∃ g : B₀, g ∉ 𝔭₀.asIdeal ∧ ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra B₀ B] [IsScalarTower A B₀ B],
      IsUnit (algebraMap B₀ B g) → Nonempty (NB c N B ≅ SheafOfModules.unit (XB c B).ringCatSheaf) := by
  let Y := XB c B₀
  let f := sB c B₀
  let P : Y.Modules := NB c N B₀
  have hP : Scheme.Modules.IsInvertible P := hN.pullback _
  letI instP := moduleSectionsOfHom f P ⊤

  have annTop : ∀ (C : Type u) [CommRing C] [Algebra A C], J.map (algebraMap A C) = ⊥ →
      ((J.map (algebraMap A C)).annihilator ≃ₗ[C] C) := by
    intro C _ _ hC
    exact (LinearEquiv.ofEq _ _ (by rw [hC, Submodule.annihilator_bot])) ≪≫ₗ Submodule.topEquiv

  obtain ⟨e1B₀⟩ := hA1 B₀ hu₁B₀
  have hsec0 : Nonempty (Γ(P, ⊤) ≃ₗ[B₀] B₀) := ⟨(ε B₀) ≪≫ₗ e1B₀ ≪≫ₗ annTop B₀ hJB₀⟩

  have hsec : ∀ (C : Type u) [CommRing C] [Algebra B₀ C],
      letI := moduleSectionsOfHom (Limits.pullback.snd f (specMap B₀ C))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap B₀ C))).obj P) ⊤
      Nonempty (Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap B₀ C))).obj P, ⊤) ≃ₗ[C] C) := by
    intro C _ _
    letI : Algebra A C := ((algebraMap B₀ C).comp (algebraMap A B₀)).toAlgebra
    haveI : IsScalarTower A B₀ C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI := moduleSectionsOfHom (sB c C) (NB c N C) ⊤
    have huC : IsUnit (algebraMap A C h₁) := by
      rw [IsScalarTower.algebraMap_apply A B₀ C]; exact RingHom.isUnit_map _ hu₁B₀
    have hJC : J.map (algebraMap A C) = ⊥ := by
      rw [IsScalarTower.algebraMap_eq A B₀ C, ← Ideal.map_map, hJB₀, Ideal.map_bot]
    obtain ⟨e1C⟩ := hA1 C huC
    exact ⟨(secTransfer c B₀ C N).symm ≪≫ₗ (ε C) ≪≫ₗ e1C ≪≫ₗ annTop C hJC⟩

  have hO : ∀ t : Γ(Limits.pullback f (specMap B₀ 𝔭₀.asIdeal.ResidueField), ⊤), t ≠ 0 → IsUnit t :=
    forall_isUnit_XBC c B₀ _ (forall_isUnit c hH0 _)
  have htriv₀ : Nonempty ((Scheme.Modules.pullback
      (Limits.pullback.fst f (specMap B₀ 𝔭₀.asIdeal.ResidueField))).obj P ≅
        SheafOfModules.unit (Limits.pullback f (specMap B₀ 𝔭₀.asIdeal.ResidueField)).ringCatSheaf) :=
    ⟨isoUnitOfIsoUnit' c B₀ _ N (isoUnitOfAlgHom c N K₁ _ φ eκ)⟩
  obtain ⟨g, hg𝔭₀, ⟨eW⟩⟩ :=
    Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv
      f P hP hsec0 hsec 𝔭₀ hO htriv₀
  refine ⟨g, hg𝔭₀, fun B _ _ _ _ hg => ⟨?_⟩⟩

  set W : Y.Opens := f ⁻¹ᵁ PrimeSpectrum.basicOpen g
  have hrange : Set.range (Limits.pullback.fst f (specMap B₀ B)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change f (Limits.pullback.fst f (specMap B₀ B) x) ∈ PrimeSpectrum.basicOpen g
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
    change g ∉ ((specMap B₀ B) (Limits.pullback.snd f (specMap B₀ B) x)).asIdeal
    have : ((specMap B₀ B) (Limits.pullback.snd f (specMap B₀ B) x)).asIdeal =
        (Limits.pullback.snd f (specMap B₀ B) x).asIdeal.comap (algebraMap B₀ B) := by
      change ((Spec.map (CommRingCat.ofHom (algebraMap B₀ B))).base _).asIdeal = _
      rw [Spec.map_base]
      rfl
    rw [this, Ideal.mem_comap]
    exact fun hmem => (Limits.pullback.snd f (specMap B₀ B) x).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem hg)
  let l := IsOpenImmersion.lift W.ι (Limits.pullback.fst f (specMap B₀ B)) hrange
  have eBC : (Scheme.Modules.pullback (Limits.pullback.fst f (specMap B₀ B))).obj P ≅
      SheafOfModules.unit (Limits.pullback f (specMap B₀ B)).ringCatSheaf :=
    isoUnitOfFac l W.ι _ (IsOpenImmersion.lift_fac _ _ _) P eW
  exact isoUnitOfIsoUnit c B₀ B N eBC

theorem caseT (𝔭 : PrimeSpectrum A)
    (htriv : Nonempty (NB c N 𝔭.asIdeal.ResidueField ≅ SheafOfModules.unit (XB c 𝔭.asIdeal.ResidueField).ringCatSheaf)) :
    ∃ (h : A) (J : Ideal A), h ∉ 𝔭.asIdeal ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h) →
        (Scheme.Modules.LocallyIsoOver (sB c B) (NB c N B) (SheafOfModules.unit (XB c B).ringCatSheaf) ↔
          J.map (algebraMap A B) = ⊥) := by
  set κ := 𝔭.asIdeal.ResidueField with hκ
  obtain ⟨eκ⟩ := htriv
  letI instκ := moduleSectionsOfHom (sB c κ) (NB c N κ) ⊤

  have hH0κ : G.H0 κ ≃ₗ[κ] κ := (ε κ).symm ≪≫ₗ secEquivOfIsoUnit c N hH0 κ eκ
  have h1 : G.fibreH0 𝔭 ≤ 1 := by
    change Module.finrank κ (G.H0 κ) ≤ 1
    rw [hH0κ.finrank_eq, Module.finrank_self]

  obtain ⟨h₁, J, h₁𝔭, hA1⟩ :=
    CoherentBaseChange.TwoTermComplex.exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one G 𝔭 h1
  have hu₁κ : IsUnit (algebraMap A κ h₁) := by
    rw [isUnit_iff_ne_zero, ne_eq, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]; exact h₁𝔭

  have hJκ : ∀ j ∈ J, algebraMap A κ j = 0 := by
    rw [← map_eq_bot_iff]
    obtain ⟨e1⟩ := hA1 κ hu₁κ
    exact ideal_eq_bot_of_annihilator_equiv _ (e1.symm ≪≫ₗ hH0κ)

  let B₀ : Type u := Localization.Away (Ideal.Quotient.mk J h₁)
  have hu₁B₀ : IsUnit (algebraMap A B₀ h₁) := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ J) B₀, Ideal.Quotient.algebraMap_eq]
    exact IsLocalization.Away.algebraMap_isUnit _
  have hJB₀ : J.map (algebraMap A B₀) = ⊥ := by
    rw [map_eq_bot_iff]
    intro j hj
    rw [IsScalarTower.algebraMap_apply A (A ⧸ J) B₀, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hj, map_zero]

  have hunit : IsUnit ((Ideal.Quotient.lift J (algebraMap A κ) hJκ) (Ideal.Quotient.mk J h₁)) := by
    rw [Ideal.Quotient.lift_mk]; exact hu₁κ
  let ψ : B₀ →+* κ := IsLocalization.Away.lift (Ideal.Quotient.mk J h₁) hunit
  have hψ : ∀ a : A, ψ (algebraMap A B₀ a) = algebraMap A κ a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A (A ⧸ J) B₀, Ideal.Quotient.algebraMap_eq]
    change IsLocalization.Away.lift _ hunit _ = _
    rw [IsLocalization.Away.lift_eq, Ideal.Quotient.lift_mk]
  let 𝔭₀ : PrimeSpectrum B₀ := ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  have hcomap : 𝔭.asIdeal = 𝔭₀.asIdeal.comap (Algebra.ofId A B₀).toRingHom := by
    change 𝔭.asIdeal = (RingHom.ker ψ).comap (algebraMap A B₀)
    rw [RingHom.comap_ker]
    have : ψ.comp (algebraMap A B₀) = algebraMap A κ := RingHom.ext hψ
    rw [this, Ideal.ker_algebraMap_residueField]
  haveI : 𝔭₀.asIdeal.IsPrime := 𝔭₀.isPrime
  let φ : κ →ₐ[A] 𝔭₀.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ 𝔭.asIdeal 𝔭₀.asIdeal (Algebra.ofId A B₀) hcomap

  obtain ⟨g, hg𝔭₀, hg⟩ := caseT_core c N hN hH0 G ε h₁ J hA1 B₀ hu₁B₀ hJB₀ 𝔭₀ κ φ eκ

  obtain ⟨⟨x, s⟩, hgs⟩ := IsLocalization.surj (Submonoid.powers (Ideal.Quotient.mk J h₁)) g
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have hgs' : g * algebraMap A B₀ h₁ ^ n = algebraMap A B₀ a := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ J) B₀, IsScalarTower.algebraMap_apply A (A ⧸ J) B₀,
      Ideal.Quotient.algebraMap_eq, ← map_pow, hn]
    exact hgs
  have ha𝔭 : a ∉ 𝔭.asIdeal := by
    intro ha
    apply hg𝔭₀
    change ψ g = 0
    have h2 := congrArg ψ hgs'
    rw [map_mul, map_pow, hψ, hψ] at h2
    have h3 : algebraMap A κ a = 0 := by
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]; exact ha
    rw [h3] at h2
    exact (mul_eq_zero.mp h2).resolve_right (pow_ne_zero n hu₁κ.ne_zero)
  refine ⟨h₁ * a, J, 𝔭.isPrime.mul_notMem h₁𝔭 ha𝔭, fun B _ _ hu => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hu
  refine ⟨map_eq_bot_of_locallyIsoOver c N hH0 G ε h₁ J hA1 B hu.1, fun hJB => ?_⟩

  rw [map_eq_bot_iff] at hJB
  have hunitB : IsUnit ((Ideal.Quotient.lift J (algebraMap A B) hJB) (Ideal.Quotient.mk J h₁)) := by
    rw [Ideal.Quotient.lift_mk]; exact hu.1
  let χ : B₀ →+* B := IsLocalization.Away.lift (Ideal.Quotient.mk J h₁) hunitB
  have hχ : ∀ a : A, χ (algebraMap A B₀ a) = algebraMap A B a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A (A ⧸ J) B₀, Ideal.Quotient.algebraMap_eq]
    change IsLocalization.Away.lift _ hunitB _ = _
    rw [IsLocalization.Away.lift_eq, Ideal.Quotient.lift_mk]
  letI : Algebra B₀ B := χ.toAlgebra
  haveI : IsScalarTower A B₀ B := IsScalarTower.of_algebraMap_eq (fun a => (hχ a).symm)
  have hχg : IsUnit (algebraMap B₀ B g) := by
    have h2 := congrArg (algebraMap B₀ B) hgs'
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
    exact isUnit_of_mul_isUnit_left (h2 ▸ hu.2)
  obtain ⟨e⟩ := hg B hχg
  exact Scheme.Modules.LocallyIsoOver.of_iso _ e

end CaseT

section Main

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) (N Ninv : X.Modules)

theorem locallyIsoOver_inv
    (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ X),
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf))
    (B : Type u) [CommRing B] [Algebra A B]
    (hloc : Scheme.Modules.LocallyIsoOver (sB c B) (NB c N B) (SheafOfModules.unit (XB c B).ringCatSheaf)) :
    Scheme.Modules.LocallyIsoOver (sB c B) (NB c Ninv B) (SheafOfModules.unit (XB c B).ringCatSheaf) := by
  intro τ
  obtain ⟨U, hτ, ⟨e⟩⟩ := hloc τ
  set V : (XB c B).Opens := sB c B ⁻¹ᵁ U
  have e1 : (Scheme.Modules.pullback (V.ι ≫ fB c B)).obj N ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
    ((Scheme.Modules.pullbackComp V.ι (fB c B)).app N).symm ≪≫ e ≪≫ Scheme.Modules.pullbackUnitIso _
  obtain ⟨e2⟩ := hinv V (V.ι ≫ fB c B) ⟨e1⟩
  exact ⟨U, hτ, ⟨(Scheme.Modules.pullbackComp V.ι (fB c B)).app Ninv ≪≫ e2 ≪≫
    (Scheme.Modules.pullbackUnitIso _).symm⟩⟩

theorem main [IsNoetherianRing A] [IsProper c] [Flat c]
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap A B)))).appTop)
    (hN : Scheme.Modules.IsInvertible N) (hNinv : Scheme.Modules.IsInvertible Ninv)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      (∃ s : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj N, ⊤), s ≠ 0) →
      (∃ t : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj Ninv, ⊤), t ≠ 0) →
        Nonempty ((Scheme.Modules.pullback
            (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj N ≅
          SheafOfModules.unit (Limits.pullback c (Spec.map (CommRingCat.ofHom (algebraMap A K)))).ringCatSheaf))
    (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ X),
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf))
    (𝔭 : PrimeSpectrum A) :
    ∃ (h : A) (J : Ideal A), h ∉ 𝔭.asIdeal ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h) →
        (Scheme.Modules.LocallyIsoOver (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap A B))))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A B))))).obj N)
            (SheafOfModules.unit
              (Limits.pullback c (Spec.map (CommRingCat.ofHom (algebraMap A B)))).ringCatSheaf) ↔
          Ideal.map (algebraMap A B) J = ⊥) := by
  set κ := 𝔭.asIdeal.ResidueField

  obtain ⟨G, -, ε, -⟩ := Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange c N hN.1
  obtain ⟨G', -, ε', -⟩ := Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange c Ninv hNinv.1
  by_cases htriv : Nonempty (NB c N κ ≅ SheafOfModules.unit (XB c κ).ringCatSheaf)
  ·
    exact caseT c N hN hH0 G (fun B _ _ => ε B) 𝔭 htriv
  ·
    have hcases : (∀ s : Γ(NB c N κ, ⊤), s = 0) ∨ (∀ t : Γ(NB c Ninv κ, ⊤), t = 0) := by
      by_contra hcon
      rw [not_or] at hcon
      push Not at hcon
      obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hcon
      exact htriv (hfib κ ⟨s, hs⟩ ⟨t, ht⟩)

    have hZ : ∃ h : A, h ∉ 𝔭.asIdeal ∧ ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h) →
        Scheme.Modules.LocallyIsoOver (sB c B) (NB c N B) (SheafOfModules.unit (XB c B).ringCatSheaf) →
          Subsingleton B := by
      rcases hcases with hs | ht
      · letI := moduleSectionsOfHom (sB c κ) (NB c N κ) ⊤
        haveI : Subsingleton Γ(NB c N κ, ⊤) := subsingleton_of_forall_eq 0 hs
        haveI : Subsingleton (G.H0 κ) := (ε κ).symm.toEquiv.subsingleton
        have h0 : G.fibreH0 𝔭 = 0 := Module.finrank_zero_of_subsingleton
        exact exists_forall_subsingleton_of_fibreH0_eq_zero c N hH0 G (fun B _ _ => ε B) 𝔭 h0
      · letI := moduleSectionsOfHom (sB c κ) (NB c Ninv κ) ⊤
        haveI : Subsingleton Γ(NB c Ninv κ, ⊤) := subsingleton_of_forall_eq 0 ht
        haveI : Subsingleton (G'.H0 κ) := (ε' κ).symm.toEquiv.subsingleton
        have h0 : G'.fibreH0 𝔭 = 0 := Module.finrank_zero_of_subsingleton
        obtain ⟨h, h𝔭, hh⟩ :=
          exists_forall_subsingleton_of_fibreH0_eq_zero c Ninv hH0 G' (fun B _ _ => ε' B) 𝔭 h0
        exact ⟨h, h𝔭, fun B _ _ hu hloc => hh B hu (locallyIsoOver_inv c N Ninv hinv B hloc)⟩
    obtain ⟨h, h𝔭, hh⟩ := hZ
    refine ⟨h, ⊤, h𝔭, fun B _ _ hu => ?_⟩
    rw [Ideal.map_top]
    constructor
    · intro hloc
      haveI := hh B hu hloc
      exact Subsingleton.elim _ _
    · intro htop
      haveI : Subsingleton B := by
        have h1 : (1 : B) ∈ (⊥ : Ideal B) := htop ▸ Submodule.mem_top
        rw [Ideal.mem_bot] at h1
        exact subsingleton_of_zero_eq_one h1.symm
      haveI : IsEmpty (PrimeSpectrum B) := inferInstance
      intro τ
      exact (IsEmpty.false (show PrimeSpectrum B from τ)).elim

end Main

end P2mSeesawLocalRep

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    [IsProper c] [Flat c]
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap A B)))).appTop)
    (N Ninv : X.Modules) (hN : Scheme.Modules.IsInvertible N) (hNinv : Scheme.Modules.IsInvertible Ninv)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      (∃ s : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj N, ⊤), s ≠ 0) →
      (∃ t : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj Ninv, ⊤), t ≠ 0) →
        Nonempty ((Scheme.Modules.pullback
            (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj N ≅
          SheafOfModules.unit (Limits.pullback c (Spec.map (CommRingCat.ofHom (algebraMap A K)))).ringCatSheaf))
    (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ X),
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf))
    (𝔭 : PrimeSpectrum A) :
    ∃ (h : A) (J : Ideal A), h ∉ 𝔭.asIdeal ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h) →
        (Scheme.Modules.LocallyIsoOver (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap A B))))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A B))))).obj N)
            (SheafOfModules.unit
              (Limits.pullback c (Spec.map (CommRingCat.ofHom (algebraMap A B)))).ringCatSheaf) ↔
          Ideal.map (algebraMap A B) J = ⊥) :=
  P2mSeesawLocalRep.main c N Ninv hH0 hN hNinv hfib hinv 𝔭

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot (solution)
