-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e7f2c9b8-2567-5e63-8181-78620233d416

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
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

namespace P2mSeesawAffineRep

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

def isoUnitOfIsoUnit (N : X.Modules)
    (e : (Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B) ≅
      SheafOfModules.unit (XBC c B C).ringCatSheaf) :
    NB c N C ≅ SheafOfModules.unit (XB c C).ringCatSheaf :=
  isoUnitOfPullbackIsoUnit (θ c B C) (NB c N C) ((μ c B C N).symm ≪≫ e)

def isoUnitOfIsoUnit' (N : X.Modules) (e : NB c N C ≅ SheafOfModules.unit (XB c C).ringCatSheaf) :
    (Scheme.Modules.pullback (Limits.pullback.fst (sB c B) (specMap B C))).obj (NB c N B) ≅
      SheafOfModules.unit (XBC c B C).ringCatSheaf :=
  μ c B C N ≪≫ (Scheme.Modules.pullback (θ c B C).hom).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _

end Tower

section LIO

variable {X X' T T' : Scheme.{u}}

abbrev LIO (q : X ⟶ T) (M : X.Modules) : Prop :=
  Scheme.Modules.LocallyIsoOver q M (SheafOfModules.unit X.ringCatSheaf)

theorem lio_of_iso {q : X ⟶ T} {M M' : X.Modules} (e : M ≅ M') (h : LIO q M) : LIO q M' :=
  (Scheme.Modules.LocallyIsoOver.of_iso q e.symm).trans h

def restrictIsoOfMapsTo (g : X' ⟶ X) (M : X.Modules) (V : X.Opens) (W : X'.Opens)
    (hWV : ∀ x : X', x ∈ W → g x ∈ V)
    (e : (Scheme.Modules.pullback V.ι).obj M ≅ (Scheme.Modules.pullback V.ι).obj (SheafOfModules.unit X.ringCatSheaf)) :
    (Scheme.Modules.pullback W.ι).obj ((Scheme.Modules.pullback g).obj M) ≅ (Scheme.Modules.pullback W.ι).obj (SheafOfModules.unit X'.ringCatSheaf) :=
  have hrange : Set.range (W.ι ≫ g) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hWV _ x.2
  let l := IsOpenImmersion.lift V.ι (W.ι ≫ g) hrange
  (Scheme.Modules.pullbackComp W.ι g).app M ≪≫
    isoUnitOfFac l V.ι (W.ι ≫ g) (IsOpenImmersion.lift_fac _ _ _) M (e ≪≫ Scheme.Modules.pullbackUnitIso V.ι) ≪≫
      (Scheme.Modules.pullbackUnitIso W.ι).symm

theorem lio_precomp (q : X ⟶ T) (g : X' ⟶ X) (M : X.Modules) (h : LIO q M) : LIO (g ≫ q) ((Scheme.Modules.pullback g).obj M) := by
  intro τ
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  refine ⟨U, hτ, ⟨restrictIsoOfMapsTo g M (q ⁻¹ᵁ U) ((g ≫ q) ⁻¹ᵁ U) (fun x hx => ?_) e⟩⟩
  change (g ≫ q) x ∈ U at hx
  rwa [Scheme.Hom.comp_apply] at hx

theorem lio_baseChange (q : X ⟶ T) (z : T' ⟶ T) (M : X.Modules) (h : LIO q M) :
    LIO (Limits.pullback.snd q z) ((Scheme.Modules.pullback (Limits.pullback.fst q z)).obj M) := by
  intro τ'
  obtain ⟨U, hτ, ⟨e⟩⟩ := h (z τ')
  refine ⟨z ⁻¹ᵁ U, hτ, ⟨restrictIsoOfMapsTo _ M (q ⁻¹ᵁ U) _ (fun x hx => ?_) e⟩⟩
  change (Limits.pullback.snd q z) x ∈ z ⁻¹ᵁ U at hx
  change q (Limits.pullback.fst q z x) ∈ U
  rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
  exact hx

theorem exists_iso_of_openImmersion (q : X ⟶ T) (q' : X' ⟶ T') (j : X' ⟶ X) (i : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion i] (hsq : j ≫ q = q' ≫ i)
    (hsurj : ∀ x : X, q x ∈ Set.range i → x ∈ Set.range j)
    (M : X.Modules) (h : LIO q' ((Scheme.Modules.pullback j).obj M)) (τ' : T') :
    ∃ U : T.Opens, i τ' ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅
        (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  obtain ⟨U', hτ', ⟨e'⟩⟩ := h τ'
  refine ⟨i ''ᵁ U', ⟨τ', hτ', rfl⟩, ⟨?_⟩⟩

  have hrange : Set.range ((q' ⁻¹ᵁ U').ι ≫ j) = Set.range (q ⁻¹ᵁ (i ''ᵁ U')).ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      change q (j x') ∈ i ''ᵁ U'
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
      exact ⟨q' x', hx', rfl⟩
    · rintro ⟨τ'', hτ'', hx⟩
      obtain ⟨x', rfl⟩ := hsurj x ⟨τ'', hx⟩
      refine ⟨x', ?_, rfl⟩
      change q' x' ∈ U'
      have h1 : i (q' x') = i τ'' := by
        rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]; exact hx.symm
      rw [i.isOpenEmbedding.injective h1]
      exact hτ''
  let ν := IsOpenImmersion.isoOfRangeEq ((q' ⁻¹ᵁ U').ι ≫ j) (q ⁻¹ᵁ (i ''ᵁ U')).ι hrange
  have hfac : ν.inv ≫ ((q' ⁻¹ᵁ U').ι ≫ j) = (q ⁻¹ᵁ (i ''ᵁ U')).ι := by
    rw [Iso.inv_comp_eq, IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact isoUnitOfFac ν.inv ((q' ⁻¹ᵁ U').ι ≫ j) _ hfac M
      (((Scheme.Modules.pullbackComp (q' ⁻¹ᵁ U').ι j).app M).symm ≪≫ e' ≪≫ Scheme.Modules.pullbackUnitIso _) ≪≫
    (Scheme.Modules.pullbackUnitIso _).symm

end LIO

section Falg

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) (N : X.Modules)

abbrev Falg (B : Type u) [CommRing B] [Algebra A B] : Prop := LIO (sB c B) (NB c N B)

theorem θ_inv_snd (B C : Type u) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] :
    (θ c B C).inv ≫ Limits.pullback.snd (sB c B) (specMap B C) = sB c C := by
  rw [Iso.inv_comp_eq, θ_hom_snd]

def invHomIso (B C : Type u) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] (M : (XB c C).Modules) :
    (Scheme.Modules.pullback (θ c B C).inv).obj ((Scheme.Modules.pullback (θ c B C).hom).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp (θ c B C).inv (θ c B C).hom).app M ≪≫
    (Scheme.Modules.pullbackCongr (θ c B C).inv_hom_id).app M ≪≫ (Scheme.Modules.pullbackId _).app M

theorem falg_of_tower (B C : Type u) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] (h : Falg c N B) : Falg c N C := by
  have h1 := lio_baseChange (sB c B) (specMap B C) (NB c N B) h
  have h2 := lio_precomp _ (θ c B C).inv _ h1
  rw [θ_inv_snd] at h2
  exact lio_of_iso ((Scheme.Modules.pullback (θ c B C).inv).mapIso (μ c B C N) ≪≫ invHomIso c B C _) h2

theorem falg_of_cover (B : Type u) [CommRing B] [Algebra A B] {ι : Type*} (h : ι → A)
    (hcov : ∀ 𝔮 : PrimeSpectrum B, ∃ i, algebraMap A B (h i) ∉ 𝔮.asIdeal)
    (hloc : ∀ i, Falg c N (Localization.Away (algebraMap A B (h i)))) : Falg c N B := by
  intro τ
  obtain ⟨i, hi⟩ := hcov τ
  set g := algebraMap A B (h i)
  set C := Localization.Away g
  haveI : IsOpenImmersion (specMap B C) := IsOpenImmersion.of_isLocalization g
  let fst' := Limits.pullback.fst (sB c B) (specMap B C)
  let j : XB c C ⟶ XB c B := (θ c B C).inv ≫ fst'
  have hsq : j ≫ sB c B = sB c C ≫ specMap B C := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, θ_inv_snd]
  have hsurj : ∀ x : XB c B, sB c B x ∈ Set.range (specMap B C) → x ∈ Set.range j := by
    intro x hx
    have hx' : x ∈ Set.range fst' := by rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨y, rfl⟩ := hx'
    refine ⟨(θ c B C).hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  have hj : LIO (sB c C) ((Scheme.Modules.pullback j).obj (NB c N B)) := by
    refine lio_of_iso ?_ (hloc i)
    exact ((invHomIso c B C _).symm ≪≫ (Scheme.Modules.pullback (θ c B C).inv).mapIso (μ c B C N).symm) ≪≫
      (Scheme.Modules.pullbackComp (θ c B C).inv fst').app (NB c N B)

  have hτ : τ ∈ Set.range (specMap B C) := by
    change τ ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap B C))).base
    rw [Spec.map_base]
    change τ ∈ Set.range (PrimeSpectrum.comap (algebraMap B C))
    rw [PrimeSpectrum.localization_away_comap_range C g]
    exact hi
  obtain ⟨τ', rfl⟩ := hτ
  obtain ⟨U, hU, hiso⟩ := exists_iso_of_openImmersion (sB c B) (sB c C) j (specMap B C) hsq hsurj (NB c N B) hj τ'
  exact ⟨U, hU, hiso⟩

end Falg

section Glue

variable {A : Type u} [CommRing A]

theorem map_le_of_map_quotient_eq_bot {C : Type u} [CommRing C] [Algebra A C] (J J' : Ideal A)
    (h : J.map (algebraMap A (C ⧸ J'.map (algebraMap A C))) = ⊥) :
    J.map (algebraMap A C) ≤ J'.map (algebraMap A C) := by
  rw [IsScalarTower.algebraMap_eq A C (C ⧸ J'.map (algebraMap A C)), ← Ideal.map_map, Ideal.Quotient.algebraMap_eq,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h
  exact h

theorem exists_pow_mul_mem_of_mem_map (g : A) (J : Ideal A) (x : A)
    (hx : algebraMap A (Localization.Away g) x ∈ J.map (algebraMap A (Localization.Away g))) :
    ∃ n : ℕ, g ^ n * x ∈ J := by
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g)] at hx
  obtain ⟨⟨⟨a, ha⟩, ⟨_, m, rfl⟩⟩, hax⟩ := hx
  change algebraMap A (Localization.Away g) x * algebraMap A _ (g ^ m) = algebraMap A _ a at hax
  rw [← map_mul, IsLocalization.eq_iff_exists (Submonoid.powers g)] at hax
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := hax
  change g ^ t * (x * g ^ m) = g ^ t * a at ht
  refine ⟨t + m, ?_⟩
  have : g ^ (t + m) * x = g ^ t * a := by rw [← ht]; ring
  rw [this]
  exact J.mul_mem_left _ ha

theorem mem_map_of_pow_mul_mem (g : A) (J : Ideal A) (x : A) (n : ℕ) (hx : g ^ n * x ∈ J) :
    algebraMap A (Localization.Away g) x ∈ J.map (algebraMap A (Localization.Away g)) := by
  have hu : IsUnit (algebraMap A (Localization.Away g) (g ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow n
  have h1 : algebraMap A (Localization.Away g) (g ^ n * x) ∈ J.map (algebraMap A (Localization.Away g)) :=
    Ideal.mem_map_of_mem _ hx
  rw [map_mul] at h1
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1

end Glue

section GlueMain

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) (N : X.Modules)

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

theorem map_eq_bot_iff' {B : Type u} [CommRing B] [Algebra A B] (J : Ideal A) :
    J.map (algebraMap A B) = ⊥ ↔ ∀ j ∈ J, algebraMap A B j = 0 := by
  rw [Ideal.map, Ideal.span_eq_bot]
  simp

theorem exists_ideal_repr
    (loc : ∀ 𝔭 : PrimeSpectrum A, ∃ (h : A) (J : Ideal A), h ∉ 𝔭.asIdeal ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B h) →
        (Falg c N B ↔ J.map (algebraMap A B) = ⊥)) :
    ∃ I : Ideal A, ∀ (B : Type u) [CommRing B] [Algebra A B], Falg c N B ↔ I.map (algebraMap A B) = ⊥ := by
  classical
  choose hf Jf hnot hrep using loc

  have hspan : (1 : A) ∈ Ideal.span (Set.range hf) := by
    by_contra h1
    have hne : Ideal.span (Set.range hf) ≠ ⊤ := fun htop => h1 (htop ▸ Submodule.mem_top)
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hnot ⟨𝔪, h𝔪.isPrime⟩ (hle (Ideal.subset_span ⟨⟨𝔪, h𝔪.isPrime⟩, rfl⟩))
  obtain ⟨S, hSsub, hS1⟩ := Submodule.mem_span_finite_of_mem_span hspan
  have hpr : ∀ g : S, ∃ 𝔭 : PrimeSpectrum A, hf 𝔭 = g.1 := fun g => hSsub g.2
  choose pr hpr using hpr

  let hh : S → A := fun i => i.1
  let JJ : S → Ideal A := fun i => Jf (pr i)
  have rep : ∀ (i : S) (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B (hh i)) →
      (Falg c N B ↔ (JJ i).map (algebraMap A B) = ⊥) := by
    intro i B _ _ hu
    exact hrep (pr i) B (by rw [hpr]; exact hu)
  have hcovB : ∀ (B : Type u) [CommRing B] [Algebra A B] (𝔮 : PrimeSpectrum B), ∃ i : S, algebraMap A B (hh i) ∉ 𝔮.asIdeal := by
    intro B _ _ 𝔮
    by_contra hall
    push Not at hall
    have hle : Ideal.span (S : Set A) ≤ 𝔮.asIdeal.comap (algebraMap A B) :=
      Ideal.span_le.mpr fun g hg => hall ⟨g, hg⟩
    exact 𝔮.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hle hS1))

  have overlap : ∀ i k : S,
      (JJ i).map (algebraMap A (Localization.Away (hh i * hh k))) ≤
        (JJ k).map (algebraMap A (Localization.Away (hh i * hh k))) := by
    intro i k
    set Aik := Localization.Away (hh i * hh k)
    have hu : IsUnit (algebraMap A Aik (hh i * hh k)) := IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul, IsUnit.mul_iff] at hu
    set C' := Aik ⧸ (JJ k).map (algebraMap A Aik)
    have huC : ∀ x : A, IsUnit (algebraMap A Aik x) → IsUnit (algebraMap A C' x) := fun x hx => by
      rw [IsScalarTower.algebraMap_apply A Aik C']; exact RingHom.isUnit_map _ hx
    have hk : (JJ k).map (algebraMap A C') = ⊥ := by
      rw [IsScalarTower.algebraMap_eq A Aik C', ← Ideal.map_map, Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self]
    have hF : Falg c N C' := (rep k C' (huC _ hu.2)).mpr hk
    have hi : (JJ i).map (algebraMap A C') = ⊥ := (rep i C' (huC _ hu.1)).mp hF
    exact map_le_of_map_quotient_eq_bot _ _ hi

  let I : Ideal A := ⨅ i : S, ((JJ i).map (algebraMap A (Localization.Away (hh i)))).comap (algebraMap A _)
  refine ⟨I, fun B _ _ => ⟨fun hF => ?_, fun hI => ?_⟩⟩
  ·
    rw [map_eq_bot_iff']
    intro a ha
    apply eq_zero_of_forall_prime
    intro 𝔮
    obtain ⟨i, hi⟩ := hcovB B 𝔮
    set g := algebraMap A B (hh i)
    set Bg := Localization.Away g
    refine ⟨g, hi, ?_⟩
    have huBg : IsUnit (algebraMap A Bg (hh i)) := by
      rw [IsScalarTower.algebraMap_apply A B Bg]; exact IsLocalization.Away.algebraMap_isUnit g
    have hFg : Falg c N Bg := falg_of_tower c N B Bg hF
    have hJ : (JJ i).map (algebraMap A Bg) = ⊥ := (rep i Bg huBg).mp hFg
    have ha_i : algebraMap A (Localization.Away (hh i)) a ∈ (JJ i).map (algebraMap A _) := (Ideal.mem_iInf.mp ha) i
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_mem_map (hh i) (JJ i) a ha_i
    have h0 : algebraMap A Bg (hh i ^ n * a) = 0 := by
      rw [← Ideal.mem_bot, ← hJ]
      exact Ideal.mem_map_of_mem _ hn
    rw [IsScalarTower.algebraMap_apply A B Bg, IsLocalization.map_eq_zero_iff (Submonoid.powers g)] at h0
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := h0
    refine ⟨m + n, ?_⟩
    change g ^ m * algebraMap A B (hh i ^ n * a) = 0 at hm
    rw [map_mul, map_pow] at hm
    rw [pow_add, mul_assoc]
    exact hm
  ·
    refine falg_of_cover c N B hh (hcovB B) fun i => ?_
    set Bi := Localization.Away (algebraMap A B (hh i))
    have huBi : IsUnit (algebraMap A Bi (hh i)) := by
      rw [IsScalarTower.algebraMap_apply A B Bi]; exact IsLocalization.Away.algebraMap_isUnit _
    refine (rep i Bi huBi).mpr ?_
    rw [map_eq_bot_iff']
    intro j hj

    have hk : ∀ k : S, ∃ nk : ℕ, ∀ n, nk ≤ n → algebraMap A (Localization.Away (hh k)) (hh i ^ n * j) ∈
        (JJ k).map (algebraMap A (Localization.Away (hh k))) := by
      intro k
      have h1 : algebraMap A (Localization.Away (hh i * hh k)) j ∈ (JJ k).map (algebraMap A _) :=
        overlap i k (Ideal.mem_map_of_mem _ hj)
      obtain ⟨nk, hnk⟩ := exists_pow_mul_mem_of_mem_map _ _ _ h1
      refine ⟨nk, fun n hn => mem_map_of_pow_mul_mem (hh k) (JJ k) _ nk ?_⟩
      have : hh k ^ nk * (hh i ^ n * j) = hh i ^ (n - nk) * ((hh i * hh k) ^ nk * j) := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [Nat.add_sub_cancel_left, mul_pow, pow_add]; ring
      rw [this]
      exact Ideal.mul_mem_left _ _ hnk
    choose nk hnk using hk
    let n := Finset.univ.sup nk
    have hmem : hh i ^ n * j ∈ I := Ideal.mem_iInf.mpr fun k => hnk k n (Finset.le_sup (Finset.mem_univ k))
    have h0 : algebraMap A B (hh i ^ n * j) = 0 := by
      rw [← Ideal.mem_bot, ← hI]; exact Ideal.mem_map_of_mem _ hmem
    have h1 : algebraMap A Bi (hh i ^ n * j) = 0 := by
      rw [IsScalarTower.algebraMap_apply A B Bi, h0, map_zero]
    rw [map_mul, map_pow] at h1
    exact (huBi.pow n).mul_right_eq_zero.mp h1

end GlueMain

section TestSchemes

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) (N : X.Modules)

abbrev F {T' : Scheme.{u}} (ψ : T' ⟶ Spec (.of A)) : Prop :=
  LIO (Limits.pullback.snd c ψ) ((Scheme.Modules.pullback (Limits.pullback.fst c ψ)).obj N)

theorem F_comp {T' T'' : Scheme.{u}} (ψ : T' ⟶ Spec (.of A)) (z : T'' ⟶ T') (h : F c N ψ) : F c N (z ≫ ψ) := by
  have h1 := lio_baseChange (Limits.pullback.snd c ψ) z _ h
  let π := pullbackLeftPullbackSndIso c ψ z
  have h2 := lio_precomp _ π.inv _ h1
  have hsnd : π.inv ≫ Limits.pullback.snd (Limits.pullback.snd c ψ) z = Limits.pullback.snd c (z ≫ ψ) := by
    rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
  rw [hsnd] at h2
  refine lio_of_iso ?_ h2
  have hfst : π.inv ≫ Limits.pullback.fst (Limits.pullback.snd c ψ) z ≫ Limits.pullback.fst c ψ =
      Limits.pullback.fst c (z ≫ ψ) := pullbackLeftPullbackSndIso_inv_fst c ψ z
  exact (Scheme.Modules.pullback π.inv).mapIso ((Scheme.Modules.pullbackComp _ _).app N) ≪≫
    (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr hfst).app N

theorem fromSpec_comp {T' : Scheme.{u}} (ψ : T' ⟶ Spec (.of A)) (W : T'.Opens) (hW : IsAffineOpen W) :
    letI := algebraOfHom ψ W
    hW.fromSpec ≫ ψ = specMap A Γ(T', W) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec ψ (isAffineOpen_top _) hW (le_top : W ≤ ψ ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm

theorem falg_of_F {T' : Scheme.{u}} (ψ : T' ⟶ Spec (.of A)) (h : F c N ψ) (W : T'.Opens) (hW : IsAffineOpen W) :
    letI := algebraOfHom ψ W
    Falg c N Γ(T', W) := by
  letI := algebraOfHom ψ W
  have h1 := F_comp c N ψ hW.fromSpec h
  rw [fromSpec_comp] at h1
  exact h1

theorem F_iff_of_repr (I : Ideal A)
    (hI : ∀ (B : Type u) [CommRing B] [Algebra A B], Falg c N B ↔ I.map (algebraMap A B) = ⊥)
    {T' : Scheme.{u}} (ψ : T' ⟶ Spec (.of A)) :
    (∃ z : T' ⟶ Spec (.of (A ⧸ I)), z ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))) = ψ) ↔ F c N ψ := by
  constructor
  · rintro ⟨z, rfl⟩
    apply F_comp
    change Falg c N (A ⧸ I)
    rw [hI, Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self]
  · intro hF

    let φ : A →+* Γ(T', ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ ψ.appTop).hom
    have hφ : ∀ a ∈ I, φ a = 0 := by
      intro a ha
      apply TopCat.Sheaf.eq_of_locally_eq' T'.sheaf (fun W : T'.affineOpens => (W : T'.Opens)) ⊤
        (fun W => homOfLE le_top) (by rw [iSup_affineOpens_eq_top])
      intro W
      change T'.presheaf.map (homOfLE (le_top : (W : T'.Opens) ≤ ⊤)).op (φ a) =
        T'.presheaf.map (homOfLE (le_top : (W : T'.Opens) ≤ ⊤)).op 0
      rw [map_zero]
      letI := algebraOfHom ψ W
      have h1 : Falg c N Γ(T', W) := falg_of_F c N ψ hF W W.2
      rw [hI, map_eq_bot_iff'] at h1
      have h2 := h1 a ha
      rw [algebraMap_algebraOfHom] at h2
      change (ψ.app ⊤ ≫ T'.presheaf.map (homOfLE _).op).hom _ = 0 at h2
      exact h2
    let φ' : A ⧸ I →+* Γ(T', ⊤) := Ideal.Quotient.lift I φ hφ
    refine ⟨T'.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ'), ?_⟩
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.lift_comp_mk]
    change T'.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ ψ.appTop) = ψ
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end TestSchemes

section Main

theorem main {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
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
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ I : Ideal A, ∀ {T' : Scheme.{u}} (ψ : T' ⟶ Spec (CommRingCat.of A)),
      (∃ z : T' ⟶ Spec (CommRingCat.of (A ⧸ I)), z ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))) = ψ) ↔
        Scheme.Modules.LocallyIsoOver (Limits.pullback.snd c ψ)
          ((Scheme.Modules.pullback (Limits.pullback.fst c ψ)).obj N)
          (SheafOfModules.unit (Limits.pullback c ψ).ringCatSheaf) := by
  obtain ⟨I, hI⟩ := exists_ideal_repr c N (fun 𝔭 =>
    Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot c hH0 N Ninv hN hNinv
      hfib hinv 𝔭)
  exact ⟨I, fun ψ => F_iff_of_repr c N I hI ψ⟩

end Main

end P2mSeesawAffineRep

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
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
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ I : Ideal A, ∀ {T' : Scheme.{u}} (ψ : T' ⟶ Spec (CommRingCat.of A)),
      (∃ z : T' ⟶ Spec (CommRingCat.of (A ⧸ I)), z ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))) = ψ) ↔
        Scheme.Modules.LocallyIsoOver (Limits.pullback.snd c ψ)
          ((Scheme.Modules.pullback (Limits.pullback.fst c ψ)).obj N)
          (SheafOfModules.unit (Limits.pullback c ψ).ringCatSheaf) :=
  P2mSeesawAffineRep.main c hH0 N Ninv hN hNinv hfib hinv

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper (solution)
