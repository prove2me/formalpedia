-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9884fd70-47c6-5f37-b274-8a0813f942a1

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
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

namespace P2mSeesawGeneralBase

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

section FT

variable {XT T : Scheme.{u}} (p : XT ⟶ T) (N : XT.Modules)

abbrev F {T' : Scheme.{u}} (ψ : T' ⟶ T) : Prop :=
  LIO (Limits.pullback.snd p ψ) ((Scheme.Modules.pullback (Limits.pullback.fst p ψ)).obj N)

theorem F_comp {T' T'' : Scheme.{u}} (ψ : T' ⟶ T) (z : T'' ⟶ T') (h : F p N ψ) : F p N (z ≫ ψ) := by
  have h1 := lio_baseChange (Limits.pullback.snd p ψ) z _ h
  let π := pullbackLeftPullbackSndIso p ψ z
  have h2 := lio_precomp _ π.inv _ h1
  have hsnd : π.inv ≫ Limits.pullback.snd (Limits.pullback.snd p ψ) z = Limits.pullback.snd p (z ≫ ψ) := by
    rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
  rw [hsnd] at h2
  refine lio_of_iso ?_ h2
  have hfst : π.inv ≫ Limits.pullback.fst (Limits.pullback.snd p ψ) z ≫ Limits.pullback.fst p ψ =
      Limits.pullback.fst p (z ≫ ψ) := pullbackLeftPullbackSndIso_inv_fst p ψ z
  exact (Scheme.Modules.pullback π.inv).mapIso ((Scheme.Modules.pullbackComp _ _).app N) ≪≫
    (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr hfst).app N

theorem F_of_openCover {T' : Scheme.{u}} (ψ : T' ⟶ T) (𝒰 : T'.OpenCover) (h : ∀ i, F p N (𝒰.f i ≫ ψ)) :
    F p N ψ := by
  intro τ'
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq τ'
  let π := pullbackLeftPullbackSndIso p ψ (𝒰.f i)
  let fst' := Limits.pullback.fst (Limits.pullback.snd p ψ) (𝒰.f i)
  let j : Limits.pullback p (𝒰.f i ≫ ψ) ⟶ Limits.pullback p ψ := π.inv ≫ fst'
  have hsnd : π.inv ≫ Limits.pullback.snd (Limits.pullback.snd p ψ) (𝒰.f i) = Limits.pullback.snd p (𝒰.f i ≫ ψ) := by
    rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
  have hsq : j ≫ Limits.pullback.snd p ψ = Limits.pullback.snd p (𝒰.f i ≫ ψ) ≫ 𝒰.f i := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd]
  have hsurj : ∀ x : ↑(Limits.pullback p ψ), Limits.pullback.snd p ψ x ∈ Set.range (𝒰.f i) → x ∈ Set.range j := by
    intro x hx
    have hx' : x ∈ Set.range fst' := by rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨w, rfl⟩ := hx'
    exact ⟨π.hom w, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]⟩
  have hj : LIO (Limits.pullback.snd p (𝒰.f i ≫ ψ))
      ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (Limits.pullback.fst p ψ)).obj N)) := by
    refine lio_of_iso ?_ (h i)
    have hfst : π.inv ≫ fst' ≫ Limits.pullback.fst p ψ = Limits.pullback.fst p (𝒰.f i ≫ ψ) :=
      pullbackLeftPullbackSndIso_inv_fst p ψ (𝒰.f i)
    exact ((Scheme.Modules.pullbackCongr hfst).app N).symm ≪≫ ((Scheme.Modules.pullbackComp π.inv _).app N).symm ≪≫
      (Scheme.Modules.pullback π.inv).mapIso ((Scheme.Modules.pullbackComp fst' _).app N).symm ≪≫
      (Scheme.Modules.pullbackComp π.inv fst').app _
  obtain ⟨U, hU, hiso⟩ := exists_iso_of_openImmersion (Limits.pullback.snd p ψ) _ j (𝒰.f i) hsq hsurj _ hj y
  exact ⟨U, hU, hiso⟩

end FT

section Factor

variable {A : Type u} [CommRing A]

theorem exists_fac_iff (I : Ideal A) {T' : Scheme.{u}} (ψ : T' ⟶ Spec (.of A)) :
    (∃ z : T' ⟶ Spec (.of (A ⧸ I)), z ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))) = ψ) ↔
      ∀ a ∈ I, ψ.appTop ((Scheme.ΓSpecIso (.of A)).inv a) = 0 := by
  constructor
  · rintro ⟨z, rfl⟩ a ha
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    change z.appTop (((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))).appTop) a) = 0
    rw [← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change z.appTop ((Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]
  · intro hkill
    let φ : A →+* Γ(T', ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ ψ.appTop).hom
    let φ' : A ⧸ I →+* Γ(T', ⊤) := Ideal.Quotient.lift I φ hkill
    refine ⟨T'.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ'), ?_⟩
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.lift_comp_mk]
    change T'.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ ψ.appTop) = ψ
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem appTop_ΓSpecIso_inv {B : Type u} [CommRing B] (φ : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (φ a) := by
  change ((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop) a = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Factor

section Charts

variable {R : Type u} [CommRing R] {X T : Scheme.{u}} (c : X ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
  (N : (Limits.pullback c t).Modules)

theorem fromSpec_eq (U : T.affineOpens) :
    letI := algebraOfHom t U
    U.2.fromSpec ≫ t = specMap R Γ(T, U) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) U.2 (le_top : (U : T.Opens) ≤ t ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm

def mU (U : T.affineOpens) : letI := algebraOfHom t U; XB c Γ(T, U) ⟶ Limits.pullback c t :=
  letI := algebraOfHom t U
  pullback.map c (specMap R Γ(T, U)) c t (𝟙 X) U.2.fromSpec (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, fromSpec_eq])

theorem mU_fst (U : T.affineOpens) :
    letI := algebraOfHom t U
    mU c t U ≫ Limits.pullback.fst c t = fB c Γ(T, U) := by
  letI := algebraOfHom t U
  rw [mU, fB, pullback.lift_fst, Category.comp_id]

theorem mU_snd (U : T.affineOpens) :
    letI := algebraOfHom t U
    mU c t U ≫ Limits.pullback.snd c t = sB c Γ(T, U) ≫ U.2.fromSpec := by
  letI := algebraOfHom t U
  rw [mU, sB, pullback.lift_snd]

variable (U : T.affineOpens) {T' : Scheme.{u}}

def πU (ψ' : T' ⟶ Spec (.of Γ(T, U))) :
    letI := algebraOfHom t U
    Limits.pullback (sB c Γ(T, U)) ψ' ≅ Limits.pullback (Limits.pullback.snd c t) (ψ' ≫ U.2.fromSpec) :=
  letI := algebraOfHom t U
  pullbackLeftPullbackSndIso c (specMap R Γ(T, U)) ψ' ≪≫
    pullback.congrHom rfl (by rw [Category.assoc, fromSpec_eq]) ≪≫
      (pullbackLeftPullbackSndIso c t (ψ' ≫ U.2.fromSpec)).symm

theorem πU_hom_snd (ψ' : T' ⟶ Spec (.of Γ(T, U))) :
    letI := algebraOfHom t U
    (πU c t U ψ').hom ≫ Limits.pullback.snd (Limits.pullback.snd c t) (ψ' ≫ U.2.fromSpec) =
      Limits.pullback.snd (sB c Γ(T, U)) ψ' := by
  letI := algebraOfHom t U
  change ((pullbackLeftPullbackSndIso c (specMap R Γ(T, U)) ψ').hom ≫ (pullback.congrHom rfl _).hom ≫
    (pullbackLeftPullbackSndIso c t (ψ' ≫ U.2.fromSpec)).inv) ≫ _ = _
  have h2 : (pullbackLeftPullbackSndIso c t (ψ' ≫ U.2.fromSpec)).inv ≫
      Limits.pullback.snd (Limits.pullback.snd c t) (ψ' ≫ U.2.fromSpec) = Limits.pullback.snd c _ := by
    rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
  rw [Category.assoc, Category.assoc, h2, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

theorem πU_hom_fst (ψ' : T' ⟶ Spec (.of Γ(T, U))) :
    letI := algebraOfHom t U
    (πU c t U ψ').hom ≫ Limits.pullback.fst (Limits.pullback.snd c t) (ψ' ≫ U.2.fromSpec) =
      Limits.pullback.fst (sB c Γ(T, U)) ψ' ≫ mU c t U := by
  letI := algebraOfHom t U
  apply pullback.hom_ext
  · have e1 : (pullbackLeftPullbackSndIso c t (ψ' ≫ U.2.fromSpec)).inv ≫
        Limits.pullback.fst (Limits.pullback.snd c t) (ψ' ≫ U.2.fromSpec) ≫ Limits.pullback.fst c t =
          Limits.pullback.fst c _ := pullbackLeftPullbackSndIso_inv_fst _ _ _
    have e2 : (pullback.congrHom rfl (by rw [Category.assoc, fromSpec_eq]) :
        Limits.pullback c (ψ' ≫ specMap R Γ(T, U)) ≅ Limits.pullback c ((ψ' ≫ U.2.fromSpec) ≫ t)).hom ≫
          Limits.pullback.fst c _ = Limits.pullback.fst c _ := by
      rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
    change ((pullbackLeftPullbackSndIso c (specMap R Γ(T, U)) ψ').hom ≫ (pullback.congrHom rfl _).hom ≫
      (pullbackLeftPullbackSndIso c t (ψ' ≫ U.2.fromSpec)).inv) ≫ _ ≫ _ = _
    simp only [Category.assoc]
    rw [e1, e2, pullbackLeftPullbackSndIso_hom_fst, mU_fst]
  · rw [Category.assoc, Category.assoc, Limits.pullback.condition, ← Category.assoc, πU_hom_snd, mU_snd,
      Limits.pullback.condition_assoc]

theorem πU_inv_snd (ψ' : T' ⟶ Spec (.of Γ(T, U))) :
    letI := algebraOfHom t U
    (πU c t U ψ').inv ≫ Limits.pullback.snd (sB c Γ(T, U)) ψ' =
      Limits.pullback.snd (Limits.pullback.snd c t) (ψ' ≫ U.2.fromSpec) := by
  rw [Iso.inv_comp_eq, πU_hom_snd]

def eU (ψ' : T' ⟶ Spec (.of Γ(T, U))) :
    letI := algebraOfHom t U
    (Scheme.Modules.pullback (Limits.pullback.fst (sB c Γ(T, U)) ψ')).obj ((Scheme.Modules.pullback (mU c t U)).obj N) ≅
      (Scheme.Modules.pullback (πU c t U ψ').hom).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) (ψ' ≫ U.2.fromSpec))).obj N) :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr (πU_hom_fst c t U ψ').symm).app N ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N).symm

theorem F_chart_iff (ψ' : T' ⟶ Spec (.of Γ(T, U))) :
    letI := algebraOfHom t U
    F (Limits.pullback.snd c t) N (ψ' ≫ U.2.fromSpec) ↔
      LIO (Limits.pullback.snd (sB c Γ(T, U)) ψ')
        ((Scheme.Modules.pullback (Limits.pullback.fst (sB c Γ(T, U)) ψ')).obj
          ((Scheme.Modules.pullback (mU c t U)).obj N)) := by
  letI := algebraOfHom t U
  constructor
  · intro h
    have h1 := lio_precomp _ (πU c t U ψ').hom _ h
    rw [πU_hom_snd] at h1
    exact lio_of_iso (eU c t N U ψ').symm h1
  · intro h
    have h1 := lio_precomp _ (πU c t U ψ').inv _ h
    rw [πU_inv_snd] at h1
    refine lio_of_iso ?_ h1
    exact (Scheme.Modules.pullback (πU c t U ψ').inv).mapIso (eU c t N U ψ') ≪≫
      (Scheme.Modules.pullbackComp (πU c t U ψ').inv (πU c t U ψ').hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr (πU c t U ψ').inv_hom_id).app _ ≪≫ (Scheme.Modules.pullbackId _).app _

end Charts

section KI

variable {R : Type u} [CommRing R] {X T : Scheme.{u}} (c : X ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
  (N Ninv : (Limits.pullback c t).Modules)

theorem bijective_unit_app {Y Y' : Scheme.{u}} (e : Y' ≅ Y) (M : Y.Modules) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M).app ⊤) := by
  let E : Y.Modules ≌ Y'.Modules := CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom)
    (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId Y).symm ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id.symm ≪≫
        (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫ Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
        Scheme.Modules.pullbackId Y')
  haveI : (Scheme.Modules.pullback e.hom).IsEquivalence := E.isEquivalence_functor
  haveI := (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit_isIso_of_L_fully_faithful
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M) := inferInstance
  exact ConcreteCategory.bijective_of_isIso _

theorem exists_ne_zero_iff {Y Y' : Scheme.{u}} (e : Y' ≅ Y) (M : Y.Modules) :
    (∃ s : Γ(M, ⊤), s ≠ 0) ↔ ∃ s : Γ((Scheme.Modules.pullback e.hom).obj M, ⊤), s ≠ 0 := by
  have hb := bijective_unit_app e M
  set u := ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M).app ⊤
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(show Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) from u s), fun h0 => hs (hb.1 ?_)⟩
    exact h0.trans (map_zero (ConcreteCategory.hom u)).symm
  · rintro ⟨s, hs⟩
    obtain ⟨s', hs'⟩ := hb.2 s
    refine ⟨s', fun h0 => hs ?_⟩
    rw [← hs', h0]
    exact map_zero (ConcreteCategory.hom u)

theorem exists_ne_zero_of_iso {Y : Scheme.{u}} {M M' : Y.Modules} (e : M ≅ M') (h : ∃ s : Γ(M, ⊤), s ≠ 0) :
    ∃ s : Γ(M', ⊤), s ≠ 0 := by
  obtain ⟨s, hs⟩ := h
  refine ⟨e.hom.app ⊤ s, fun h0 => hs ?_⟩
  have := inv_app_hom_app e ⊤ s
  rw [← this, h0, map_zero]

def KI (U : T.affineOpens) (I : Ideal Γ(T, U)) : Prop :=
  ∀ ⦃T' : Scheme.{u}⦄ (ψ' : T' ⟶ Spec (.of Γ(T, U))),
    F (Limits.pullback.snd c t) N (ψ' ≫ U.2.fromSpec) ↔ ∀ a ∈ I, ψ'.appTop ((Scheme.ΓSpecIso (.of Γ(T, U))).inv a) = 0

variable [IsLocallyNoetherian T] [IsProper c] [Flat c]
variable (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
  Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
variable (hN : Scheme.Modules.IsInvertible N) (hNinv : Scheme.Modules.IsInvertible Ninv)
variable (hfib : ∀ (K : Type u) [Field K] (k : Spec (.of K) ⟶ T),
  (∃ s : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N, ⊤), s ≠ 0) →
  (∃ s' : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj Ninv, ⊤), s' ≠ 0) →
    Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N ≅
      SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) k).ringCatSheaf))
variable (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ Limits.pullback c t),
  Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
    Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf))
include hH0 hN hNinv hfib hinv

theorem exists_KI (U : T.affineOpens) : ∃ I : Ideal Γ(T, U), KI c t N U I := by
  letI := algebraOfHom t U
  haveI : IsNoetherianRing Γ(T, U) := IsLocallyNoetherian.component_noetherian U
  let c' : XB c Γ(T, U) ⟶ Spec (.of Γ(T, U)) := sB c Γ(T, U)
  let N' : (XB c Γ(T, U)).Modules := (Scheme.Modules.pullback (mU c t U)).obj N
  let Ninv' : (XB c Γ(T, U)).Modules := (Scheme.Modules.pullback (mU c t U)).obj Ninv

  have hH0' : ∀ (B : Type u) [CommRing B] [Algebra Γ(T, U) B],
      Function.Bijective (Limits.pullback.snd c' (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) B)))).appTop := by
    intro B _ _
    letI : Algebra R B := ((algebraMap Γ(T, U) B).comp (algebraMap R Γ(T, U))).toAlgebra
    haveI : IsScalarTower R Γ(T, U) B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have h1 : Limits.pullback.snd c' (specMap Γ(T, U) B) = (θ c Γ(T, U) B).hom ≫ sB c B := (θ_hom_snd c Γ(T, U) B).symm
    change Function.Bijective (Limits.pullback.snd c' (specMap Γ(T, U) B)).appTop
    rw [h1, Scheme.Hom.comp_appTop]
    haveI : IsIso ((θ c Γ(T, U) B).hom.app ⊤) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso ((θ c Γ(T, U) B).hom.app ⊤)).comp (hH0 B)
  have hinv' : ∀ (Y : Scheme.{u}) (g : Y ⟶ XB c Γ(T, U)),
      Nonempty ((Scheme.Modules.pullback g).obj N' ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv' ≅ SheafOfModules.unit Y.ringCatSheaf) := by
    intro Y g ⟨e⟩
    obtain ⟨e'⟩ := hinv Y (g ≫ mU c t U) ⟨((Scheme.Modules.pullbackComp _ _).app N).symm ≪≫ e⟩
    exact ⟨(Scheme.Modules.pullbackComp _ _).app Ninv ≪≫ e'⟩
  have hfib' : ∀ (K : Type u) [Field K] [Algebra Γ(T, U) K],
      (∃ s : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c' (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) K))))).obj N', ⊤), s ≠ 0) →
      (∃ s' : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c' (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) K))))).obj Ninv', ⊤), s' ≠ 0) →
        Nonempty ((Scheme.Modules.pullback
            (Limits.pullback.fst c' (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) K))))).obj N' ≅
          SheafOfModules.unit (Limits.pullback c' (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) K)))).ringCatSheaf) := by
    intro K _ _ hs hs'
    let k : Spec (.of K) ⟶ T := specMap Γ(T, U) K ≫ U.2.fromSpec
    let π := πU c t U (specMap Γ(T, U) K)
    have h1 : ∃ s : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N, ⊤), s ≠ 0 :=
      (exists_ne_zero_iff π _).mpr (exists_ne_zero_of_iso (eU c t N U (specMap Γ(T, U) K)) hs)
    have h2 : ∃ s : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj Ninv, ⊤), s ≠ 0 :=
      (exists_ne_zero_iff π _).mpr (exists_ne_zero_of_iso (eU c t Ninv U (specMap Γ(T, U) K)) hs')
    obtain ⟨e⟩ := hfib K k h1 h2
    exact ⟨eU c t N U (specMap Γ(T, U) K) ≪≫ (Scheme.Modules.pullback π.hom).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _⟩
  obtain ⟨I, hI⟩ :=
    Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper c' hH0' N' Ninv'
      (hN.pullback _) (hNinv.pullback _) hfib' hinv'
  refine ⟨I, fun T' ψ' => ?_⟩
  rw [F_chart_iff, ← exists_fac_iff I ψ']
  exact (hI ψ').symm

end KI

section Sheaf

variable {R : Type u} [CommRing R] {X T : Scheme.{u}} (c : X ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
  (N : (Limits.pullback c t).Modules)

theorem kills_quotient {A : Type u} [CommRing A] (I : Ideal A) :
    ∀ a ∈ I, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ((Scheme.ΓSpecIso (.of A)).inv a) = 0 := by
  intro a ha
  rw [appTop_ΓSpecIso_inv, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

theorem KI_unique (U : T.affineOpens) (I I' : Ideal Γ(T, U)) (h : KI c t N U I) (h' : KI c t N U I') : I = I' := by
  have key : ∀ (J J' : Ideal Γ(T, U)), KI c t N U J → KI c t N U J' → J' ≤ J := by
    intro J J' hJ hJ' a ha
    have hF : F (Limits.pullback.snd c t) N (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ U.2.fromSpec) :=
      (hJ _).mpr (kills_quotient J)
    have h1 := (hJ' _).mp hF a ha
    rw [appTop_ΓSpecIso_inv] at h1
    have h2 : Ideal.Quotient.mk J a = 0 :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Γ(T, U) ⧸ J))).inv).1 (h1.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  exact le_antisymm (key I' I h' h) (key I I' h h')

theorem KI_basicOpen (U : T.affineOpens) (f : Γ(T, U)) (I : Ideal Γ(T, U)) (h : KI c t N U I) :
    KI c t N (T.affineBasicOpen f) (I.map (T.presheaf.map (homOfLE (T.basicOpen_le f)).op).hom) := by
  intro T' ψ''
  have hVU : (T.affineBasicOpen f).2.fromSpec =
      Spec.map (T.presheaf.map (homOfLE (T.basicOpen_le f)).op) ≫ U.2.fromSpec :=
    (IsAffineOpen.map_fromSpec U.2 (T.affineBasicOpen f).2 (homOfLE (T.basicOpen_le f)).op).symm
  have h1 := h (ψ'' ≫ Spec.map (T.presheaf.map (homOfLE (T.basicOpen_le f)).op))
  have hassoc : (ψ'' ≫ Spec.map (T.presheaf.map (homOfLE (T.basicOpen_le f)).op)) ≫ U.2.fromSpec =
      ψ'' ≫ (T.affineBasicOpen f).2.fromSpec := by
    rw [Category.assoc]; exact congrArg (ψ'' ≫ ·) hVU.symm
  rw [hassoc] at h1
  rw [h1]
  constructor
  · intro hk a' ha'
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha'
    · rintro _ ⟨a, ha, rfl⟩
      have := hk a ha
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
      change ψ''.appTop ((Spec.map (CommRingCat.ofHom (T.presheaf.map (homOfLE (T.basicOpen_le f)).op).hom)).appTop
        ((Scheme.ΓSpecIso (.of Γ(T, U))).inv a)) = 0 at this
      rwa [appTop_ΓSpecIso_inv] at this
    · rw [map_zero, map_zero]
    · intro x y _ _ hx hy; rw [map_add, map_add, hx, hy, add_zero]
    · intro r x _ hx; rw [smul_eq_mul, map_mul, map_mul, hx, mul_zero]
  · intro hk a ha
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    change ψ''.appTop ((Spec.map (CommRingCat.ofHom (T.presheaf.map (homOfLE (T.basicOpen_le f)).op).hom)).appTop
      ((Scheme.ΓSpecIso (.of Γ(T, U))).inv a)) = 0
    rw [appTop_ΓSpecIso_inv]
    exact hk _ (Ideal.mem_map_of_mem _ ha)

def idealSheaf (hex : ∀ U : T.affineOpens, ∃ I : Ideal Γ(T, U), KI c t N U I) : T.IdealSheafData where
  ideal U := Classical.choose (hex U)
  map_ideal_basicOpen U f :=
    KI_unique c t N _ _ _ (KI_basicOpen c t N U f _ (Classical.choose_spec (hex U)))
      (Classical.choose_spec (hex (T.affineBasicOpen f)))

theorem idealSheaf_KI (hex : ∀ U : T.affineOpens, ∃ I : Ideal Γ(T, U), KI c t N U I) (U : T.affineOpens) :
    KI c t N U ((idealSheaf c t N hex).ideal U) :=
  Classical.choose_spec (hex U)

end Sheaf

section Main

variable {R : Type u} [CommRing R] {X T : Scheme.{u}} (c : X ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
  (N : (Limits.pullback c t).Modules)

theorem exists_isClosedImmersion (hex : ∀ U : T.affineOpens, ∃ I : Ideal Γ(T, U), KI c t N U I) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ T), IsClosedImmersion ι ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), (∃ z : T' ⟶ Z, z ≫ ι = ψ) ↔ F (Limits.pullback.snd c t) N ψ := by
  let 𝓘 := idealSheaf c t N hex
  refine ⟨𝓘.subscheme, 𝓘.subschemeι, inferInstance, fun {T'} ψ => ⟨?_, fun hF => ?_⟩⟩
  · rintro ⟨z, rfl⟩
    apply F_comp

    apply F_of_openCover _ _ _ 𝓘.subschemeCover.openCover
    intro U
    change F (Limits.pullback.snd c t) N (𝓘.subschemeCover.f U ≫ 𝓘.subschemeι)
    rw [Scheme.IdealSheafData.subschemeCover_map_subschemeι, Scheme.IdealSheafData.glueDataObjι_ι]
    exact (idealSheaf_KI c t N hex U _).mpr (kills_quotient _)
  ·
    have hle : 𝓘 ≤ ψ.ker := by
      rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
      intro U a ha
      rw [RingHom.mem_ker]

      let ι' : Type u := {V : T'.affineOpens // (V : T'.Opens) ≤ ψ ⁻¹ᵁ U}
      apply TopCat.Sheaf.eq_of_locally_eq' T'.sheaf (fun V : ι' => (V.1 : T'.Opens)) (ψ ⁻¹ᵁ U)
        (fun V => homOfLE V.2)
      · intro x hx
        obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
          T'.isBasis_affineOpens.exists_subset_of_mem_open hx (ψ ⁻¹ᵁ (U : T.Opens)).2
        exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
      · intro V
        change T'.presheaf.map (homOfLE V.2).op (ψ.app U a) = T'.presheaf.map (homOfLE V.2).op 0
        rw [map_zero]
        change ψ.appLE U V.1 V.2 a = 0
        have hF' : F (Limits.pullback.snd c t) N (Spec.map (ψ.appLE U V.1 V.2) ≫ U.2.fromSpec) := by
          rw [IsAffineOpen.SpecMap_appLE_fromSpec ψ U.2 V.1.2 V.2]
          exact F_comp _ _ _ _ hF
        have h1 := (idealSheaf_KI c t N hex U _).mp hF' a ha
        change (Spec.map (CommRingCat.ofHom (ψ.appLE U V.1 V.2).hom)).appTop _ = 0 at h1
        rw [appTop_ΓSpecIso_inv] at h1
        exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1 (h1.trans (map_zero _).symm)
    refine ⟨IsClosedImmersion.lift 𝓘.subschemeι ψ (by rwa [Scheme.IdealSheafData.ker_subschemeι]), ?_⟩
    exact IsClosedImmersion.lift_fac _ _ _

theorem main [IsLocallyNoetherian T] [IsProper c] [Flat c]
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    (N Ninv : (Limits.pullback c t).Modules)
    (hN : Scheme.Modules.IsInvertible N) (hNinv : Scheme.Modules.IsInvertible Ninv)
    (hfib : ∀ (K : Type u) [Field K] (k : Spec (.of K) ⟶ T),
      (∃ s : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N, ⊤), s ≠ 0) →
      (∃ s' : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj Ninv, ⊤), s' ≠ 0) →
        Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N ≅
          SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) k).ringCatSheaf))
    (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ Limits.pullback c t),
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ T), IsClosedImmersion ι ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T),
        (∃ z : T' ⟶ Z, z ≫ ι = ψ) ↔
          Scheme.Modules.LocallyIsoOver (Limits.pullback.snd (Limits.pullback.snd c t) ψ)
            ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) ψ)).obj N)
            (SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) ψ).ringCatSheaf) :=
  exists_isClosedImmersion c t N (fun U => exists_KI c t N Ninv hH0 hN hNinv hfib hinv U)

end Main

end P2mSeesawGeneralBase

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    {T : Scheme.{u}} [IsLocallyNoetherian T] (t : T ⟶ Spec (CommRingCat.of R))
    (N Ninv : (Limits.pullback c t).Modules)
    (hN : Scheme.Modules.IsInvertible N) (hNinv : Scheme.Modules.IsInvertible Ninv)
    (hfib : ∀ (K : Type u) [Field K] (k : Spec (CommRingCat.of K) ⟶ T),
      (∃ s : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N, ⊤), s ≠ 0) →
      (∃ s' : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj Ninv, ⊤), s' ≠ 0) →
        Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N ≅
          SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) k).ringCatSheaf))
    (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ Limits.pullback c t),
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ T), IsClosedImmersion ι ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T),
        (∃ z : T' ⟶ Z, z ≫ ι = ψ) ↔
          Scheme.Modules.LocallyIsoOver (Limits.pullback.snd (Limits.pullback.snd c t) ψ)
            ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) ψ)).obj N)
            (SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) ψ).ringCatSheaf) :=
  P2mSeesawGeneralBase.main c t hH0 N Ninv hN hNinv hfib hinv

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper (solution)
