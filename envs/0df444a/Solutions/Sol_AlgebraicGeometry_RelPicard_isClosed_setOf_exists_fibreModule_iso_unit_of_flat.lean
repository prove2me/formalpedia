-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isClosed_setOf_exists_fibreModule_iso_unit_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/dd7e681a-26cf-57d4-8f25-ab04e48f25dd

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import Theorems.Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat.AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory"

namespace H0UnitAux

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat.AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {R : Type u} [CommRing R]

theorem finrank_H0_unit_eq_finrank_sections {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (.of R)) :
    Module.finrank R (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H0 =
      (letI := algebraOfHom x ⊤; Module.finrank R Γ(X, ⊤)) := by
  letI := algebraOfHom x ⊤
  letI := moduleSectionsOfHom x (SheafOfModules.unit X.ringCatSheaf) ⊤
  obtain ⟨e, -⟩ := exists_linearEquiv_sectionsOf_H0 𝒱 x (SheafOfModules.unit X.ringCatSheaf)

  let e0 : Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) ≃ₗ[R] Γ(X, ⊤) :=
    { toFun := fun m => (m : Γ(X, ⊤))
      invFun := fun a => (a : Γ(SheafOfModules.unit X.ringCatSheaf, ⊤))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.finrank_eq, e0.finrank_eq]

theorem algebraMap_eq_appTop {Y : Scheme.{u}} (y : Y ⟶ Spec (.of R)) (r : R) :
    (algebraOfHom y ⊤).algebraMap r = y.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
  have happ : y.appLE ⊤ ⊤ le_top = y.appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [algebraMap_algebraOfHom, happ]

theorem appTop_algebraMap {X X' : Scheme.{u}} (x : X ⟶ Spec (.of R)) (x' : X' ⟶ Spec (.of R))
    (ψ : X ⟶ X') (hψ : ψ ≫ x' = x) (r : R) :
    ψ.appTop.hom ((algebraOfHom x' ⊤).algebraMap r) = (algebraOfHom x ⊤).algebraMap r := by
  rw [algebraMap_eq_appTop, algebraMap_eq_appTop, ← hψ, Scheme.Hom.comp_appTop]
  rfl

noncomputable def sectionsLinearEquiv {X X' : Scheme.{u}} (x : X ⟶ Spec (.of R)) (x' : X' ⟶ Spec (.of R))
    (ψ : X ≅ X') (hψ : ψ.hom ≫ x' = x) :
    letI := algebraOfHom x' ⊤; letI := algebraOfHom x ⊤
    Γ(X', ⊤) ≃ₗ[R] Γ(X, ⊤) :=
  letI := algebraOfHom x' ⊤; letI := algebraOfHom x ⊤
  { toFun := fun a => ψ.hom.appTop.hom a
    invFun := fun b => ψ.inv.appTop.hom b
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact appTop_algebraMap x x' ψ.hom hψ r
    left_inv := fun a => by
      change (ψ.hom.appTop ≫ ψ.inv.appTop).hom a = a
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
      rfl
    right_inv := fun b => by
      change (ψ.inv.appTop ≫ ψ.hom.appTop).hom b = b
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      rfl }

theorem finrank_eq_one_of_bijective {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]
    (h : Function.Bijective (algebraMap k S)) : Module.finrank k S = 1 := by
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap k S) h).finrank_eq, Module.finrank_self]

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (k : Type u) [Field k]
    (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (Limits.pullback (Limits.pullback.snd c t) s).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (Limits.pullback.snd (Limits.pullback.snd c t) s)
      (SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) s).ringCatSheaf)).H0 = 1 := by

  letI : Algebra R k := (Spec.preimage (s ≫ t)).hom.toAlgebra
  have hspec : Scheme.TwoAffineOpenCover.specMap R k = s ≫ t := by
    change Spec.map (CommRingCat.ofHom (algebraMap R k)) = s ≫ t
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

  let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R k)
  let x' : X' ⟶ Spec (.of k) := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k)
  let ψ : Limits.pullback (Limits.pullback.snd c t) s ≅ X' :=
    pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hspec.symm
  have hψ : ψ.hom ≫ x' = Limits.pullback.snd (Limits.pullback.snd c t) s := by
    simp only [ψ, x', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
      Category.comp_id]
    exact pullbackLeftPullbackSndIso_hom_snd c t s
  rw [finrank_H0_unit_eq_finrank_sections 𝒲 (Limits.pullback.snd (Limits.pullback.snd c t) s)]
  letI := algebraOfHom x' ⊤
  letI := algebraOfHom (Limits.pullback.snd (Limits.pullback.snd c t) s) ⊤
  have e := sectionsLinearEquiv (Limits.pullback.snd (Limits.pullback.snd c t) s) x' ψ hψ
  rw [← e.finrank_eq]
  exact finrank_eq_one_of_bijective (hH0 k)

end H0UnitAux

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage IsLocallyNoetherian Scheme.Modules.Hom.zero_app IsProper Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.Modules.presheaf IsAffineOpen.fromSpec_top Scheme.Modules.Hom IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec Scheme.Hom.id_appTop Spec.map Scheme Scheme.Modules.Hom.app Scheme.isoSpec_Spec_inv Scheme.Hom.comp_appTop Flat IsLocallyNoetherian.component_noetherian exists_isAffineOpen_mem_and_subset Spec.preimage Scheme.Modules.pullbackCongr isAffineOpen_top Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.isScalarTower_sections Scheme.Modules.pullbackTensorUnitObjIso OModulePresheaf Scheme.TwoAffineOpenCover.flat_sections_of_flat Scheme.Modules.projective_sections_of_locallyTrivial OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero fibreModule exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField"
namespace UnitClosed
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open TensorProduct Opposite

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_H0_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact e0.finrank_eq

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A)
    (p : Spec (CommRingCat.of 𝔭.asIdeal.ResidueField)) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base p = 𝔭 := by
  apply PrimeSpectrum.ext
  have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right p.isPrime.ne_top
  change Ideal.comap (algebraMap A 𝔭.asIdeal.ResidueField) p.asIdeal = 𝔭.asIdeal
  rw [hp, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     show (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  show (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

theorem flat_prod {S : Type*} [CommRing S] (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module S N] [Module.Flat S M] [Module.Flat S N] : Module.Flat S (M × N) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hM := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S M)) I
  have hN := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S N)) I
  have key' : ∀ (p : M × N) (i : I), TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype (p ⊗ₜ i)) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I (p ⊗ₜ i)) := by
    intro p i
    obtain ⟨m, n⟩ := p
    simp [TensorProduct.prodLeft_tmul, LinearMap.lTensor_tmul]
  have key : ∀ x, TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype x) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p i => exact key' p i
  intro x y hxy
  apply (TensorProduct.prodLeft S S M N I).injective
  have hxy' := congrArg (TensorProduct.prodLeft S S M N S) hxy
  rw [key, key] at hxy'
  have h1 := congrArg Prod.fst hxy'
  have h2 := congrArg Prod.snd hxy'
  simp only [LinearMap.prodMap_apply] at h1 h2
  exact Prod.ext (hM h1) (hN h2)

theorem isClosed_setOf_le_finrank_ker_cechDiff_baseChange
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of A))
    [IsProper π] [Flat π] (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum A | n ≤ Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.sectionsOf π M).cechDiff.baseChange 𝔭.asIdeal.ResidueField))} := by

  have flatOf : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
      Module.Flat A Γ(M, U) := by
    intro U hU
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
    haveI : Module.Flat A Γ(X, U) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π U hU
    haveI : Module.Projective Γ(X, U) Γ(M, U) :=
      Scheme.Modules.projective_sections_of_locallyTrivial _ hM.1 ⟨U, hU⟩
    exact Module.Flat.trans A Γ(X, U) Γ(M, U)
  haveI : Module.Flat A (𝒱.sectionsOf π M).M0 := flatOf _ 𝒱.isAffineOpen_U0
  haveI : Module.Flat A (𝒱.sectionsOf π M).M1 := flatOf _ 𝒱.isAffineOpen_U1
  haveI : Module.Flat A (𝒱.sectionsOf π M).M01 := flatOf _ 𝒱.isAffineOpen_inf
  haveI : Module.Flat A ((𝒱.sectionsOf π M).M0 × (𝒱.sectionsOf π M).M1) := flat_prod _ _

  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M hM.1 𝒱.toOrderedAffineCover
  obtain ⟨hfin0, hfin1⟩ := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf
  haveI : Module.Finite A (LinearMap.ker (𝒱.sectionsOf π M).cechDiff) := hfin0
  haveI : Module.Finite A ((𝒱.sectionsOf π M).M01 ⧸ LinearMap.range (𝒱.sectionsOf π M).cechDiff) := hfin1
  have h := TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange (𝒱.sectionsOf π M).cechDiff
    (𝟙 (Spec (CommRingCat.of A))) n
  first
    | simpa using h
    | (have h' := h; simp at h' ⊢; exact h')
    | (have h' := h; simp at h'; exact h')
    | exact h

theorem map_eq_zero_iff_of_iso {X Y : Scheme.{u}} (φ : X ≅ Y) {M N : X.Modules} (σ : M ⟶ N) :
    (Scheme.Modules.pullback φ.inv).map σ = 0 ↔ σ = 0 := by
  constructor
  · intro h

    let Nat : 𝟭 X.Modules ≅ Scheme.Modules.pullback φ.inv ⋙ Scheme.Modules.pullback φ.hom :=
      (Scheme.Modules.pullbackId X).symm ≪≫ Scheme.Modules.pullbackCongr φ.hom_inv_id.symm ≪≫
        (Scheme.Modules.pullbackComp φ.hom φ.inv).symm
    have hnat := Nat.hom.naturality σ

    have h2 : (Scheme.Modules.pullback φ.inv ⋙ Scheme.Modules.pullback φ.hom).map σ = 0 := by
      change (Scheme.Modules.pullback φ.hom).map ((Scheme.Modules.pullback φ.inv).map σ) = 0
      rw [h, Functor.map_zero]
    rw [h2, Limits.comp_zero] at hnat
    have h3 : σ ≫ Nat.hom.app N = (0 : M ⟶ N) ≫ Nat.hom.app N := by
      rw [Limits.zero_comp]; simpa using hnat
    exact (cancel_mono (Nat.hom.app N)).mp h3
  · rintro rfl; exact Functor.map_zero _ _ _

theorem nonempty_iso_unit_of_hfib
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : (pullback c x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd c x) L →
      ∀ s : 𝟙_ (pullback c x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback c x).Modules))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {k : Type u} [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ T) (M : (pullback (pullback.snd c t) s).Modules)
    (hM : Scheme.Modules.IsInvertible M) (hA : IsAlgEquivZero (fibreAt c t s) M)
    (σ : 𝟙_ (pullback (pullback.snd c t) s).Modules ⟶ M) (hσ : σ ≠ 0) :
    Nonempty (M ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules) := by
  let φ : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) := pullbackLeftPullbackSndIso c t s
  have hψ : φ.inv ≫ fibreAt c t s = pullback.snd c (s ≫ t) := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd c t s).symm
  let M' : (pullback c (s ≫ t)).Modules := (Scheme.Modules.pullback φ.inv).obj M
  have hM' : Scheme.Modules.IsInvertible M' := hM.pullback φ.inv
  have hA' : IsAlgEquivZero (pullback.snd c (s ≫ t)) M' := hA.pullback φ.inv hψ
  let σ' : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ M' :=
    (Scheme.Modules.pullbackTensorUnitObjIso φ.inv).inv ≫ (Scheme.Modules.pullback φ.inv).map σ
  have hσ' : σ' ≠ 0 := by
    intro h0
    apply hσ
    rw [← map_eq_zero_iff_of_iso φ]
    have := congrArg (fun f => (Scheme.Modules.pullbackTensorUnitObjIso φ.inv).hom ≫ f) h0
    first
      | simpa [σ'] using this
      | (have h' := this; simp [σ'] at h' ⊢; exact h')
      | (have h' := this; simp [σ'] at h'; exact h')
      | exact this
  obtain ⟨e'⟩ := hfib k (s ≫ t) M' hM' hA' σ' hσ'
  refine ⟨?_⟩

  exact ((Scheme.Modules.pullbackId _).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.hom_inv_id.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp φ.hom φ.inv).app M).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso e' ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso φ.hom

theorem finrank_H0_fibreModule_unit_eq_one'
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 = 1 := by
  rw [finrank_H0_congr (fibreAt c t s) 𝒲 (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s))]
  exact H0UnitAux.main c hH0 t k s 𝒲

end AlgebraicGeometry.RelPicard.UnitClosed

open AlgebraicGeometry.RelPicard.UnitClosed TensorProduct in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : (pullback c x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd c x) L →
      ∀ s : 𝟙_ (pullback c x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback c x).Modules))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) :
    IsClosed {x : T | ∃ (k : Type u) (_ : Field k) (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x ∧
        Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)} := by
  classical
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t

  have pointwise : ∀ {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      1 ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 →
        Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules) := by
    intro k _ _ s 𝒲 h1

    haveI : Nontrivial (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 :=
      Module.nontrivial_of_finrank_pos (R := k) h1
    obtain ⟨y, hy⟩ := exists_ne (0 : (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0)
    obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 (fibreAt c t s)
      (fibreModule c t s L.L)
    have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
    obtain ⟨σ, hσ0⟩ := exists_hom_ne_zero (fibreModule c t s L.L) (eΓ.symm y) hσ
    exact nonempty_iso_unit_of_hfib c hfib t s _ (L.isInvertible.pullback _) (hL k s) σ hσ0

  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx

  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := (⊤ : T.Opens)) trivial
  haveI : IsNoetherianRing Γ(T, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
  set A : Type u := Γ(T, W) with hA
  set j : Spec (CommRingCat.of A) ⟶ T := hW.fromSpec with hjdef
  have hj : j ≫ t = Scheme.TwoAffineOpenCover.specMap R A := by
    have e1 : CommRingCat.ofHom (algebraMap R A) = (Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top := rfl
    rw [hjdef, Scheme.TwoAffineOpenCover.specMap, e1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW]

  set CA := pullback c (Scheme.TwoAffineOpenCover.specMap R A) with hCA
  set πA : CA ⟶ Spec (CommRingCat.of A) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A) with hπA
  set g' : CA ⟶ pullback c t := pullback.map c (Scheme.TwoAffineOpenCover.specMap R A) c t (𝟙 C) j (𝟙 _)
    (by simp) (by rw [Category.comp_id, hj]) with hg'
  have hg'fst : g' ≫ pullback.fst c t = pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A) := by
    rw [hg', pullback.lift_fst, Category.comp_id]
  have hg'snd : g' ≫ pullback.snd c t = πA ≫ j := by
    rw [hg', pullback.lift_snd]
  have hcart : IsPullback g' πA (pullback.snd c t) j := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c t)
    rw [hg'fst, hj]
    exact IsPullback.of_hasPullback c (Scheme.TwoAffineOpenCover.specMap R A)
  haveI : IsProper πA := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : Flat πA := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  let 𝒱A : CA.TwoAffineOpenCover := 𝒱.pullback c A

  let h0 : (pullback c t).Modules → PrimeSpectrum A → ℕ := fun M 𝔭 =>
    Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
        𝔭.asIdeal.ResidueField))
  have hVclosed : IsClosed {𝔭 : PrimeSpectrum A | 1 ≤ h0 L.L 𝔭} :=
    isClosed_setOf_le_finrank_ker_cechDiff_baseChange πA 𝒱A _ (L.isInvertible.pullback g') 1

  have geom : ∀ 𝔭 : PrimeSpectrum A, ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (sb : Spec (CommRingCat.of K) ⟶ T),
      sb.base (IsLocalRing.closedPoint K) = j.base 𝔭 := by
    intro 𝔭
    refine ⟨AlgebraicClosure 𝔭.asIdeal.ResidueField, inferInstance, inferInstance,
      Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField (AlgebraicClosure 𝔭.asIdeal.ResidueField) ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField ≫ j, ?_⟩
    change j.base ((Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base
      ((Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField (AlgebraicClosure 𝔭.asIdeal.ResidueField)).base
        (IsLocalRing.closedPoint _))) = j.base 𝔭
    rw [specMap_residueField_base]

  have hO1 : ∀ 𝔭 : PrimeSpectrum A, h0 (𝟙_ (pullback c t).Modules) 𝔭 = 1 := by
    intro 𝔭
    obtain ⟨K, _, _, sb, hsb⟩ := geom 𝔭
    obtain ⟨𝒲, h𝒲⟩ :=
      exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱A 𝔭 sb hsb
    obtain ⟨hO0, -⟩ := h𝒲 (𝟙_ (pullback c t).Modules) (Scheme.Modules.isInvertible_unit _)
    change Module.finrank _ _ = 1
    rw [← hO0]
    exact finrank_H0_fibreModule_unit_eq_one' c hH0 t K sb 𝒲

  have key : ∀ 𝔭 : PrimeSpectrum A,
      (∃ (k : Type u) (_ : Field k) (s : Spec (CommRingCat.of k) ⟶ T),
        s.base (IsLocalRing.closedPoint k) = j.base 𝔭 ∧
          Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)) ↔ 1 ≤ h0 L.L 𝔭 := by
    intro 𝔭
    constructor
    · rintro ⟨k, _, s, hs, ⟨e⟩⟩
      obtain ⟨𝒲, h𝒲⟩ :=
        exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱A 𝔭 s hs
      obtain ⟨hL0, -⟩ := h𝒲 L.L L.isInvertible
      obtain ⟨hO0, -⟩ := h𝒲 (𝟙_ (pullback c t).Modules) (Scheme.Modules.isInvertible_unit _)
      have hcongr := finrank_H0_congr (fibreAt c t s) 𝒲
        (e ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s)).symm)
      rw [← hO1 𝔭]
      change Module.finrank _ _ ≤ Module.finrank _ _
      rw [← hL0, ← hO0, hcongr]
    · intro h
      obtain ⟨K, _, _, sb, hsb⟩ := geom 𝔭
      obtain ⟨𝒲, h𝒲⟩ :=
        exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱A 𝔭 sb hsb
      obtain ⟨hL0, -⟩ := h𝒲 L.L L.isInvertible
      refine ⟨K, inferInstance, sb, hsb, pointwise sb 𝒲 ?_⟩
      rw [hL0]
      exact h
  refine ⟨j.base '' {𝔭 : PrimeSpectrum A | 1 ≤ h0 L.L 𝔭}ᶜ, ?_, j.isOpenEmbedding.isOpenMap _ hVclosed.isOpen_compl, ?_⟩
  ·
    rintro _ ⟨𝔭, h𝔭, rfl⟩ hmem
    exact h𝔭 ((key 𝔭).mp hmem)
  ·
    have hxr : x ∈ Set.range ⇑j.base := by
      rw [hjdef]
      change x ∈ Set.range hW.fromSpec
      rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, rfl⟩ := hxr
    exact ⟨𝔭, fun h𝔭 => hx ((key 𝔭).mpr h𝔭), rfl⟩

end
end S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat (solution)
