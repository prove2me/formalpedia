-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_free_complex_cech_sliceAt_stalk_and_seesaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3247024f-d23f-56da-9cfd-bc1f2dabb568

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_free_complex_quasiIso_cech_sliceAt_stalk
import Theorems.Thm_AlgebraicGeometry_Polarisation_finrank_ker_baseChange_residue_eq_one_of_quasiIso_cech_sliceAt_stalk_of_forall
import Theorems.Thm_AlgebraicGeometry_Polarisation_forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall
import Theorems.Thm_AlgebraicGeometry_Polarisation_forall_exists_pullbackSection_eq_iff_exists_comp_eq_of_mem_range
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_free_complex_cech_sliceAt_stalk_and_seesaw
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace Dressing

theorem ker_stalkMap_le_maximalIdeal {KM A : Scheme.{0}} (κ : KM ⟶ A) (y' : KM) :
    RingHom.ker (κ.stalkMap y').hom ≤ IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y')) := by
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h := hu.map (κ.stalkMap y').hom
  rw [ha] at h
  exact not_isUnit_zero h

theorem isArtinianRing_stalk_of_isFinite (K : Type) [Field K] {KM : Scheme.{0}}
    (p : KM ⟶ Spec (CommRingCat.of K)) [IsFinite p] (y' : KM) :
    IsArtinianRing (KM.presheaf.stalk y') := by
  obtain ⟨hAff, hfin⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).1 (inferInstance : IsFinite p)

  letI : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(KM, ⊤) := p.appTop.hom.toAlgebra
  haveI : Module.Finite Γ(Spec (CommRingCat.of K), ⊤) Γ(KM, ⊤) := hfin
  have hF : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  letI : Field Γ(Spec (CommRingCat.of K), ⊤) := hF.toField
  haveI : IsArtinianRing Γ(KM, ⊤) := IsArtinianRing.of_finite Γ(Spec (CommRingCat.of K), ⊤) _

  have hU : IsAffineOpen (⊤ : KM.Opens) := isAffineOpen_top KM
  letI := TopCat.Presheaf.algebra_section_stalk KM.presheaf (⟨y', trivial⟩ : (⊤ : KM.Opens))
  have hloc := hU.isLocalization_stalk ⟨y', trivial⟩
  exact IsArtinianRing.localization_artinian (hU.primeIdealOf ⟨y', trivial⟩).asIdeal.primeCompl _

theorem exists_maximalIdeal_pow_le_ker_stalkMap (K : Type) [Field K] {KM A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of K)) (κ : KM ⟶ A) (hfin : IsFinite (κ ≫ f)) (y' : KM) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y')) ^ n ≤ RingHom.ker (κ.stalkMap y').hom := by
  haveI := hfin
  haveI : IsArtinianRing (KM.presheaf.stalk y') := isArtinianRing_stalk_of_isFinite K (κ ≫ f) y'
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := KM.presheaf.stalk y')
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩

  have hmap : (IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y'))).map (κ.stalkMap y').hom ≤
      IsLocalRing.maximalIdeal (KM.presheaf.stalk y') :=
    IsLocalRing.map_maximalIdeal_le (κ.stalkMap y').hom
  intro a ha
  rw [RingHom.mem_ker]
  have h1 : (κ.stalkMap y').hom a ∈ (IsLocalRing.maximalIdeal (KM.presheaf.stalk y')) ^ n := by
    have : (κ.stalkMap y').hom a ∈ ((IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y'))) ^ n).map (κ.stalkMap y').hom :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hmap n this
  rwa [hn] at h1

end Dressing

open TensorProduct in
set_option maxHeartbeats 1600000 in

theorem solution
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y' : KM) :
    letI y : A := κ.base y'
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules (pullback.snd f tR) FR
    letI 𝔪 : Ideal R := IsLocalRing.maximalIdeal R
    letI I : Ideal R := RingHom.ker (κ.stalkMap y').hom
    ∃ (Kc : ℕ → Type) (_ : ∀ i, AddCommGroup (Kc i)) (_ : ∀ i, Module R (Kc i))
      (_ : ∀ i, Module.Finite R (Kc i)) (_ : ∀ i, Module.Free R (Kc i))
      (_ : ∀ i, g < i → Subsingleton (Kc i))
      (δ : ∀ i, Kc i →ₗ[R] Kc (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0),
      Nonempty (LinearMap.ker (δ 0) ≃ₗ[R] G.H0 𝒦R) ∧
      (∀ i : ℕ, Nonempty
        ((LinearMap.ker (δ (i + 1)) ⧸ (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) ≃ₗ[R]
          G.HSucc 𝒦R i)) ∧
      I ≤ 𝔪 ∧ (∃ n : ℕ, 𝔪 ^ n ≤ I) ∧
      Module.finrank (R ⧸ 𝔪) (LinearMap.ker ((δ 0).baseChange (R ⧸ 𝔪))) = 1 ∧
      ∀ (J' : Ideal R) (hJ' : J' ≤ 𝔪), (∃ n : ℕ, 𝔪 ^ n ≤ J') →
        ((∀ z : (R ⧸ 𝔪) ⊗[R] Kc 0, (δ 0).baseChange (R ⧸ 𝔪) z = 0 →
            ∃ w : (R ⧸ J') ⊗[R] Kc 0, (δ 0).baseChange (R ⧸ J') w = 0 ∧
              LinearMap.rTensor (Kc 0) (Submodule.factor hJ') w = z) ↔ I ≤ J') := by
  obtain ⟨Kc, i1, i2, i3, i4, δ, hdd, hbdd, φ, hφ, Θ, hiso, hΘ⟩ :=
    AlgebraicGeometry.Polarisation.exists_free_complex_quasiIso_cech_sliceAt_stalk K f L hA g M hM N hN 𝒦 h𝒦 (κ.base y')
  refine ⟨Kc, i1, i2, i3, i4, hbdd, δ, hdd, hiso.1, hiso.2, Dressing.ker_stalkMap_le_maximalIdeal κ y',
    Dressing.exists_maximalIdeal_pow_le_ker_stalkMap K f κ hfin y', ?_, ?_⟩
  · exact AlgebraicGeometry.Polarisation.finrank_ker_baseChange_residue_eq_one_of_quasiIso_cech_sliceAt_stalk_of_forall
      K f L hc hA g M hM κ hκ hfin hK N hN 𝒦 h𝒦 (κ.base y') ⟨y', rfl⟩ Kc δ hdd hbdd φ hφ Θ ⟨hiso, hΘ⟩
  · intro J' hJ' hJ'N
    rw [AlgebraicGeometry.Polarisation.forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall
      K f L hA g M hM N hN 𝒦 h𝒦 (κ.base y') Kc δ hdd hbdd φ hφ Θ ⟨hiso, hΘ⟩ J' hJ' hJ'N,
      AlgebraicGeometry.Polarisation.forall_exists_pullbackSection_eq_iff_exists_comp_eq_of_mem_range
      K f L hc hA M hM κ hκ hfin hK N hN (κ.base y') ⟨y', rfl⟩ J' hJ' hJ'N]
    exact AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le κ y' J'

end S_AlgebraicGeometry_Polarisation_exists_free_complex_cech_sliceAt_stalk_and_seesaw
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_free_complex_cech_sliceAt_stalk_and_seesaw (solution)
