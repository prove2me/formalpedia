-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.finrank_H0_baseChange_residue_sliceAt_stalk_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/590c51f1-172b-5952-885e-a29802a3b233

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
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_tensorUnit_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_unit_zero_eq_one_of_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_finrank_H0_baseChange_residue_sliceAt_stalk_eq_one
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation Opposite"

namespace SeesawGeo

noncomputable def isoOfIsoPullback {X Y : Scheme.{0}} (i : Y ⟶ X) [IsIso i] {P Q : X.Modules}
    (e : (Scheme.Modules.pullback i).obj P ≅ (Scheme.Modules.pullback i).obj Q) : P ≅ Q :=
  ((Scheme.Modules.pullbackId X).app P).symm ≪≫
    (Scheme.Modules.pullbackCongr (show 𝟙 X = inv i ≫ i by simp)).app P ≪≫
    ((Scheme.Modules.pullbackComp (inv i) i).app P).symm ≪≫
    (Scheme.Modules.pullback (inv i)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (inv i) i).app Q ≪≫
    (Scheme.Modules.pullbackCongr (show inv i ≫ i = 𝟙 X by simp)).app Q ≪≫
    (Scheme.Modules.pullbackId X).app Q

theorem nonempty_iso_unit_of_isLocalRing (R : Type) [CommRing R] [IsLocalRing R]
    (L : (Spec (CommRingCat.of R)).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of R)).Modules) := by
  obtain ⟨U, hU, ⟨eU⟩⟩ := hL.exists_trivialization (IsLocalRing.closedPoint R)
  have hU' : U = ⊤ := (IsLocalRing.closed_point_mem_iff (R := R)).mp hU
  subst hU'
  haveI : IsIso (⊤ : (Spec (CommRingCat.of R)).Opens).ι := (Scheme.topIso _).isIso_hom
  exact ⟨isoOfIsoPullback (⊤ : (Spec (CommRingCat.of R)).Opens).ι
    (eU ≪≫ (Scheme.Modules.pullbackUnitIso (⊤ : (Spec (CommRingCat.of R)).Opens).ι).symm)⟩

theorem locIsoOnBase_iff_of_isLocalRing {B : Type} [CommRing B] [IsLocalRing B] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of B)) (P Q : X.Modules) :
    LocIsoOnBase q P Q ↔ Nonempty (P ≅ Q) := by
  constructor
  · intro h
    obtain ⟨U, hU, ⟨e⟩⟩ := h (IsLocalRing.closedPoint B)
    have hU' : U = ⊤ := (IsLocalRing.closed_point_mem_iff (R := B)).mp hU
    subst hU'
    rw [Scheme.Hom.preimage_top] at e
    haveI : IsIso (⊤ : X.Opens).ι := (Scheme.topIso _).isIso_hom
    exact ⟨isoOfIsoPullback (⊤ : X.Opens).ι e⟩
  · rintro ⟨e⟩ s
    exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem isLocalRing_quotient {R : Type} [CommRing R] [IsLocalRing R] (J : Ideal R)
    (hJ : J ≤ IsLocalRing.maximalIdeal R) : IsLocalRing (R ⧸ J) := by
  have hJt : J ≠ ⊤ := fun h => IsLocalRing.maximalIdeal.isMaximal R |>.ne_top (top_le_iff.mp (h ▸ hJ))
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJt
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

theorem subsingleton_primeSpectrum_quotient {R : Type} [CommRing R] [IsLocalRing R] (J : Ideal R)
    (hJ : J ≤ IsLocalRing.maximalIdeal R) (hJN : ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ J) :
    Subsingleton (PrimeSpectrum (R ⧸ J)) := by
  obtain ⟨n, hn⟩ := hJN

  have key : ∀ p : PrimeSpectrum (R ⧸ J), p.asIdeal = (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J) := by
    intro p
    have hle : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J) ≤ p.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      have hrn : (Ideal.Quotient.mk J r) ^ n = 0 := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact hn (Ideal.pow_mem_pow hr n)
      exact p.isPrime.mem_of_pow_mem n (by rw [hrn]; exact zero_mem _)
    have hmax : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J)).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
          (IsLocalRing.maximalIdeal.isMaximal R) with h | h
      · exfalso
        have h2 : Ideal.comap (Ideal.Quotient.mk J) ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J)) =
            IsLocalRing.maximalIdeal R := by
          rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
            Ideal.mk_ker]
          exact sup_eq_left.mpr hJ
        rw [h, Ideal.comap_top] at h2
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2.symm
      · exact h
    exact (hmax.eq_of_le p.isPrime.ne_top hle).symm
  exact ⟨fun p q => PrimeSpectrum.ext (by rw [key p, key q])⟩

end SeesawGeo

namespace SeesawMain

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
  {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) in
theorem sliceAt_fst : sliceAt f x ≫ pullback.fst f f = pullback.fst f t := by
  unfold sliceAt
  exact pullback.lift_fst _ _ _

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
  {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) in
theorem sliceAt_snd : sliceAt f x ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by
  unfold sliceAt
  exact pullback.lift_snd _ _ _

theorem trivLink (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A)
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (R : Type) [CommRing R] (bR : Spec (CommRingCat.of R) ⟶ A)
    (J : Ideal R) (hloc : IsLocalRing (R ⧸ J)) :
    (∃ t : Spec (CommRingCat.of (R ⧸ J)) ⟶ KM, t ≫ κ = Scheme.TwoAffineOpenCover.specMap R (R ⧸ J) ≫ bR) ↔
      Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (bR ≫ f)) (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj
        ((Scheme.Modules.pullback (sliceAt f (⟨bR, rfl⟩ : SchemeHomOver (bR ≫ f) f))).obj
          (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)) ≅ 𝟙_ _) := by
  haveI := hloc

  let tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
  let xR : SchemeHomOver tR f := ⟨bR, rfl⟩
  let π : pullback f tR ⟶ Spec (CommRingCat.of R) := pullback.snd f tR
  let spB : Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec (CommRingCat.of R) := Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)
  let bB : Spec (CommRingCat.of (R ⧸ J)) ⟶ A := spB ≫ bR
  let tB : Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec (CommRingCat.of K) := spB ≫ tR
  let xB : SchemeHomOver tB f := ⟨bB, Category.assoc _ _ _⟩
  let F' : (pullback f f).Modules := mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N
  let SΛ : (pullback f tB).Modules := (Scheme.Modules.pullback (sliceAt f xB)).obj (mumfordBundle f L M)
  let SB : (pullback f tB).Modules := (Scheme.Modules.pullback (sliceAt f xB)).obj F'
  let FB := (Scheme.Modules.pullback (pullback.fst π spB)).obj ((Scheme.Modules.pullback (sliceAt f xR)).obj F')
  show (∃ t : Spec (CommRingCat.of (R ⧸ J)) ⟶ KM, t ≫ κ = bB) ↔ Nonempty (FB ≅ 𝟙_ _)

  have e1 : (∃ t : Spec (CommRingCat.of (R ⧸ J)) ⟶ KM, t ≫ κ = bB) ↔ Nonempty (SΛ ≅ 𝟙_ _) := by
    rw [hK (R ⧸ J) tB xB, isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit K f L M hM (R ⧸ J) tB xB,
      SeesawGeo.locIsoOnBase_iff_of_isLocalRing]

  have hsl : sliceAt f xB ≫ pullback.snd f f = pullback.snd f tB ≫ bB := sliceAt_snd f xB
  obtain ⟨ν⟩ := SeesawGeo.nonempty_iso_unit_of_isLocalRing (R ⧸ J) ((Scheme.Modules.pullback bB).obj N) (hN.pullback bB)
  let τ : (Scheme.Modules.pullback (sliceAt f xB)).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj N) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp (sliceAt f xB) (pullback.snd f f)).app N ≪≫
      (Scheme.Modules.pullbackCongr hsl).app N ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f tB) bB).app N).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd f tB)).mapIso ν ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd f tB)

  let σ : SB ≅ SΛ :=
    Scheme.Modules.pullbackTensorObjIso (sliceAt f xB) (mumfordBundle f L M) _ ≪≫ whiskerLeftIso SΛ τ ≪≫ ρ_ SΛ
  have e2 : Nonempty (SΛ ≅ 𝟙_ _) ↔ Nonempty (SB ≅ 𝟙_ _) :=
    ⟨fun ⟨e⟩ => ⟨σ ≪≫ e⟩, fun ⟨e⟩ => ⟨σ.symm ≪≫ e⟩⟩

  have hcond : pullback.fst π spB ≫ pullback.snd f tR = pullback.snd π spB ≫ spB := pullback.condition
  have hw1 : (pullback.fst π spB ≫ pullback.fst f tR) ≫ f = pullback.snd π spB ≫ tB := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hcond, Category.assoc]
  let p : pullback π spB ⟶ pullback f tB := pullback.lift (pullback.fst π spB ≫ pullback.fst f tR) (pullback.snd π spB) hw1
  have hp1 : p ≫ pullback.fst f tB = pullback.fst π spB ≫ pullback.fst f tR := pullback.lift_fst _ _ _
  have hp2 : p ≫ pullback.snd f tB = pullback.snd π spB := pullback.lift_snd _ _ _
  have hp : p ≫ sliceAt f xB = pullback.fst π spB ≫ sliceAt f xR := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, sliceAt_fst, sliceAt_fst, hp1]
    · rw [Category.assoc, Category.assoc, sliceAt_snd, sliceAt_snd, ← Category.assoc, hp2,
        ← Category.assoc (pullback.fst π spB), hcond, Category.assoc]
  have hw2 : pullback.fst f tB ≫ f = (pullback.snd f tB ≫ spB) ≫ tR := by
    rw [pullback.condition, Category.assoc]
  let q1 : pullback f tB ⟶ pullback f tR := pullback.lift (pullback.fst f tB) (pullback.snd f tB ≫ spB) hw2
  have hq11 : q1 ≫ pullback.fst f tR = pullback.fst f tB := pullback.lift_fst _ _ _
  have hq12 : q1 ≫ pullback.snd f tR = pullback.snd f tB ≫ spB := pullback.lift_snd _ _ _
  let q : pullback f tB ⟶ pullback π spB := pullback.lift q1 (pullback.snd f tB) hq12
  have hq1 : q ≫ pullback.fst π spB = q1 := pullback.lift_fst _ _ _
  have hq : q ≫ (pullback.fst π spB ≫ sliceAt f xR) = sliceAt f xB := by
    apply pullback.hom_ext
    · rw [sliceAt_fst, Category.assoc, Category.assoc, sliceAt_fst, ← Category.assoc, hq1, hq11]
    · rw [sliceAt_snd, Category.assoc, Category.assoc, sliceAt_snd, ← Category.assoc, hq1, ← Category.assoc, hq12,
        Category.assoc]
  have e3 : Nonempty (SB ≅ 𝟙_ _) ↔ Nonempty (FB ≅ 𝟙_ _) := by
    constructor
    · rintro ⟨e⟩
      exact ⟨(Scheme.Modules.pullbackComp (pullback.fst π spB) (sliceAt f xR)).app F' ≪≫
        (Scheme.Modules.pullbackCongr hp.symm).app F' ≪≫
        ((Scheme.Modules.pullbackComp p (sliceAt f xB)).app F').symm ≪≫
        (Scheme.Modules.pullback p).mapIso e ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso p⟩
    · rintro ⟨e⟩
      exact ⟨(Scheme.Modules.pullbackCongr hq.symm).app F' ≪≫
        ((Scheme.Modules.pullbackComp q (pullback.fst π spB ≫ sliceAt f xR)).app F').symm ≪≫
        (Scheme.Modules.pullback q).mapIso
          (((Scheme.Modules.pullbackComp (pullback.fst π spB) (sliceAt f xR)).app F').symm ≪≫ e) ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso q⟩
  exact e1.trans (e2.trans e3)

end SeesawMain

namespace SeesawMain

theorem specMap_quot {R : Type} [CommRing R] (J : Ideal R) :
    Scheme.TwoAffineOpenCover.specMap R (R ⧸ J) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ J))) = _
  rw [Ideal.Quotient.algebraMap_eq]

end SeesawMain

namespace SeesawMain

theorem bijective_sections_quotient (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (R : Type) [CommRing R] (bR : Spec (CommRingCat.of R) ⟶ A) (I : Ideal R) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv ≫
      (pullback.snd (pullback.snd f (bR ≫ f)) (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I))).appTop).hom := by
  let π := pullback.snd f (bR ≫ f)
  let spk := Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)
  let φ : CommRingCat.of K ⟶ CommRingCat.of (R ⧸ I) := Spec.preimage (spk ≫ (bR ≫ f))
  have hφ : Spec.map (CommRingCat.ofHom φ.hom) = spk ≫ (bR ≫ f) := by
    rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage _
  have hsq : IsPullback (pullback.fst π spk ≫ pullback.fst f (bR ≫ f)) (pullback.snd π spk) f
      (Spec.map (CommRingCat.ofHom φ.hom)) := by
    rw [hφ]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback π spk) (IsPullback.of_hasPullback f (bR ≫ f))
  exact hA.bijective_specIso_inv_comp_appTop_of_isPullback φ.hom (pullback.snd π spk)
    (pullback.fst π spk ≫ pullback.fst f (bR ≫ f)) hsq

theorem finrank_H0_eq_one_of_iso_unit {R : Type} [CommRing R] (I : Ideal R) {X : Scheme.{0}}
    (πk : X ⟶ Spec (CommRingCat.of (R ⧸ I)))
    (hsep : IsSeparated πk) (F : X.Modules) (e : F ≅ 𝟙_ X.Modules)
    (hbij : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv ≫ πk.appTop).hom)
    (Kc : X.OrderedAffineCover) :
    Module.finrank (R ⧸ I) ((OModulePresheaf.ofModules πk F).H0 Kc) = 1 := by
  haveI := hsep
  obtain ⟨⟨e1⟩, -, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso πk e Kc
  rw [e1.finrank_eq]
  obtain ⟨⟨e2⟩, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_tensorUnit_unit πk Kc
  rw [e2.finrank_eq, ← OModulePresheaf.cechFinrank_zero]
  refine OModulePresheaf.cechFinrank_unit_zero_eq_one_of_bijective πk ?_ Kc
  have happ : πk.appLE ⊤ ⊤ le_top = πk.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  show Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv ≫ πk.appLE ⊤ ⊤ le_top).hom
  rw [happ]
  exact hbij

end SeesawMain

open SeesawMain in
open TensorProduct in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) (hy : y ∈ Set.range κ.base) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI π : pullback f tR ⟶ Spec (CommRingCat.of R) := pullback.snd f tR
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI kk : Type := R ⧸ IsLocalRing.maximalIdeal R
    Module.finrank kk
      ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R kk))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R kk))).obj FR)).H0 (𝒦R.baseChange π kk)) = 1 := by
  obtain ⟨y', rfl⟩ := hy
  haveI : IsClosedImmersion κ := hκ
  have ik : IsLocalRing ((A.presheaf.stalk (κ.base y')) ⧸ IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y'))) :=
    SeesawGeo.isLocalRing_quotient _ le_rfl

  have hk := trivLink K f L M hM κ hK N hN (↥(A.presheaf.stalk (κ.base y'))) (A.fromSpecStalk (κ.base y'))
    (IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y'))) ik
  have hker : RingHom.ker (κ.stalkMap y').hom ≤ IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y')) :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hfk := (IsClosedImmersion.exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le κ y' _).mpr hker
  rw [← specMap_quot] at hfk
  obtain ⟨ek⟩ := hk.mp hfk

  haveI : IsProper f := hA.proper
  have hbij := bijective_sections_quotient K f hA (↥(A.presheaf.stalk (κ.base y'))) (A.fromSpecStalk (κ.base y'))
    (IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y')))
  have hsep1 : IsSeparated (pullback.snd f (A.fromSpecStalk (κ.base y') ≫ f)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hsep2 : IsSeparated (pullback.snd (pullback.snd f (A.fromSpecStalk (κ.base y') ≫ f))
      (Scheme.TwoAffineOpenCover.specMap (↥(A.presheaf.stalk (κ.base y')))
        ((A.presheaf.stalk (κ.base y')) ⧸ IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y'))))) :=
    MorphismProperty.pullback_snd _ _ hsep1
  exact finrank_H0_eq_one_of_iso_unit (IsLocalRing.maximalIdeal (A.presheaf.stalk (κ.base y'))) _ hsep2 _ ek hbij _

end S_AlgebraicGeometry_Polarisation_finrank_H0_baseChange_residue_sliceAt_stalk_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_finrank_H0_baseChange_residue_sliceAt_stalk_eq_one (solution)
