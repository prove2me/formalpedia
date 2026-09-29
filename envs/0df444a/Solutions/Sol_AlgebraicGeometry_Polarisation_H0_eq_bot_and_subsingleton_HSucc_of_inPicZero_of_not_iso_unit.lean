-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f6781e88-0e85-5c0d-81b2-2c77f102599c

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_tensor_pullback_eq_sum_mul_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Polarisation_isIso_lift_fst_addMor
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_addMor_iso_tensor_of_mumfordBundle_iso_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_tensorUnit_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules
import Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_sections_of_inPicZero_of_not_iso_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_iff_nonempty_mumfordBundle_iso_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_tensorUnit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule CochainCx.Bounded.abGrp CochainCx.Bounded.modR"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

set_option maxHeartbeats 1600000

namespace P2mAcyclic

p2m_open "AlgebraicGeometry.OModulePresheaf~zero"

theorem dims_eq_zero_of_kunneth (h h' : ℕ → ℕ) (h'0 : 1 ≤ h' 0) (h0 : h 0 = 0)
    (hK : ∀ n, ∑ i ∈ Finset.range (n + 1), h' i * h (n - i) = ∑ i ∈ Finset.range (n + 1), h i * h (n - i)) :
    ∀ n, h n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0
    have hR : ∑ i ∈ Finset.range (n + 1), h i * h (n - i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rcases lt_or_ge i n with hlt | hge
      · rw [ih i hlt, zero_mul]
      · have : i = n := by omega
        subst this
        rw [Nat.sub_self, h0, mul_zero]
    have hL : h' 0 * h n ≤ ∑ i ∈ Finset.range (n + 1), h' i * h (n - i) := by
      have := Finset.single_le_sum (f := fun i => h' i * h (n - i)) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.succ_pos n))
      simpa using this
    rw [hK n, hR] at hL
    have : h n ≤ h' 0 * h n := Nat.le_mul_of_pos_left _ h'0
    omega

theorem nonempty_orderedAffineCover (X : Scheme.{0}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical
  let 𝒱 := X.affineCover.finiteSubcover
  letI : LinearOrder 𝒱.I₀ := LinearOrder.lift' (Fintype.equivFin 𝒱.I₀) (Fintype.equivFin 𝒱.I₀).injective
  exact ⟨Scheme.OrderedAffineCover.mk (ι := 𝒱.I₀) (U := fun j => (𝒱.f j).opensRange)
    (isAffineOpen := fun j => isAffineOpen_opensRange (𝒱.f j)) (iSup_eq_top := 𝒱.iSup_opensRange)⟩

end P2mAcyclic

open P2mAcyclic in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : InPicZero f L M) (hM1 : ¬ Nonempty (M ≅ 𝟙_ (A.Modules))) (𝒰 : A.OrderedAffineCover) :
    (OModulePresheaf.ofModules f M).H0 𝒰 = ⊥ ∧ ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules f M).HSucc 𝒰 i) := by
  classical

  haveI hP : IsProper f := hA.proper
  have hMinv : Scheme.Modules.IsInvertible M := hM.1
  have h1inv : Scheme.Modules.IsInvertible (𝟙_ A.Modules) := (inPicZero_tensorUnit k f L).1

  have hΛ := (inPicZero_iff_nonempty_mumfordBundle_iso_unit k f L hc hA M hMinv).mp hM
  obtain ⟨eμ⟩ := nonempty_pullback_addMor_iso_tensor_of_mumfordBundle_iso_unit f L M hMinv hΛ

  haveI : CompactSpace ↑(pullback f f) := by
    haveI : QuasiCompact (pullback.fst f f ≫ f) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f ≫ f)
  obtain ⟨𝔚⟩ := nonempty_orderedAffineCover (pullback f f)

  have KD1 := OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper f f (𝟙_ A.Modules) h1inv M hMinv 𝒰 𝒰 𝔚
  have KD2 := OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper f f M hMinv M hMinv 𝒰 𝒰 𝔚

  set Φ := pullback.lift (pullback.fst f f) (addMor f L) (addMor_over f L).symm with hΦ
  haveI : IsIso Φ := isIso_lift_fst_addMor f L
  haveI : IsSeparated (pullback.fst f f ≫ f) := inferInstance
  have hΦfst : Φ ≫ pullback.fst f f = pullback.fst f f := pullback.lift_fst _ _ _
  have hΦsnd : Φ ≫ pullback.snd f f = addMor f L := pullback.lift_snd _ _ _
  have AI := fun n => OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso (pullback.fst f f ≫ f) Φ
    ((Scheme.Modules.pullback (pullback.snd f f)).obj M) (hMinv.pullback _) 𝔚 𝔚 n

  have eΦ : (Scheme.Modules.pullback Φ).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj M) ≅
      (Scheme.Modules.pullback (addMor f L)).obj M :=
    ((Scheme.Modules.pullbackComp Φ (pullback.snd f f)).app M) ≪≫ (Scheme.Modules.pullbackCongr hΦsnd).app M
  have e1 : (Scheme.Modules.pullback (pullback.fst f f)).obj (𝟙_ A.Modules) ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj M ≅
      (Scheme.Modules.pullback (pullback.snd f f)).obj M :=
    (whiskerRightIso (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst f f)) _) ≪≫ λ_ _

  set h : ℕ → ℕ := fun n => (OModulePresheaf.ofModules f M).cechFinrank 𝒰 n with hh
  set h' : ℕ → ℕ := fun n => (OModulePresheaf.ofModules f (𝟙_ A.Modules)).cechFinrank 𝒰 n with hh'

  have hK : ∀ n, ∑ i ∈ Finset.range (n + 1), h' i * h (n - i) = ∑ i ∈ Finset.range (n + 1), h i * h (n - i) := by
    intro n
    have hπ : Φ ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f := by rw [← Category.assoc, hΦfst]

    have a1 := KD1 n
    have a2 : (OModulePresheaf.ofModules (pullback.fst f f ≫ f)
        ((Scheme.Modules.pullback (pullback.fst f f)).obj (𝟙_ A.Modules) ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj M)).cechFinrank 𝔚 n =
        (OModulePresheaf.ofModules (pullback.fst f f ≫ f) ((Scheme.Modules.pullback (pullback.snd f f)).obj M)).cechFinrank 𝔚 n := by
      obtain ⟨⟨q0⟩, qS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso (pullback.fst f f ≫ f) e1 𝔚
      cases n with
      | zero => rw [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero]; exact q0.finrank_eq
      | succ i => rw [OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ]; obtain ⟨q⟩ := qS i; exact q.finrank_eq

    have a3 := AI n
    have a4 : (OModulePresheaf.ofModules (Φ ≫ (pullback.fst f f ≫ f))
        ((Scheme.Modules.pullback Φ).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj M))).cechFinrank 𝔚 n =
        (OModulePresheaf.ofModules (pullback.fst f f ≫ f)
          ((Scheme.Modules.pullback (pullback.fst f f)).obj M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj M)).cechFinrank 𝔚 n := by
      rw [hπ]
      obtain ⟨⟨q0⟩, qS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso (pullback.fst f f ≫ f) (eΦ ≪≫ eμ) 𝔚
      cases n with
      | zero => rw [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero]; exact q0.finrank_eq
      | succ i => rw [OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ]; obtain ⟨q⟩ := qS i; exact q.finrank_eq
    have a5 := KD2 n
    simp only [hh, hh']
    rw [← a1, a2, ← a3, a4, a5]

  have h'0 : 1 ≤ h' 0 := by
    simp only [hh']
    obtain ⟨⟨u0⟩, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_tensorUnit_unit f 𝒰
    rw [OModulePresheaf.cechFinrank_zero, u0.finrank_eq, ← OModulePresheaf.cechFinrank_zero,
      GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one k f hA 𝒰]
  have h0 : h 0 = 0 := by
    simp only [hh]
    haveI := subsingleton_sections_of_inPicZero_of_not_iso_unit k f L hc hA M hM hM1
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
    obtain ⟨s0⟩ := OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules f M 𝒰
    rw [OModulePresheaf.cechFinrank_zero, ← s0.finrank_eq]
    exact Module.finrank_zero_of_subsingleton
  have hzero := dims_eq_zero_of_kunneth h h' h'0 h0 hK

  have hfin : (OModulePresheaf.ofModules f M).CechFinite 𝒰 :=
    OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f M hMinv.exists_trivialization 𝒰
  refine ⟨?_, fun i => ?_⟩
  · haveI := hfin.1
    have := hzero 0
    simp only [hh, OModulePresheaf.cechFinrank_zero] at this
    haveI hs : Subsingleton ((OModulePresheaf.ofModules f M).H0 𝒰) := Module.finrank_zero_iff.mp this
    exact (Submodule.eq_bot_iff _).mpr fun x hx =>
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : (OModulePresheaf.ofModules f M).H0 𝒰) ⟨0, Submodule.zero_mem _⟩)
  · haveI := hfin.2 i
    have := hzero (i + 1)
    simp only [hh, OModulePresheaf.cechFinrank_succ] at this
    exact Module.finrank_zero_iff.mp this

end S_AlgebraicGeometry_Polarisation_H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit (solution)
