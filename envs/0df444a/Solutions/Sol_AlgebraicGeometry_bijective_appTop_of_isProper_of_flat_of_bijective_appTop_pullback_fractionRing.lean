-- Prove2me | solution 1 for AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_bijective_appTop_pullback_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/19ee2102-21f2-5112-8233-5c7dbd37fd9b

import Mathlib
import Theorems.Thm_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_bijective_appTop_pullback_fractionRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of A)) [IsProper πX] [Flat πX]
    (hK : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap A K)))).appTop).hom) :
    Function.Bijective πX.appTop := by
  classical
  set e := Scheme.ΓSpecIso (CommRingCat.of A) with he
  let φA : CommRingCat.of A ⟶ Γ(X, ⊤) := e.inv ≫ πX.appTop

  have htf : ∀ (a : A), a ≠ 0 → ∀ r : Γ(X, ⊤), φA.hom a * r = 0 → r = 0 := by
    intro a ha r hr
    apply X.sheaf.eq_of_locally_eq' (fun U : X.affineOpens => (U : X.Opens)) ⊤ (fun U => homOfLE le_top)
      (by rw [iSup_affineOpens_eq_top])
    intro U
    show X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op r = X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op 0
    rw [map_zero]
    have hflat : (πX.appLE ⊤ U le_top).hom.Flat :=
      HasRingHomProperty.appLE @Flat πX inferInstance ⟨⊤, isAffineOpen_top _⟩ U le_top
    have hflat' : (e.inv ≫ πX.appLE ⊤ U le_top).hom.Flat := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e.inv)) hflat
    letI alg : Algebra A Γ(X, U) := (e.inv ≫ πX.appLE ⊤ U le_top).hom.toAlgebra
    haveI : Module.Flat A Γ(X, U) := hflat'
    have key : φA ≫ X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op = e.inv ≫ πX.appLE ⊤ U le_top := by
      simp only [φA, Category.assoc, Scheme.Hom.appTop, Scheme.Hom.appLE]
      rfl
    have hsm : (a : A) • (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op r) =
        (a : A) • (0 : Γ(X, U)) := by
      rw [smul_zero, Algebra.smul_def]
      show (e.inv ≫ πX.appLE ⊤ U le_top).hom a * _ = 0
      rw [← key, CommRingCat.hom_comp, RingHom.comp_apply, ← map_mul, hr, map_zero]
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha) hsm

  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace πX
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated πX
  haveI : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have hpo := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat πX K
  rw [← he] at hpo

  set sK := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap A K)))).appTop with hsK
  set fT := (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap A K)))).appTop with hfT
  have hw : ∀ a : A, sK.hom (algebraMap A K a) = fT.hom (φA.hom a) := by
    intro a
    have := congrArg (fun k => k.hom a) hpo.w
    simp at this
    exact this

  have inj1 : Function.Injective φA.hom := by
    intro a b hab
    have := congrArg fT.hom hab
    rw [← hw, ← hw] at this
    exact IsFractionRing.injective A K (hK.1 this)

  letI algR : Algebra A Γ(X, ⊤) := φA.hom.toAlgebra
  have hpo' := CommRingCat.isPushout_tensorProduct A K Γ(X, ⊤)
  have eφ : CommRingCat.ofHom (algebraMap A Γ(X, ⊤)) = φA := rfl
  rw [eφ] at hpo'
  let iso := hpo'.isoIsPushout _ _ hpo
  have hinr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := Γ(X, ⊤))).toRingHom ≫ iso.hom = fT :=
    hpo'.inr_isoIsPushout_hom _ _ hpo
  have inj2 : Function.Injective fT.hom := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro r hr
    have h1 : (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := Γ(X, ⊤))) r = 0 := by
      apply (ConcreteCategory.bijective_of_isIso iso.hom).1
      rw [map_zero]
      have := congrArg (fun k => k.hom r) hinr
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      rw [← hr]; exact this
    have h2 : (TensorProduct.mk A K Γ(X, ⊤) 1) r = 0 := h1
    rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors A) (TensorProduct.mk A K Γ(X, ⊤) 1)] at h2
    obtain ⟨s', hs'⟩ := h2
    have : (s' : A) • r = 0 := hs'
    rw [Algebra.smul_def] at this
    exact htf s' (nonZeroDivisors.coe_ne_zero s') r this

  have hfin : φA.hom.Finite := by
    have h := AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing πX
    have : φA.hom = πX.appTop.hom.comp e.inv.hom := rfl
    rw [this]
    exact RingHom.Finite.comp h (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)
  haveI : Module.Finite A Γ(X, ⊤) := hfin
  let eK : Γ(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap A K))), ⊤) ≃+* K := (RingEquiv.ofBijective sK.hom hK).symm
  have heK : ∀ y : K, eK (sK.hom y) = y := fun y => (RingEquiv.ofBijective sK.hom hK).symm_apply_apply y
  let g : Γ(X, ⊤) →ₐ[A] K :=
    { toRingHom := eK.toRingHom.comp fT.hom
      commutes' := by
        intro a
        show eK (fT.hom (φA.hom a)) = algebraMap A K a
        rw [← hw, heK] }
  have surj1 : Function.Surjective φA.hom := by
    intro r
    have hint : IsIntegral A (g r) := (Algebra.IsIntegral.isIntegral (R := A) r).map g
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hint
    refine ⟨a, inj2 ?_⟩
    apply eK.injective
    show g (φA.hom a) = g r
    rw [← ha]; exact g.commutes a

  have : πX.appTop = e.hom ≫ φA := by simp [φA]
  rw [this]
  show Function.Bijective (φA.hom.comp e.hom.hom)
  rw [RingHom.coe_comp]
  exact Function.Bijective.comp ⟨inj1, surj1⟩ (ConcreteCategory.bijective_of_isIso e.hom)

end S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_bijective_appTop_pullback_fractionRing
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_bijective_appTop_pullback_fractionRing (solution)
