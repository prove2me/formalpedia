-- Prove2me | solution 1 for AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fabcf431-a120-5f0f-87eb-1762a77c624d

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_isIdempotentElem_map_eq_of_module_finite
import Theorems.Thm_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_henselianLocalRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

namespace SolPiAlg

section HenselLocal

open IsLocalRing

lemma isArtinianRing_quotient (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] :
    IsArtinianRing (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by

  letI : Algebra (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  haveI : IsScalarTower A (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact IsArtinianRing.of_finite (A ⧸ maximalIdeal A) _

lemma map_maximalIdeal_le_of_isMaximal (A : Type u) [CommRing A] [IsLocalRing A]
    {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B] (M : Ideal B) [hM : M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A B) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  have hmax : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := B) M
  exact (IsLocalRing.eq_maximalIdeal hmax).ge

theorem isLocalRing_of_forall_isIdempotentElem (A : Type u) [CommRing A] [HenselianLocalRing A]
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Nontrivial B]
    (h : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  classical
  haveI : IsArtinianRing (B ⧸ ((maximalIdeal A).map (algebraMap A B))) :=
    isArtinianRing_quotient A B

  have huniq : ∀ M₁ M₂ : Ideal B, M₁.IsMaximal → M₂.IsMaximal → M₁ = M₂ := by
    intro M₁ M₂ h₁ h₂
    by_contra hne
    have hJ₁ : ((maximalIdeal A).map (algebraMap A B)) ≤ M₁ := map_maximalIdeal_le_of_isMaximal A M₁
    have hJ₂ : ((maximalIdeal A).map (algebraMap A B)) ≤ M₂ := map_maximalIdeal_le_of_isMaximal A M₂

    have hk : RingHom.ker (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) =
        (maximalIdeal A).map (algebraMap A B) := Ideal.mk_ker
    have hp₁ : (M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (hk.symm ▸ hJ₁)
    have hp₂ : (M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (hk.symm ▸ hJ₂)
    have hc₁ : (M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).comap
        (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) = M₁ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        hk, sup_eq_left.mpr hJ₁]
    have hc₂ : (M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).comap
        (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) = M₂ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        hk, sup_eq_left.mpr hJ₂]
    have hp : M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) ≠
        M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) :=
      fun heq => hne (by rw [← hc₁, ← hc₂, heq])
    haveI := hp₁.isPrime
    obtain ⟨r, hr₁, hr, hr'⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne
      (M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))))
    have hr₂ : r ∈ M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) :=
      hr' _ hp₂.isPrime hp

    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective r

    obtain ⟨e, he, hemk⟩ :=
      HenselianLocalRing.exists_isIdempotentElem_map_eq_of_module_finite (R := A)
        (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)) x₀) hr
    rcases h e he with rfl | rfl
    · rw [map_zero] at hemk
      exact hr₁ (hemk ▸ Ideal.zero_mem _)
    · rw [map_one] at hemk
      exact hp₂.ne_top ((Ideal.eq_top_iff_one _).mpr (hemk ▸ hr₂))
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => huniq M' M hM' hM⟩

theorem comap_eq_maximalIdeal_iff (A : Type u) [CommRing A] [IsLocalRing A]
    {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (p : Ideal B) [p.IsPrime] :
    p.comap (algebraMap A B) = maximalIdeal A ↔ p = maximalIdeal B := by
  constructor
  · intro hp
    haveI : (p.comap (algebraMap A B)).IsMaximal := hp ▸ inferInstance
    haveI : p.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p this
    exact IsLocalRing.eq_maximalIdeal this
  · rintro rfl
    haveI : ((maximalIdeal B).comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    exact IsLocalRing.eq_maximalIdeal this

end HenselLocal

end SolPiAlg

namespace SolPiGeo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Topology TopologicalSpace

section Idem

lemma isUnit_iff_not_isUnit_one_sub_of_isIdempotentElem {R : Type*} [CommRing R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : IsUnit a ↔ ¬ IsUnit (1 - a) := by
  constructor
  · intro hu hu'

    have h1 : a = 1 := by
      obtain ⟨u, rfl⟩ := hu
      have := ha.eq
      calc (u : R) = ↑u * ↑u * ↑u⁻¹ := by rw [Units.mul_inv_cancel_right]
        _ = ↑u * ↑u⁻¹ := by rw [this]
        _ = 1 := Units.mul_inv _
    rw [h1, sub_self] at hu'
    exact not_isUnit_zero hu'
  · intro h
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self a).resolve_right h

theorem isIdempotentElem_eq_zero_or_one {Q : Scheme.{u}} [CompactSpace Q] [PreconnectedSpace Q]
    (e : Γ(Q, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by

  have hcompl : ((Q.basicOpen e : Set Q))ᶜ = (Q.basicOpen (1 - e) : Set Q) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]
    have hex : IsIdempotentElem (Q.presheaf.germ ⊤ x trivial e) := he.map _
    rw [isUnit_iff_not_isUnit_one_sub_of_isIdempotentElem hex, not_not]
  have hclopen : IsClopen (Q.basicOpen e : Set Q) := by
    refine ⟨?_, (Q.basicOpen e).isOpen⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (Q.basicOpen (1 - e)).isOpen
  rcases isClopen_iff.mp hclopen with h | h
  ·
    left
    have hbot : Q.basicOpen e = ⊥ := by
      apply TopologicalSpace.Opens.ext; simpa using h
    obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot e).mpr hbot
    calc e = e ^ (n + 1) := (he.pow_succ_eq n).symm
      _ = 0 := by rw [pow_succ, hn, zero_mul]
  ·
    right
    have hbot : Q.basicOpen (1 - e) = ⊥ := by
      apply TopologicalSpace.Opens.ext
      simp only [TopologicalSpace.Opens.coe_bot]
      rw [← hcompl, h, Set.compl_univ]
    obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot (1 - e)).mpr hbot
    have h1 : (1 - e) = 0 := by
      calc (1 - e) = (1 - e) ^ (n + 1) := (he.one_sub.pow_succ_eq n).symm
        _ = 0 := by rw [pow_succ, hn, zero_mul]
    exact (sub_eq_zero.mp h1).symm

end Idem

section Conn

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]

lemma apply_eq_comap_toSpecΓ {Q : Scheme.{u}} (g : Q ⟶ Spec (CommRingCat.of A)) (y : Q) :
    g y = PrimeSpectrum.comap (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (Q.toSpecΓ y) := by
  have hnat := Scheme.toSpecΓ_naturality g
  rw [← SpecMap_ΓSpecIso_hom] at hnat
  have h1 : (Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom) (g y)
      = (Spec.map g.appTop) (Q.toSpecΓ y) := by
    have := congrArg (fun h : Q ⟶ _ => h y) hnat
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using this
  rw [Spec.map_apply, Spec.map_apply] at h1
  have h2 := congrArg (PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) h1
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply] at h2
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) = RingHom.id A := by
    rw [← CommRingCat.hom_comp, CategoryTheory.Iso.inv_hom_id, CommRingCat.hom_id]
  rw [h3, PrimeSpectrum.comap_id] at h2
  exact h2

theorem isPreconnected_fibre_of_connectedSpace {Q : Scheme.{u}} (g : Q ⟶ Spec (CommRingCat.of A))
    [IsProper g] [ConnectedSpace Q] : _root_.IsPreconnected (g ⁻¹' {closedPoint A}) := by
  haveI : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace g

  let φ : A →+* Γ(Q, ⊤) := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  letI : Algebra A Γ(Q, ⊤) := φ.toAlgebra
  haveI : Module.Finite A Γ(Q, ⊤) := by
    have hF : g.appTop.hom.Finite :=
      AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing g
    have : φ.Finite := RingHom.Finite.comp hF (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective)
    exact this
  haveI : Nonempty (⊤ : Q.Opens) := ⟨⟨Classical.arbitrary Q, trivial⟩⟩
  haveI : Nontrivial Γ(Q, ⊤) := inferInstance
  haveI : IsLocalRing Γ(Q, ⊤) := SolPiAlg.isLocalRing_of_forall_isIdempotentElem A Γ(Q, ⊤)
    (fun e he => isIdempotentElem_eq_zero_or_one e he)
  haveI : IsNoetherianRing Γ(Q, ⊤) := IsNoetherianRing.of_finite A Γ(Q, ⊤)

  haveI : IsProper (Q.toSpecΓ ≫ Spec.map g.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]; infer_instance
  haveI : IsProper Q.toSpecΓ := IsProper.of_comp _ (Spec.map g.appTop)
  have hbij : Function.Bijective Q.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]; exact ConcreteCategory.bijective_of_isIso _

  have key : _root_.IsPreconnected (Q.toSpecΓ ⁻¹' {closedPoint Γ(Q, ⊤)}) :=
    AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
      (A := Γ(Q, ⊤)) Q.toSpecΓ hbij

  suffices hfib : g ⁻¹' {closedPoint A} = Q.toSpecΓ ⁻¹' {closedPoint Γ(Q, ⊤)} by
    rwa [hfib]
  ext y
  simp only [Set.mem_preimage]
  rw [apply_eq_comap_toSpecΓ g y]
  constructor
  · intro h
    have h' : (Q.toSpecΓ y).asIdeal.comap (algebraMap A Γ(Q, ⊤)) = maximalIdeal A :=
      congrArg PrimeSpectrum.asIdeal h
    exact PrimeSpectrum.ext ((SolPiAlg.comap_eq_maximalIdeal_iff A _).mp h')
  · intro h
    rw [h]
    exact PrimeSpectrum.ext ((SolPiAlg.comap_eq_maximalIdeal_iff A _).mpr rfl)

end Conn

section Components

theorem isOpen_connectedComponent' {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro z hz hzx
      have h1 : irreducibleComponent y ⊆ connectedComponent z :=
        isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent hz
      have h2 : connectedComponent x = connectedComponent z := connectedComponent_eq hzx
      exact hy (h2 ▸ h1 mem_irreducibleComponent)
    · rintro ⟨Z, ⟨-, hdisj⟩, hyZ⟩ hy
      exact Set.disjoint_left.mp hdisj hyZ hy
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1

end Components

section ClosedPointOfField

variable {R : Type u} [CommRing R] [IsLocalRing R] {K : Type u} [Field K]
  (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion ι]

lemma surjective_preimage : Function.Surjective (Spec.preimage ι).hom := by
  have h : Function.Surjective (ι.appTop) := ι.app_surjective ⊤ (isAffineOpen_top _)
  have hnat := Scheme.ΓSpecIso_naturality (Spec.preimage ι)
  rw [Spec.map_preimage] at hnat
  have heq : (Spec.preimage ι) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ι.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [hnat, CategoryTheory.Iso.inv_hom_id_assoc]
  have hsurj : Function.Surjective
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ι.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.surjective.comp h).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, by rw [heq]; exact hx⟩

lemma apply_eq_closedPoint (z : Spec (CommRingCat.of K)) : ι z = closedPoint R := by
  have hι : ι = Spec.map (Spec.preimage ι) := (Spec.map_preimage ι).symm
  rw [hι]
  apply PrimeSpectrum.ext
  change Ideal.comap (Spec.preimage ι).hom z.asIdeal = maximalIdeal R
  have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top
  rw [hz, ← RingHom.ker_eq_comap_bot]
  exact IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ (surjective_preimage ι))

lemma range_eq : Set.range ι = {closedPoint R} := by
  ext p
  simp only [Set.mem_range]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ apply_eq_closedPoint ι z, fun h => ⟨closedPoint K, h ▸ apply_eq_closedPoint ι _⟩⟩

end ClosedPointOfField

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
  [IsClosedImmersion ι]

lemma isPreconnected_preimage_connectedComponent (x : P) :
    _root_.IsPreconnected (pullback.fst q ι ⁻¹' connectedComponent x) := by
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  haveI : IsNoetherian P := {}

  let U : P.Opens := ⟨connectedComponent x, isOpen_connectedComponent' x⟩
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  haveI : ConnectedSpace (U : Scheme.{u}) := ‹ConnectedSpace U›
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have h1 : _root_.IsPreconnected ((U.ι ≫ q) ⁻¹' {closedPoint A}) :=
    isPreconnected_fibre_of_connectedSpace (U.ι ≫ q)
  have h2 : _root_.IsPreconnected (U.ι '' ((U.ι ≫ q) ⁻¹' {closedPoint A})) :=
    h1.image _ U.ι.continuous.continuousOn
  have h3 : U.ι '' ((U.ι ≫ q) ⁻¹' {closedPoint A}) = connectedComponent x ∩ q ⁻¹' {closedPoint A} := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage, Scheme.Hom.comp_base,
      TopCat.coe_comp, Function.comp_apply, Set.mem_inter_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨by simp [Scheme.Opens.ι_apply], hz⟩
    · rintro ⟨hy, hqy⟩
      exact ⟨⟨y, hy⟩, by simpa [Scheme.Opens.ι_apply] using hqy, rfl⟩
  rw [h3] at h2

  have hrange : Set.range (pullback.fst q ι) = q ⁻¹' {closedPoint A} := by
    rw [Scheme.Pullback.range_fst, range_eq ι]
  have h4 : pullback.fst q ι ⁻¹' connectedComponent x
      = pullback.fst q ι ⁻¹' (connectedComponent x ∩ q ⁻¹' {closedPoint A}) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_inter_iff, iff_self_and]
    intro _
    have : pullback.fst q ι w ∈ Set.range (pullback.fst q ι) := ⟨w, rfl⟩
    rw [hrange] at this
    exact this
  rw [h4]
  refine ((pullback.fst q ι).isEmbedding.isInducing.isPreconnected_image).mp ?_
  rwa [Set.image_preimage_eq_of_subset]
  rw [hrange]
  exact Set.inter_subset_right

theorem main (V₀ : Set ↥(pullback q ι)) (hV₀ : IsClopen V₀) :
    ∃ V : Set P, IsClopen V ∧ pullback.fst q ι ⁻¹' V = V₀ := by
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  haveI : IsNoetherian P := {}
  let f := pullback.fst q ι
  refine ⟨⋃ z ∈ V₀, connectedComponent (f z), ⟨?_, ?_⟩, ?_⟩
  ·
    rw [← isOpen_compl_iff]
    have : (⋃ z ∈ V₀, connectedComponent (f z))ᶜ =
        ⋃ y ∈ (⋃ z ∈ V₀, connectedComponent (f z))ᶜ, connectedComponent y := by
      apply subset_antisymm
      · intro y hy
        exact Set.mem_biUnion hy mem_connectedComponent
      · intro w hw
        simp only [Set.mem_iUnion, Set.mem_compl_iff, exists_prop, not_exists, not_and] at hw ⊢
        obtain ⟨y, hy, hwy⟩ := hw
        intro z hz hwz
        have e1 : connectedComponent (f z) = connectedComponent w := connectedComponent_eq hwz
        have e2 : connectedComponent y = connectedComponent w := connectedComponent_eq hwy
        exact hy z hz (by rw [e1, ← e2]; exact mem_connectedComponent)
    rw [this]
    exact isOpen_biUnion fun y _ => isOpen_connectedComponent' y
  · exact isOpen_biUnion fun z _ => isOpen_connectedComponent' (f z)
  · apply subset_antisymm
    · intro w hw
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop] at hw
      obtain ⟨z, hz, hwz⟩ := hw
      have hpc := isPreconnected_preimage_connectedComponent q ι (f z)
      have hsub : f ⁻¹' connectedComponent (f z) ⊆ V₀ :=
        hpc.subset_isClopen hV₀ ⟨z, mem_connectedComponent, hz⟩
      exact hsub hwz
    · intro z hz
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
      exact ⟨z, hz, mem_connectedComponent⟩

end Main

end SolPiGeo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion ι]
    (V₀ : Set ↥(pullback q ι)) (hV₀ : IsClopen V₀) :
    ∃ V : Set P, IsClopen V ∧ pullback.fst q ι ⁻¹' V = V₀ :=
  SolPiGeo.main q ι V₀ hV₀

end S_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_henselianLocalRing (solution)
