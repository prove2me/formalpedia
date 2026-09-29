-- Prove2me | solution 1 for AlgebraicGeometry.connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8885a62b-2a48-5008-aaca-2e975582abff

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Theorems.Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

namespace GC3bWitt

open WittVector

variable (M : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [CharP k ℓ]

local notation "ZM" => Localization.Away ((M : ℕ) : ℤ)

theorem natCast_witt_ne_zero (n : ℕ) (hn : n ≠ 0) : (n : WittVector ℓ k) ≠ 0 := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ (Fact.out : ℓ.Prime).ne_one
  rw [Nat.cast_mul, Nat.cast_pow]
  refine mul_ne_zero (pow_ne_zero _ (WittVector.p_nonzero ℓ k)) ?_
  have hunit : IsUnit (m : WittVector ℓ k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, map_natCast]
    intro h
    exact hm ((CharP.cast_eq_zero_iff k ℓ m).mp h)
  exact hunit.ne_zero

theorem intCast_witt_injective : Function.Injective (Int.castRingHom (WittVector ℓ k)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rcases Int.natAbs_eq z with h | h
  · rw [h] at hz ⊢
    by_contra h0
    exact natCast_witt_ne_zero ℓ k z.natAbs (by exact_mod_cast h0) (by simpa using hz)
  · rw [h] at hz ⊢
    by_contra h0
    have : (z.natAbs : WittVector ℓ k) = 0 := by simpa using hz
    exact natCast_witt_ne_zero ℓ k z.natAbs (by intro h1; apply h0; simp [h1]) this

scoped instance flat_int : Module.Flat ℤ (WittVector ℓ k) := by
  haveI : Module.IsTorsionFree ℤ (WittVector ℓ k) := Module.IsTorsionFree.of_smul_eq_zero fun z w h => by
    rw [zsmul_eq_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (intCast_witt_injective ℓ k (by simpa using h))
    · exact Or.inr h
  infer_instance

variable (hM : ((M : ℕ) : k) ≠ 0)

include hM in
theorem isUnit_witt_natCast : IsUnit ((M : ℕ) : WittVector ℓ k) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [← WittVector.constantCoeff_apply, map_natCast]
  exact hM

def φ : ZM →+* WittVector ℓ k :=
  IsLocalization.Away.lift ((M : ℕ) : ℤ) (g := Int.castRingHom (WittVector ℓ k))
    (by rw [map_natCast]; exact isUnit_witt_natCast M ℓ k hM)

theorem φ_comp_algebraMap : (φ M ℓ k hM).comp (algebraMap ℤ ZM) = Int.castRingHom (WittVector ℓ k) :=
  IsLocalization.Away.lift_comp ((M : ℕ) : ℤ) _

theorem flat_witt : letI : Algebra ZM (WittVector ℓ k) := (φ M ℓ k hM).toAlgebra; Module.Flat ZM (WittVector ℓ k) := by
  letI alg : Algebra ZM (WittVector ℓ k) := (φ M ℓ k hM).toAlgebra
  have hM0 : ((M : ℕ) : ℤ) ≠ 0 := by
    have : (M : ℕ) ≠ 0 := by rintro h0; exact hM (by simp [h0])
    exact_mod_cast this
  haveI : IsDomain ZM := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hM0)
  haveI : IsDedekindDomain ZM :=
    IsLocalization.isDedekindDomain ℤ (powers_le_nonZeroDivisors_of_noZeroDivisors hM0) ZM

  have hinj : Function.Injective (algebraMap ZM (WittVector ℓ k)) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers ((M : ℕ) : ℤ)) r
    have hunit : IsUnit (algebraMap ZM (WittVector ℓ k) (algebraMap ℤ ZM (s : ℤ))) :=
      (IsLocalization.map_units ZM s).map _
    have ha : algebraMap ZM (WittVector ℓ k) (algebraMap ℤ ZM a) = 0 := by
      have := congrArg (fun x => x * algebraMap ZM (WittVector ℓ k) (algebraMap ℤ ZM (s : ℤ))) hr
      simp only [zero_mul] at this
      rwa [← map_mul, IsLocalization.mk'_spec] at this
    have ha0 : a = 0 := by
      apply intCast_witt_injective ℓ k
      show Int.castRingHom (WittVector ℓ k) a = Int.castRingHom (WittVector ℓ k) 0
      rw [map_zero, ← φ_comp_algebraMap M ℓ k hM]
      exact ha
    subst ha0
    show IsLocalization.mk' ZM (0 : ℤ) s = 0
    exact IsLocalization.mk'_zero s
  haveI : Module.IsTorsionFree ZM (WittVector ℓ k) := Module.IsTorsionFree.of_smul_eq_zero fun r w h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  infer_instance

theorem constantCoeff_comp_φ (σ : ZM →+* k) : (WittVector.constantCoeff : WittVector ℓ k →+* k).comp (φ M ℓ k hM) = σ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ((M : ℕ) : ℤ))
  rw [RingHom.comp_assoc, φ_comp_algebraMap]
  apply RingHom.ext_int

omit [CharP k ℓ] in
theorem constantCoeff_surjective' : Function.Surjective (WittVector.constantCoeff : WittVector ℓ k →+* k) :=
  WittVector.constantCoeff_surjective ℓ

theorem ker_constantCoeff_eq_maximalIdeal [PerfectRing k ℓ] :
    RingHom.ker (WittVector.constantCoeff : WittVector ℓ k →+* k) = IsLocalRing.maximalIdeal (WittVector ℓ k) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (WittVector.constantCoeff_surjective ℓ))

end GC3bWitt
p2m_reactivate "P2MW.S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop.GC3bWitt"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop.GC3bWitt"

noncomputable section

namespace GC3bCore

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option synthInstance.maxHeartbeats 1600000

theorem core (M : ℕ) [NeZero M]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))) [IsProper πX] [Flat πX]
    (hΓ : Function.Bijective πX.appTop)
    (k : Type) [Field k]
    (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra (Localization.Away ((M : ℕ) : ℤ)) R] [Module.Flat (Localization.Away ((M : ℕ) : ℤ)) R]
    (ρ : R →+* k) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R) :
    ConnectedSpace ↥(pullback πX (Spec.map (CommRingCat.ofHom (ρ.comp (algebraMap (Localization.Away ((M : ℕ) : ℤ)) R))))) := by
  classical
  set g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away ((M : ℕ) : ℤ)) R)) with hg
  set t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ρ) with ht
  have hst : Spec.map (CommRingCat.ofHom (ρ.comp (algebraMap (Localization.Away ((M : ℕ) : ℤ)) R))) = t ≫ g := by
    rw [ht, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hst]

  let q := pullback.snd πX g
  haveI : IsProper q := inferInstance

  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace πX
  haveI : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated πX
  have hq : Function.Bijective q.appTop := by
    have H := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat πX R
    haveI : IsIso πX.appTop := (ConcreteCategory.isIso_iff_bijective πX.appTop).mpr hΓ
    haveI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))).inv ≫ πX.appTop) := inferInstance
    haveI hinl := H.isIso_inl_of_isIso
    haveI : IsIso q.appTop := by
      have : q.appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop) := by
        rw [Iso.hom_inv_id_assoc]
      rw [this]; infer_instance
    exact ConcreteCategory.bijective_of_isIso q.appTop

  have hpre : _root_.IsPreconnected (q ⁻¹' {IsLocalRing.closedPoint R} : Set ↥(pullback πX g)) :=
    AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop q hq

  haveI : IsClosedImmersion t := by
    rw [ht]; exact IsClosedImmersion.spec_of_surjective _ hρ
  have hrange_t : Set.range t.base = {IsLocalRing.closedPoint R} := by
    have h1 : Set.range t.base = Set.range (PrimeSpectrum.comap ρ) := by rw [ht]; rfl
    rw [h1, range_comap_of_surjective _ ρ hρ, hker]
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff, SetLike.coe_subset_coe]
    constructor
    · intro hp
      exact PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le p.2.ne_top hp).symm
    · rintro rfl; exact le_rfl
  let e : pullback q t ≅ pullback πX (t ≫ g) := pullbackLeftPullbackSndIso πX g t
  have hrange : Set.range (pullback.fst q t).base = q ⁻¹' {IsLocalRing.closedPoint R} := by
    rw [Scheme.Pullback.range_fst, hrange_t]
  haveI : PreconnectedSpace ↥(pullback q t) := by
    constructor
    have hemb := (pullback.fst q t).isClosedEmbedding.isInducing
    rw [← hemb.isPreconnected_image, Set.image_univ, hrange]
    exact hpre

  have hne : (q ⁻¹' {IsLocalRing.closedPoint R} : Set ↥(pullback πX g)).Nonempty := by

    have hXne : Nonempty ↥(pullback πX g) := by
      by_contra hempty
      haveI : IsEmpty ↥(pullback πX g) := not_nonempty_iff.mp hempty
      have htop : (⊤ : (pullback πX g).Opens) = ⊥ := by ext x; exact (IsEmpty.false x).elim
      have hterm : Limits.IsTerminal ((pullback πX g).presheaf.obj (Opposite.op ⊤)) := by
        rw [htop]; exact (pullback πX g).sheaf.isTerminalOfEmpty
      haveI hsub : Subsingleton ↑((pullback πX g).presheaf.obj (Opposite.op ⊤)) := CommRingCat.subsingleton_of_isTerminal hterm
      have h01 : (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv 0)) = q.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv 1) :=
        Subsingleton.elim _ _
      have := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective (hq.1 h01)
      exact zero_ne_one this
    obtain ⟨x⟩ := hXne
    have hclosed : IsClosed (Set.range q.base) := q.isClosedMap.isClosed_range
    have hmem : IsLocalRing.closedPoint R ∈ Set.range q.base :=
      (IsLocalRing.specializes_closedPoint (q.base x)).mem_closed hclosed ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := hmem
    exact ⟨x', hx'⟩
  haveI : Nonempty ↥(pullback q t) := by
    obtain ⟨x, hx⟩ := hne
    rw [← hrange] at hx
    obtain ⟨y, -⟩ := hx
    exact ⟨y⟩

  let eh := Scheme.Hom.homeomorph e.hom
  haveI : Nonempty ↥(pullback πX (t ≫ g)) := ⟨eh (Classical.arbitrary _)⟩
  refine { isPreconnected_univ := ?_, toNonempty := inferInstance }
  rw [← eh.range_coe, ← Set.image_univ]
  exact (PreconnectedSpace.isPreconnected_univ).image _ eh.continuous.continuousOn

end GC3bCore
p2m_reactivate "P2MW.S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop.GC3bWitt"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop.GC3bWitt"

section Solution

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))) [IsProper πX] [Flat πX]
    (hΓ : Function.Bijective πX.appTop)
    (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))) :
    ConnectedSpace ↥(pullback πX s) := by
  classical

  let σ' : CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)) ⟶ CommRingCat.of k :=
    (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))).inv ≫ s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom
  have hs : s = Spec.map σ' := by
    have hnat := Scheme.toSpecΓ_naturality s
    rw [← SpecMap_ΓSpecIso_hom, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp] at hnat
    have := congrArg (fun u => u ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))).inv) hnat
    simp only [Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id] at this
    exact this
  let σ : Localization.Away ((M : ℕ) : ℤ) →+* k := σ'.hom
  have hσ' : σ' = CommRingCat.ofHom σ := rfl
  rw [hs, hσ']

  have hMk : ((M : ℕ) : k) ≠ 0 := by
    have hu : IsUnit (algebraMap ℤ (Localization.Away ((M : ℕ) : ℤ)) ((M : ℕ) : ℤ)) :=
      IsLocalization.Away.algebraMap_isUnit ((M : ℕ) : ℤ)
    have := (hu.map σ).ne_zero
    rwa [map_natCast, map_natCast] at this

  obtain hchar | ⟨p, ⟨hp⟩, hcp⟩ := CharP.exists' k
  ·
    letI alg : Algebra (Localization.Away ((M : ℕ) : ℤ)) k := σ.toAlgebra
    have hM0 : ((M : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    haveI : IsDomain (Localization.Away ((M : ℕ) : ℤ)) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hM0)
    haveI : IsDedekindDomain (Localization.Away ((M : ℕ) : ℤ)) :=
      IsLocalization.isDedekindDomain ℤ (powers_le_nonZeroDivisors_of_noZeroDivisors hM0) _
    have hinj : Function.Injective (algebraMap (Localization.Away ((M : ℕ) : ℤ)) k) := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers ((M : ℕ) : ℤ)) r
      have ha : algebraMap (Localization.Away ((M : ℕ) : ℤ)) k (algebraMap ℤ _ a) = 0 := by
        have := congrArg (fun x => x * algebraMap (Localization.Away ((M : ℕ) : ℤ)) k (algebraMap ℤ _ (t : ℤ))) hr
        simp only [zero_mul] at this
        rwa [← map_mul, IsLocalization.mk'_spec] at this
      have ha0 : a = 0 := by
        have hza : ((algebraMap (Localization.Away ((M : ℕ) : ℤ)) k).comp (algebraMap ℤ _)) a = 0 := ha
        rw [(RingHom.ext_int ((algebraMap (Localization.Away ((M : ℕ) : ℤ)) k).comp (algebraMap ℤ _)) (Int.castRingHom k))] at hza
        haveI : CharZero k := hchar
        exact Int.cast_eq_zero.mp hza
      subst ha0
      exact IsLocalization.mk'_zero t
    haveI : Module.IsTorsionFree (Localization.Away ((M : ℕ) : ℤ)) k := Module.IsTorsionFree.of_smul_eq_zero fun r w h => by
      rw [Algebra.smul_def] at h
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (hinj (by rw [h, map_zero]))
      · exact Or.inr h
    haveI : Module.Flat (Localization.Away ((M : ℕ) : ℤ)) k := inferInstance
    have hker : RingHom.ker (RingHom.id k) = IsLocalRing.maximalIdeal k := by
      ext x
      simp only [RingHom.mem_ker, RingHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
    have := GC3bCore.core M X πX hΓ k k (RingHom.id k) Function.surjective_id hker
    simp at this
    exact this
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : ExpChar k p := ExpChar.prime hp
    haveI : PerfectRing k p := PerfectField.toPerfectRing p
    letI alg : Algebra (Localization.Away ((M : ℕ) : ℤ)) (WittVector p k) := (GC3bWitt.φ M p k hMk).toAlgebra
    haveI : Module.Flat (Localization.Away ((M : ℕ) : ℤ)) (WittVector p k) := GC3bWitt.flat_witt M p k hMk
    have hcomp : (WittVector.constantCoeff : WittVector p k →+* k).comp (algebraMap (Localization.Away ((M : ℕ) : ℤ)) (WittVector p k)) = σ :=
      GC3bWitt.constantCoeff_comp_φ M p k hMk σ
    have := GC3bCore.core M X πX hΓ k (WittVector p k) WittVector.constantCoeff
      (WittVector.constantCoeff_surjective p) (GC3bWitt.ker_constantCoeff_eq_maximalIdeal p k)
    rwa [hcomp] at this

end Solution
p2m_reactivate "P2MW.S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop.GC3bWitt"

end S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop (solution)
