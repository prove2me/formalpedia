-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/eddcae18-b9f4-59ac-ab72-1fcdb7000266

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct
open scoped TensorProduct

namespace ChiFibre

section Conj

variable {R : Type*} [CommRing R] {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

noncomputable def kerEquivOfConj (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : ∀ x, eN (f x) = f' (eM x)) : LinearMap.ker f ≃ₗ[R] LinearMap.ker f' :=
  LinearEquiv.ofSubmodules eM (LinearMap.ker f) (LinearMap.ker f') (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, ← h, hx, map_zero]
    · intro hy
      refine ⟨eM.symm y, ?_, by simp⟩
      apply eN.injective
      rw [h, LinearEquiv.apply_symm_apply, hy, map_zero])

noncomputable def cokerEquivOfConj (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : ∀ x, eN (f x) = f' (eM x)) : (N ⧸ LinearMap.range f) ≃ₗ[R] (N' ⧸ LinearMap.range f') :=
  Submodule.Quotient.equiv (LinearMap.range f) (LinearMap.range f') eN (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨eM x, (h x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f (eM.symm x), ⟨_, rfl⟩, by rw [LinearEquiv.coe_coe, h, LinearEquiv.apply_symm_apply]⟩)

end Conj

section Coker

variable {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem nonempty_cokerBaseChangeEquiv (d : C0 →ₗ[R] C1) (A : Type*) [CommRing A] [Algebra R A] :
    Nonempty (((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) ≃ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  let q : C1 →ₗ[R] C1 ⧸ LinearMap.range d := (LinearMap.range d).mkQ
  let qA : A ⊗[R] C1 →ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d) := q.baseChange A
  have hsurj : Function.Surjective qA := by
    rw [show (qA : A ⊗[R] C1 → A ⊗[R] (C1 ⧸ LinearMap.range d)) = LinearMap.lTensor A q from
      LinearMap.baseChange_eq_ltensor q]
    exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker qA = LinearMap.range (d.baseChange A) := by
    have h1 : LinearMap.ker (LinearMap.lTensor A q) = LinearMap.range (LinearMap.lTensor A d) := by
      rw [lTensor_mkQ]
      have hd : d = (LinearMap.range d).subtype ∘ₗ d.rangeRestrict := LinearMap.ext fun _ => rfl
      conv_rhs => rw [hd, LinearMap.lTensor_comp]
      rw [LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.mpr (LinearMap.lTensor_surjective A (LinearMap.surjective_rangeRestrict d))
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have hx : qA x = LinearMap.lTensor A q x := congrFun (LinearMap.baseChange_eq_ltensor q) x
    rw [hx, ← LinearMap.mem_ker, h1, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y).symm⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (qA.quotKerEquivOfSurjective hsurj)⟩

end Coker

section FieldExt

variable {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem nonempty_kerBaseChangeEquiv_of_flat {K : Type*} [CommRing K] {V0 V1 : Type*} [AddCommGroup V0] [Module K V0]
    [AddCommGroup V1] [Module K V1] (δ : V0 →ₗ[K] V1) (K' : Type*) [CommRing K'] [Algebra K K'] [Module.Flat K K'] :
    Nonempty (LinearMap.ker (δ.baseChange K') ≃ₗ[K'] K' ⊗[K] LinearMap.ker δ) := by
  let ι : K' ⊗[K] LinearMap.ker δ →ₗ[K'] K' ⊗[K] V0 := (LinearMap.ker δ).subtype.baseChange K'
  have hι : ∀ x, δ.baseChange K' (ι x) = 0 := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  let j : K' ⊗[K] LinearMap.ker δ →ₗ[K'] LinearMap.ker (δ.baseChange K') := ι.codRestrict _ hι
  have hinj : Function.Injective j := by
    intro x y hxy
    have : ι x = ι y := congrArg Subtype.val hxy
    have hιinj : Function.Injective ι := by
      rw [show (ι : K' ⊗[K] LinearMap.ker δ → K' ⊗[K] V0) = LinearMap.lTensor K' (LinearMap.ker δ).subtype from
        LinearMap.baseChange_eq_ltensor _]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact hιinj this
  have hsurj : Function.Surjective j := by
    rintro ⟨x, hx⟩
    have hex : Function.Exact (LinearMap.lTensor K' (LinearMap.ker δ).subtype) (LinearMap.lTensor K' δ) :=
      Module.Flat.lTensor_exact K' (LinearMap.exact_subtype_ker_map δ)
    have hx' : LinearMap.lTensor K' δ x = 0 := by
      rw [← congrFun (LinearMap.baseChange_eq_ltensor δ) x]; exact hx
    obtain ⟨y, hy⟩ := (hex x).mp hx'
    refine ⟨y, Subtype.ext ?_⟩
    change ι y = x
    rw [← hy]
    exact congrFun (LinearMap.baseChange_eq_ltensor _) y
  exact ⟨(LinearEquiv.ofBijective j ⟨hinj, hsurj⟩).symm⟩

theorem baseChange_baseChange_conj (d : C0 →ₗ[R] C1) (K K' : Type*) [CommRing K] [CommRing K'] [Algebra R K]
    [Algebra R K'] [Algebra K K'] [IsScalarTower R K K'] (x : K' ⊗[K] (K ⊗[R] C0)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1 ((d.baseChange K).baseChange K' x) =
      d.baseChange K' (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0 x) := by
  rw [LinearMap.baseChange_baseChange]
  simp

theorem finrank_ker_coker_baseChange_field {K : Type*} [Field K] {V0 V1 : Type*} [AddCommGroup V0] [Module K V0]
    [AddCommGroup V1] [Module K V1] (δ : V0 →ₗ[K] V1) (K' : Type*) [Field K'] [Algebra K K'] :
    Module.finrank K' (LinearMap.ker (δ.baseChange K')) = Module.finrank K (LinearMap.ker δ) ∧
    Module.finrank K' ((K' ⊗[K] V1) ⧸ LinearMap.range (δ.baseChange K')) =
      Module.finrank K (V1 ⧸ LinearMap.range δ) := by
  obtain ⟨eker⟩ := nonempty_kerBaseChangeEquiv_of_flat δ K'
  obtain ⟨ecok⟩ := nonempty_cokerBaseChangeEquiv δ K'
  exact ⟨eker.finrank_eq.trans Module.finrank_baseChange, ecok.finrank_eq.trans Module.finrank_baseChange⟩

theorem finrank_ker_coker_baseChange_eq (d : C0 →ₗ[R] C1) (K K' : Type*) [Field K] [Field K'] [Algebra R K]
    [Algebra R K'] [Algebra K K'] [IsScalarTower R K K'] :
    Module.finrank K' (LinearMap.ker (d.baseChange K')) = Module.finrank K (LinearMap.ker (d.baseChange K)) ∧
    Module.finrank K' ((K' ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K')) =
      Module.finrank K ((K ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K)) := by
  have hconj := baseChange_baseChange_conj d K K'
  let eK : LinearMap.ker ((d.baseChange K).baseChange K') ≃ₗ[K'] LinearMap.ker (d.baseChange K') :=
    kerEquivOfConj _ _ (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1) hconj
  let eC : ((K' ⊗[K] (K ⊗[R] C1)) ⧸ LinearMap.range ((d.baseChange K).baseChange K')) ≃ₗ[K']
      ((K' ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K')) :=
    cokerEquivOfConj _ _ (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1) hconj
  obtain ⟨hk, hc⟩ := finrank_ker_coker_baseChange_field (d.baseChange K) K'
  exact ⟨eK.finrank_eq.symm.trans hk, eC.finrank_eq.symm.trans hc⟩

end FieldExt

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

end ChiFibre

open ChiFibre in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T) [IsOpenImmersion j]
    {CA : Scheme.{u}} (πA : CA ⟶ Spec (CommRingCat.of A)) (g' : CA ⟶ pullback c t)
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : PrimeSpectrum A)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (hs : s.base (IsLocalRing.closedPoint k) = j.base 𝔭) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      ∀ (M : (pullback c t).Modules), Scheme.Modules.IsInvertible M →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 =
          Module.finrank 𝔭.asIdeal.ResidueField
            (LinearMap.ker ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
              𝔭.asIdeal.ResidueField)) ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 =
          Module.finrank 𝔭.asIdeal.ResidueField
            ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).M01) ⧸
              LinearMap.range ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
                𝔭.asIdeal.ResidueField)) := by
  classical

  obtain ⟨s', hs'⟩ : ∃ s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A), s' ≫ j = s := by
    refine ⟨IsOpenImmersion.lift j s ?_, IsOpenImmersion.lift_fac j s _⟩
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k), hs]
    exact ⟨𝔭, rfl⟩
  subst hs'

  letI : Algebra A k := (Spec.preimage s').hom.toAlgebra
  have hsp : Scheme.TwoAffineOpenCover.specMap A k = s' := by
    have h1 : CommRingCat.ofHom (algebraMap A k) = Spec.preimage s' := by ext a; rfl
    rw [Scheme.TwoAffineOpenCover.specMap, h1, Spec.map_preimage]

  have hpt : (Scheme.TwoAffineOpenCover.specMap A k).base (IsLocalRing.closedPoint k) = 𝔭 := by
    apply j.isOpenEmbedding.injective
    rw [hsp]
    simpa using hs
  have hker : RingHom.ker (algebraMap A k) = 𝔭.asIdeal := by
    have h1 := congrArg PrimeSpectrum.asIdeal hpt
    have hmax : (IsLocalRing.closedPoint k).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
    have h2 : ((Scheme.TwoAffineOpenCover.specMap A k).base (IsLocalRing.closedPoint k)).asIdeal =
        Ideal.comap (algebraMap A k) (IsLocalRing.closedPoint k).asIdeal := rfl
    rw [h2, hmax, ← RingHom.ker_eq_comap_bot] at h1
    exact h1

  have hle : 𝔭.asIdeal ≤ RingHom.ker (algebraMap A k) := hker.symm.le
  have hunit : 𝔭.asIdeal.primeCompl ≤ Submonoid.comap (algebraMap A k) (IsUnit.submonoid k) := by
    intro x hx
    rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hker ▸ (RingHom.mem_ker.mpr h0))
  letI : Algebra 𝔭.asIdeal.ResidueField k :=
    (Ideal.ResidueField.lift 𝔭.asIdeal (algebraMap A k) hle hunit).toAlgebra
  haveI : IsScalarTower A 𝔭.asIdeal.ResidueField k := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap 𝔭.asIdeal (algebraMap A k) hle hunit b).symm

  set sp := Scheme.TwoAffineOpenCover.specMap A k with hspdef
  have hcartY : IsPullback (pullback.fst πA sp ≫ g') (pullback.snd πA sp) (pullback.snd c t) (s' ≫ j) := by
    rw [← hsp]
    exact (IsPullback.of_hasPullback πA sp).paste_horiz hcart
  let Φ : pullback πA sp ≅ pullback (pullback.snd c t) (s' ≫ j) := hcartY.isoPullback
  have hΦfst : Φ.hom ≫ pullback.fst (pullback.snd c t) (s' ≫ j) = pullback.fst πA sp ≫ g' :=
    hcartY.isoPullback_hom_fst
  have hΦsnd : Φ.hom ≫ pullback.snd (pullback.snd c t) (s' ≫ j) = pullback.snd πA sp :=
    hcartY.isoPullback_hom_snd
  have hΦinv_snd : Φ.symm.hom ≫ pullback.snd πA sp = fibreAt c t (s' ≫ j) := by
    rw [Iso.symm_hom, ← hΦsnd, Iso.inv_hom_id_assoc]; rfl
  have hΦinv_fst : pullback.fst (pullback.snd c t) (s' ≫ j) = Φ.inv ≫ (pullback.fst πA sp ≫ g') := by
    rw [← hΦfst, Iso.inv_hom_id_assoc]

  have eM : ∀ M : (pullback c t).Modules,
      (fibreModule c t (s' ≫ j) M ≅ (Scheme.Modules.pullback Φ.symm.hom).obj
        ((Scheme.Modules.pullback (pullback.fst πA sp)).obj ((Scheme.Modules.pullback g').obj M))) := fun M =>
    (Scheme.Modules.pullbackCongr hΦinv_fst).app M ≪≫
      ((Scheme.Modules.pullbackComp Φ.inv (pullback.fst πA sp ≫ g')).app M).symm ≪≫
      (Scheme.Modules.pullback Φ.inv).mapIso ((Scheme.Modules.pullbackComp (pullback.fst πA sp) g').app M).symm

  obtain ⟨𝒲₀, h00, h01, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (fibreAt c t (s' ≫ j)) (pullback.snd πA sp)
      Φ.symm hΦinv_snd (𝒱.pullback πA k) _ _ (eM (SheafOfModules.unit (pullback c t).ringCatSheaf : (pullback c t).Modules))
  refine ⟨𝒲₀, fun M hM => ?_⟩
  obtain ⟨𝒲, h0, h1, ⟨f0⟩, ⟨f1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (fibreAt c t (s' ≫ j)) (pullback.snd πA sp)
      Φ.symm hΦinv_snd (𝒱.pullback πA k) _ _ (eM M)
  obtain rfl : 𝒲 = 𝒲₀ := cover_ext (h0.trans h00.symm) (h1.trans h01.symm)
  rw [f0.finrank_eq, f1.finrank_eq]

  have hMA : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback g').obj M) := hM.pullback g'
  obtain ⟨⟨eH1⟩, ⟨eH0⟩, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 πA
      ((Scheme.Modules.pullback g').obj M) hMA.1 k
  obtain ⟨ecok⟩ := nonempty_cokerBaseChangeEquiv (𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff k
  obtain ⟨hker', hcoker'⟩ := finrank_ker_coker_baseChange_eq
    (𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff 𝔭.asIdeal.ResidueField k
  constructor
  · rw [eH0.finrank_eq, hker']
  · rw [eH1.finrank_eq, ← ecok.finrank_eq, hcoker']

end S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField (solution)
