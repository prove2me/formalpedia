-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/15cf72df-0243-58ac-9dcb-9b52cf2aa205

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum

open scoped InnerProductSpace BigOperators

noncomputable section

namespace SphericalCutScalar

variable (F : Type) [Field F] [NumberField F]

private theorem ext_of_glArch_of_glFin {x y : AdelicGL2 (𝓞 F) F}
    (ha : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (hf : glFin (𝓞 F) F x = glFin (𝓞 F) F y) :
    x = y := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) ha
  · exact congrArg
      (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
        (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) hf

private theorem commute_of_glArch_eq_one {r s : AdelicGL2 (𝓞 F) F}
    (hr : glArch (𝓞 F) F r = 1) (hs : glFin (𝓞 F) F s = 1) : Commute r s := by
  show r * s = s * r
  refine ext_of_glArch_of_glFin F ?_ ?_
  · rw [map_mul, map_mul, hr, one_mul, mul_one]
  · rw [map_mul, map_mul, hs, one_mul, mul_one]

private theorem commute_rowIsometryInclAt₀ {r : AdelicGL2 (𝓞 F) F}
    (hr : r ∈ finiteAdelicGL2Subgroup F) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) : Commute r (rowIsometryInclAt₀ F w k) :=
  commute_of_glArch_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F r).mp hr)
    (glFin_rowIsometryInclAt₀ F w k)

private theorem comp_mul_mem_archCutSubmodule_of_mem {tys : ArchTypeFamily F}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys)
    {r : AdelicGL2 (𝓞 F) F} (hr : r ∈ finiteAdelicGL2Subgroup F) :
    (fun x => φ (x * r)) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun φ => (fun x => φ (x * r)) ∈
      ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) (hφ w) ?_ ?_ ?_
  · intro i φ hφi
    exact le_iSup (fun j => archTypeSubmoduleAt F w (tys.rep w j)) i
      (comp_mul_mem_typeSubmodule_of_commute hφi r fun k' => commute_rowIsometryInclAt₀ F hr w k')
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

private theorem levelInvariant_iff {pins : CarrierPins F} {N : Ideal (𝓞 F)}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} :
    φ ∈ levelInvariantSubmodule F pins N ↔
      ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U N, φ (g * u) = φ g :=
  Iff.rfl

private theorem rightTranslate_mem_levelInvariantSubmodule {pins : CarrierPins F}
    {N : Ideal (𝓞 F)} (hU : pins.U N ≤ finiteAdelicGL2Subgroup F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ levelInvariantSubmodule F pins N) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ levelInvariantSubmodule F pins N := by
  refine (levelInvariant_iff F).mpr fun g u hu => ?_
  show φ (g * u * rowIsometryInclAt₀ F w k) = φ (g * rowIsometryInclAt₀ F w k)
  rw [mul_assoc, (commute_rowIsometryInclAt₀ F (hU hu) w k).eq, ← mul_assoc]
  exact (levelInvariant_iff F).mp hφ _ u hu

private theorem rightTranslate_sub_smul (g : AdelicGL2 (𝓞 F) F) (a b : AdelicGL2 (𝓞 F) F → ℂ)
    (c : ℂ) : rightTranslate F g (a - c • b) = rightTranslate F g a - c • rightTranslate F g b :=
  rfl

private theorem isArchBiFinite_and_forall_mul_left {tys : ArchTypeFamily F}
    {U : Subgroup (AdelicGL2 (𝓞 F) F)} (hU : U ≤ finiteAdelicGL2Subgroup F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsLevelSphericalOfType F tys U f) :
    IsArchBiFinite F tys f ∧ ∀ y : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f (u * y) = f y := by
  obtain ⟨fa, -, hB, -, hfeq⟩ := hf
  refine ⟨IsArchBiFinite.of_factorization F (fa := fa)
    (ff := Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) fun _ => (1 : ℂ)) hfeq hB,
    fun y u hu => ?_⟩
  have h1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp (hU hu)
  have hiff : glFin (𝓞 F) F u * glFin (𝓞 F) F y ∈ glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)) ↔
      glFin (𝓞 F) F y ∈ glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
    constructor
    · rintro ⟨k, hk, hk'⟩
      refine ⟨u⁻¹ * k, U.mul_mem (U.inv_mem hu) hk, ?_⟩
      rw [map_mul, map_inv, hk', inv_mul_cancel_left]
    · rintro ⟨k, hk, hk'⟩
      exact ⟨u * k, U.mul_mem hu hk, by rw [map_mul, hk']⟩
  rw [hfeq, hfeq, map_mul, map_mul, h1, one_mul]
  by_cases hy : glFin (𝓞 F) F y ∈ glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.mpr hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (mt hiff.mp hy)]

private theorem rightConv_apply_mul_of_forall_mul_left {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) {h : AdelicGL2 (𝓞 F) F → ℂ}
    (hh : ∀ y : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * y) = h y)
    (x : AdelicGL2 (𝓞 F) F) {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ U) :
    rightConv F ψ h (x * u) = rightConv F ψ h x := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  simp only [rightConv_apply]
  calc ∫ y, ψ (x * u * y) * h y ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ y, (fun z => ψ (x * z) * h (u⁻¹ * z)) (u * y) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        congr 1
        funext y
        simp only [mul_assoc, inv_mul_cancel_left]
    _ = ∫ z, ψ (x * z) * h (u⁻¹ * z) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
        MeasureTheory.integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
          (fun z => ψ (x * z) * h (u⁻¹ * z)) u
    _ = ∫ z, ψ (x * z) * h z ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        congr 1
        funext z
        rw [hh z u⁻¹ (U.inv_mem hu)]

private theorem rightConv_sub_smul_left {a b h : AdelicGL2 (𝓞 F) F → ℂ} (ha : Continuous a)
    (hb : Continuous b) (hh : Continuous h) (hhc : HasCompactSupport h) (c : ℂ) :
    rightConv F (a - c • b) h = rightConv F a h - c • rightConv F b h := by
  have h1 : a - c • b = a + (-c) • b := by rw [neg_smul, sub_eq_add_neg]
  have h2 : rightConv F ((-c) • b) h = (-c) • rightConv F b h := convOp_smul F h (-c) b
  have hcb : Continuous ((-c) • b) := hb.const_smul (-c)
  rw [h1, rightConv_add_left F ha hcb hh hhc, h2, neg_smul, sub_eq_add_neg]

private theorem sum_apply_mul_mul_eq {G : Type*} [Group G] {U : Subgroup G} {g : G} {n : ℕ}
    {reps : Fin n → G}
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u')
    (hcov : ∀ x : G, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j)
    {φ : G → ℂ} (hφ : ∀ x : G, ∀ u ∈ U, φ (x * u) = φ x) (x : G) {u₀ : G} (hu₀ : u₀ ∈ U) :
    ∑ i, φ (x * u₀ * reps i) = ∑ i, φ (x * reps i) := by
  have hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps :=
    { mem_doubleCoset := fun i => by
        obtain ⟨u, hu, u', hu', hi⟩ := hreps i
        exact HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, u', hu', hi.symm⟩
      covers := fun y hy => by
        obtain ⟨u, hu, u', hu', hy'⟩ := HeckePair.mem_doubleCoset_iff.mp hy
        obtain ⟨i, w, hw, hyi⟩ := hcov y ⟨u, hu, u', hu', hy'.symm⟩
        refine ⟨i, QuotientGroup.eq.mpr ?_⟩
        rw [hyi, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact U.inv_mem hw
      mk_injective := fun i j hij => hinj i j (QuotientGroup.eq.mp hij) }
  have hsys' : HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => u₀ * reps i) :=
    { mem_doubleCoset := fun i => HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu₀
      covers := fun y hy => by
        obtain ⟨i, hi⟩ :=
          hsys.covers (u₀⁻¹ * y) (HeckePair.mul_mem_doubleCoset hy (U.inv_mem hu₀))
        refine ⟨i, QuotientGroup.eq.mpr ?_⟩
        have h := QuotientGroup.eq.mp hi
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
      mk_injective := fun i j hij => by
        apply hsys.mk_injective
        apply QuotientGroup.eq.mpr
        have h := QuotientGroup.eq.mp hij
        simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h }
  calc ∑ i, φ (x * u₀ * reps i) = ∑ i, φ (x * (u₀ * reps i)) := by simp only [mul_assoc]
    _ = ∑ i, φ (x * reps i) :=
        HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys hsys' hφ x

private def shiftRange (X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hX : ∀ ψ ∈ X, Continuous ψ)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (c : ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | ∃ ψ ∈ X, φ = rightConv F ψ f - c • ψ}
  zero_mem' := ⟨0, X.zero_mem, by
    rw [smul_zero, sub_zero]
    exact (rightConv_zero_left F f).symm⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨ψ₁, h₁, rfl⟩ := ha
    obtain ⟨ψ₂, h₂, rfl⟩ := hb
    refine ⟨ψ₁ + ψ₂, X.add_mem h₁ h₂, ?_⟩
    rw [rightConv_add_left F (hX ψ₁ h₁) (hX ψ₂ h₂) hf hfc, smul_add]
    exact sub_add_sub_comm _ _ _ _
  smul_mem' := by
    intro a b hb
    obtain ⟨ψ, h, rfl⟩ := hb
    refine ⟨a • ψ, X.smul_mem a h, ?_⟩
    have hs : rightConv F (a • ψ) f = a • rightConv F ψ f := convOp_smul F f a ψ
    rw [hs, smul_sub, smul_comm c a ψ]

private theorem mem_shiftRange_iff {X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    {hX : ∀ ψ ∈ X, Continuous ψ} {f : AdelicGL2 (𝓞 F) F → ℂ} {hf : Continuous f}
    {hfc : HasCompactSupport f} {c : ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ} :
    φ ∈ shiftRange F X hX hf hfc c ↔ ∃ ψ ∈ X, φ = rightConv F ψ f - c • ψ :=
  Iff.rfl

private theorem mem_inf_inf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q r : Submodule R M} {x : M} : x ∈ p ⊓ q ⊓ r ↔ (x ∈ p ∧ x ∈ q) ∧ x ∈ r :=
  Iff.rfl

private theorem shiftRange_rightTranslate_mem {tys : ArchTypeFamily F}
    {U : Subgroup (AdelicGL2 (𝓞 F) F)} {X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hX : ∀ ψ ∈ X, Continuous ψ) {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f)
    (hfcs : HasCompactSupport f) (hf : IsLevelSphericalOfType F tys U f)
    (hXk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ ψ ∈ X, rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ X)
    (c : ℂ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    ∀ φ ∈ shiftRange F X hX hfc hfcs c,
      rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ shiftRange F X hX hfc hfcs c := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  refine ⟨rightTranslate F (rowIsometryInclAt₀ F w k) ψ, hXk w k ψ hψ, ?_⟩
  rw [rightTranslate_sub_smul, rightTranslate_rightConv_of_isLevelSphericalOfType F tys U f hf w k ψ]

private theorem shiftRange_rightConv_mem {X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hX : ∀ ψ ∈ X, Continuous ψ) {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f)
    (hfcs : HasCompactSupport f) (c : ℂ) {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : Continuous h)
    (hhc : HasCompactSupport h)
    (hcomm : ∀ ψ ∈ X, rightConv F (rightConv F ψ f) h = rightConv F (rightConv F ψ h) f)
    (hXh : ∀ ψ ∈ X, rightConv F ψ h ∈ X) (hXf : ∀ ψ ∈ X, rightConv F ψ f ∈ X) :
    ∀ φ ∈ shiftRange F X hX hfc hfcs c, rightConv F φ h ∈ shiftRange F X hX hfc hfcs c := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  refine ⟨rightConv F ψ h, hXh ψ hψ, ?_⟩
  rw [rightConv_sub_smul_left F (hX _ (hXf ψ hψ)) (hX ψ hψ) hh hhc c, hcomm ψ hψ]

private theorem shiftRange_sum_mem {X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hX : ∀ ψ ∈ X, Continuous ψ) {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f)
    (hfcs : HasCompactSupport f) (c : ℂ) {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (hcs : ∀ ψ ∈ X,
      (fun x => ∑ i, rightConv F ψ f (x * reps i)) = rightConv F (fun x => ∑ i, ψ (x * reps i)) f)
    (hXs : ∀ ψ ∈ X, (fun x => ∑ i, ψ (x * reps i)) ∈ X) :
    ∀ φ ∈ shiftRange F X hX hfc hfcs c,
      (fun x => ∑ i, φ (x * reps i)) ∈ shiftRange F X hX hfc hfcs c := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  refine ⟨fun x => ∑ i, ψ (x * reps i), hXs ψ hψ, ?_⟩
  rw [← hcs ψ hψ]
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem eq_zero_of_forall_real_exists {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f) (hfcs : HasCompactSupport f)
    (hflat : flat F σ f = f) {X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hcm : ∀ φ ∈ X, φ ∈ contMemberSubmodule F Φ₀ ξ) (hXf : ∀ ψ ∈ X, rightConv F ψ f ∈ X)
    (hall : ∀ c : ℝ, ∀ φ ∈ X, ∃ ψ ∈ X, φ = rightConv F ψ f - (c : ℂ) • ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ X) : φ = 0 := by
  obtain ⟨T, T', hT, hT', hadj⟩ := exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs
  rw [hflat] at hT'
  have hsym : ∀ x ∈ Submodule.map (toCarrier F hΦ₀ σ ξ) (X.comap (memberSubmodule F Φ₀ ξ).subtype),
      ∀ y ∈ Submodule.map (toCarrier F hΦ₀ σ ξ) (X.comap (memberSubmodule F Φ₀ ξ).subtype),
      ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro x _ y hy
    obtain ⟨⟨b, hb⟩, hbX, rfl⟩ := Submodule.mem_map.mp hy
    have hbX' : b ∈ X := Submodule.mem_comap.mp hbX
    have hbm : rightConv F b f ∈ memberSubmodule F Φ₀ ξ := (hcm _ (hXf b hbX')).1
    have eb : T (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩) = toCarrier F hΦ₀ σ ξ ⟨rightConv F b f, hbm⟩ :=
      hT.comm b (hcm b hbX')
    have eb' : T' (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩) = toCarrier F hΦ₀ σ ξ ⟨rightConv F b f, hbm⟩ :=
      hT'.comm b (hcm b hbX')
    rw [← ContinuousLinearMap.adjoint_inner_right T, hadj, eb', eb]
  have v0 : toCarrier F hΦ₀ σ ξ ⟨φ, (hcm φ hφ).1⟩ = 0 := by
    refine ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq T _ hsym _ fun c => ?_
    obtain ⟨ψ, hψX, heq⟩ := hall c φ hφ
    have hψm : ψ ∈ memberSubmodule F Φ₀ ξ := (hcm ψ hψX).1
    have hψfm : rightConv F ψ f ∈ memberSubmodule F Φ₀ ξ := (hcm _ (hXf ψ hψX)).1
    refine ⟨toCarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩,
      Submodule.mem_map.mpr ⟨⟨ψ, hψm⟩, Submodule.mem_comap.mpr hψX, rfl⟩, ?_⟩
    have e1 : T (toCarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩) = toCarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψfm⟩ :=
      hT.comm ψ (hcm ψ hψX)
    rw [e1, ← map_smul (toCarrier F hΦ₀ σ ξ), ← map_sub (toCarrier F hΦ₀ σ ξ)]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul]
    exact heq.symm
  exact eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ φ (hcm φ hφ) v0

private theorem exists_real_of_cuspKFiniteSubmodule_le (D : Set (AdelicGL2 (𝓞 F) F))
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (fdPins F D) ξ V)
    (hmem : cuspKFiniteSubmodule F (fdPins F D) ξ ≤ cuspMemberSubmodule F Φ₀ ξ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hfT : IsFactorizableTestFn F f)
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F)
      ((fdPins F D).U N) f)
    (hflat : flat F σ f = f) :
    ∃ lam : ℝ, ∀ φ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
        archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F),
      rightConv F φ f = (lam : ℂ) • φ := by
  obtain ⟨hfc, hfcs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hfT
  have hUfin : (fdPins F D).U N ≤ finiteAdelicGL2Subgroup F := inf_le_right
  obtain ⟨hbf, hfl⟩ := isArchBiFinite_and_forall_mul_left F hUfin hf

  have hcm : ∀ φ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F),
      φ ∈ contMemberSubmodule F Φ₀ ξ := fun φ hφ =>
    ⟨(hmem (hV.1.le (mem_inf_inf.mp hφ).1.1)).1.1.1, (hmem (hV.1.le (mem_inf_inf.mp hφ).1.1)).2⟩
  have hXc : ∀ φ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F), Continuous φ :=
    fun φ hφ => (hcm φ hφ).2

  have hXf : ∀ ψ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F),
      rightConv F ψ f ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
        archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) := by
    intro ψ hψ
    obtain ⟨⟨hψV, -⟩, -⟩ := mem_inf_inf.mp hψ
    refine mem_inf_inf.mpr ⟨⟨hV.1.rightConv_mem f _ hfT hbf ψ hψV,
      (levelInvariant_iff F).mpr fun x u hu => rightConv_apply_mul_of_forall_mul_left F ψ hfl x hu⟩,
      rightConv_mem_archCutSubmodule_of_isArchBiFinite F _ ψ (hXc ψ hψ) f hfT hbf⟩

  have hXk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ ψ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
        archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F),
      rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
        archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) := by
    intro w k ψ hψ
    obtain ⟨⟨hψV, hψL⟩, hψC⟩ := mem_inf_inf.mp hψ
    exact mem_inf_inf.mpr ⟨⟨hV.1.rightTranslate_arch_mem w k ψ hψV,
      rightTranslate_mem_levelInvariantSubmodule F hUfin hψL w k⟩,
      rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule F _ hψC w k⟩

  have hdich : ∀ c : ℂ,
      V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
          archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) ⊓
          shiftRange F _ hXc hfc hfcs c = ⊥ ∨
        V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
          archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) ≤
          shiftRange F _ hXc hfc hfcs c := by
    intro c
    refine inf_eq_bot_or_le_of_isCuspConstituent F D ξ N hN _ V hV (shiftRange F _ hXc hfc hfcs c)
      (fun w k => shiftRange_rightTranslate_mem F hXc hfc hfcs hf hXk c w k) ?_ ?_
    · intro g hg n reps hreps hcov hinj φ hφ
      have hrf : ∀ i, reps i ∈ finiteAdelicGL2Subgroup F := fun i => by
        obtain ⟨u, hu, u', hu', hi⟩ := hreps i
        rw [hi]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hUfin hu) hg) (hUfin hu')
      refine shiftRange_sum_mem F hXc hfc hfcs c reps (fun ψ hψ => ?_) (fun ψ hψ => ?_) φ
        (Submodule.mem_inf.mp hφ).1
      · exact cosetSum_rightConv_of_isLevelSphericalOfType F D N hN _ f hf g hg n reps hreps hcov hinj ψ
          (hXc ψ hψ) (mem_inf_inf.mp hψ).1.2
      · obtain ⟨⟨hψV, hψL⟩, hψC⟩ := mem_inf_inf.mp hψ
        have hsum : (fun x => ∑ i, ψ (x * reps i)) = ∑ i, rightTranslate F (reps i) ψ := by
          funext x
          rw [Finset.sum_apply]
          rfl
        refine mem_inf_inf.mpr ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hsum]
          exact Submodule.sum_mem _ fun i _ => hV.1.rightTranslate_fin_mem _ (hrf i) ψ hψV
        · exact (levelInvariant_iff F).mpr fun x u hu =>
            sum_apply_mul_mul_eq hreps hcov hinj ((levelInvariant_iff F).mp hψL) x hu
        · rw [hsum]
          exact Submodule.sum_mem _ fun i _ => comp_mul_mem_archCutSubmodule_of_mem F hψC (hrf i)
    · intro h hh hht hhU φ hφ
      obtain ⟨hhc, hhcs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F h hh
      refine shiftRange_rightConv_mem F hXc hfc hfcs c hhc hhcs (fun ψ hψ => ?_) (fun ψ hψ => ?_) hXf φ hφ
      · exact rightConv_rightConv_comm_of_isLevelSphericalOfType F D N hN τ hirr f hf h hh hht hhU ψ
          (hXc ψ hψ)
      · obtain ⟨⟨hψV, -⟩, -⟩ := mem_inf_inf.mp hψ
        exact mem_inf_inf.mpr ⟨⟨hV.1.rightConv_mem h _ hh hht ψ hψV,
          (levelInvariant_iff F).mpr fun x u hu =>
            rightConv_apply_mul_of_forall_mul_left F ψ (fun y u hu => (hhU y u hu).1) x hu⟩,
          rightConv_mem_archCutSubmodule_of_isArchBiFinite F _ ψ (hXc ψ hψ) h hh hht⟩

  by_cases hA : ∃ c : ℝ,
      V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
          archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) ⊓
        shiftRange F _ hXc hfc hfcs (c : ℂ) = ⊥
  · obtain ⟨c, hc⟩ := hA
    refine ⟨c, fun φ hφ => ?_⟩
    have h0 : rightConv F φ f - (c : ℂ) • φ ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :=
      hc.le (Submodule.mem_inf.mpr
        ⟨Submodule.sub_mem _ (hXf φ hφ) (Submodule.smul_mem _ _ hφ), (mem_shiftRange_iff F).mpr ⟨φ, hφ, rfl⟩⟩)
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp h0)
  · have hall : ∀ c : ℝ, ∀ φ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
        archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F),
        ∃ ψ ∈ V ⊓ levelInvariantSubmodule F (fdPins F D) N ⊓
          archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F),
          φ = rightConv F ψ f - (c : ℂ) • ψ := fun c φ hφ =>
      (mem_shiftRange_iff F).mp (((hdich c).resolve_left fun h => hA ⟨c, h⟩) hφ)
    refine ⟨0, fun φ hφ => ?_⟩
    rw [eq_zero_of_forall_real_exists F hΦ₀ σ ξ hσ hfc hfcs hflat hcm hXf hall hφ,
      Complex.ofReal_zero, zero_smul]
    exact rightConv_zero_left F f

end SphericalCutScalar

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hfT : IsFactorizableTestFn F f)
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
        ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (hflat : flat F σ f = f) :
    ∃ lam : ℝ,
      ∀ φ ∈
        V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F),
        rightConv F φ f = (lam : ℂ) • φ := by
  obtain ⟨α, β, Φ₀, hΦ₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain F
  exact SphericalCutScalar.exists_real_of_cuspKFiniteSubmodule_le F _ hΦ₀ ξ σ hσ N hN τ hirr V hV
    (AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd
      hcov ξ hΦ₀)
    f hfT hf hflat

end

#print axioms solution

end S_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType (solution)
