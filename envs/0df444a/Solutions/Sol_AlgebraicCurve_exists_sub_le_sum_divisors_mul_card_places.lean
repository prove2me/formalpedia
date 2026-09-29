-- Prove2me | solution 1 for AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e1539c5b-a789-5d4d-9438-87c3a27727c0

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_AlgebraicCurve_natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
import Theorems.Thm_AlgebraicCurve_finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
import Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct IntermediateField Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.restrictAlong Place Place.ext Divisor SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.ofAlgAut_smul SemilinearAut.smul_toValuationSubring IsFrobeniusEndo IsCurveOver genusFF LSpace mem_lSpace_iff_ord ConstantsAreBase Place.congrEquiv finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard RationalFunctionField.finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow IsCurveOver.exists_separating_transcendental isCurveOver_of_isAlgClosed_of_transcendental"
p2m_open "AlgebraicCurve~genus"

namespace BombieriLower

universe u v

section Generic

theorem injective_of_isField {R S : Type*} [CommRing R] [Semiring S] [Nontrivial S]
    (hR : IsField R) (f : R →+* S) : Function.Injective f := by
  letI := hR.toField
  exact f.injective

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

theorem mem_restrictAlong_iff (φ : M →ₐ[K] M) (hφ : φ.toRingHom.IsIntegral) (W : Place K M)
    (y : M) : y ∈ (W.restrictAlong φ hφ).toValuationSubring ↔ φ y ∈ W.toValuationSubring :=
  Iff.rfl

theorem mem_iterate_restrictAlong_iff (φ : M →ₐ[K] M) (hφ : φ.toRingHom.IsIntegral) (r : ℕ)
    (W : Place K M) (y : M) :
    y ∈ ((Place.restrictAlong φ hφ)^[r] W).toValuationSubring ↔
      (φ ^ r) y ∈ W.toValuationSubring := by
  induction r generalizing y with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', mem_restrictAlong_iff, ih, pow_succ, AlgHom.mul_apply]

theorem iterate_restrictAlong_eq (φ : M →ₐ[K] M) (hφ : φ.toRingHom.IsIntegral) (r : ℕ)
    (hφr : (φ ^ r).toRingHom.IsIntegral) :
    (Place.restrictAlong φ hφ)^[r] = Place.restrictAlong (φ ^ r) hφr := by
  funext W
  apply Place.ext
  ext y
  rw [mem_iterate_restrictAlong_iff]
  rfl

theorem algEquiv_isIntegral (τ : M ≃ₐ[K] M) : (τ : M →ₐ[K] M).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ τ.surjective

theorem comp_algEquiv_isIntegral (ψ : M →ₐ[K] M) (hψ : ψ.toRingHom.IsIntegral)
    (τ : M ≃ₐ[K] M) : (ψ.comp (τ : M →ₐ[K] M)).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans _ _ (algEquiv_isIntegral τ) hψ

theorem fixedPoints_restrictAlong_comp_algEquiv (ψ : M →ₐ[K] M) (hψ : ψ.toRingHom.IsIntegral)
    (τ : M ≃ₐ[K] M) (h : (ψ.comp (τ : M →ₐ[K] M)).toRingHom.IsIntegral) :
    Function.fixedPoints (Place.restrictAlong (ψ.comp (τ : M →ₐ[K] M)) h) =
      {W : Place K M | W.restrictAlong ψ hψ = SemilinearAut.ofAlgAut τ • W} := by
  ext W
  rw [Function.mem_fixedPoints_iff, Set.mem_setOf_eq]
  have key : W.restrictAlong (ψ.comp (τ : M →ₐ[K] M)) h =
      (SemilinearAut.ofAlgAut τ)⁻¹ • W.restrictAlong ψ hψ := by
    apply Place.ext
    ext y
    rw [SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, SemilinearAut.ofAlgAut_smul]
    exact Iff.rfl
  rw [key, inv_smul_eq_iff]

theorem IsFrobeniusEndo.comp_algEquiv {Q : ℕ} {ψ : M →ₐ[K] M} (h : IsFrobeniusEndo Q ψ)
    (τ : M ≃ₐ[K] M) : IsFrobeniusEndo Q (ψ.comp (τ : M →ₐ[K] M)) where
  pow_mem_range y := by
    obtain ⟨z, hz⟩ := h.pow_mem_range y
    exact ⟨τ.symm z, by simpa using hz⟩
  mem_range_pow y := by
    obtain ⟨z, hz⟩ := h.mem_range_pow (τ y)
    exact ⟨z, by simpa using hz⟩

theorem natCard_fixedPoints_congr {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (φA : A →ₐ[K] A) (hA : φA.toRingHom.IsIntegral)
    (φB : B →ₐ[K] B) (hB : φB.toRingHom.IsIntegral) (hcomm : ∀ a, e (φA a) = φB (e a)) :
    ((Function.fixedPoints (Place.restrictAlong φA hA)).Finite ↔
        (Function.fixedPoints (Place.restrictAlong φB hB)).Finite) ∧
      Nat.card (Function.fixedPoints (Place.restrictAlong φA hA)) =
        Nat.card (Function.fixedPoints (Place.restrictAlong φB hB)) := by
  have he : ∀ a : K, e.toRingEquiv (algebraMap K A a) = algebraMap K B a := fun a => e.commutes a
  let c : Place K A ≃ Place K B := Place.congrEquiv e.toRingEquiv he
  have hequiv : ∀ v : Place K A,
      c (Place.restrictAlong φA hA v) = Place.restrictAlong φB hB (c v) := by
    intro v
    apply Place.ext
    ext b
    change φA (e.symm b) ∈ v.toValuationSubring ↔ e.symm (φB b) ∈ v.toValuationSubring
    have : e.symm (φB b) = φA (e.symm b) := by
      apply e.injective
      rw [hcomm, e.apply_symm_apply, e.apply_symm_apply]
    rw [this]
  have hbij : Set.BijOn c (Function.fixedPoints (Place.restrictAlong φA hA))
      (Function.fixedPoints (Place.restrictAlong φB hB)) := by
    refine Equiv.bijOn c fun v => ?_
    change Place.restrictAlong φB hB (c v) = c v ↔ Place.restrictAlong φA hA v = v
    rw [← hequiv]
    exact c.injective.eq_iff
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · exact (hbij.image_eq ▸ h.image c)
  · rw [← hbij.image_eq] at h
    exact Set.Finite.of_finite_image h c.injective.injOn
  · exact Nat.card_congr (hbij.equiv c)

theorem exists_finset_adjoin_eq_top (y : M) [Module.Finite K⟮y⟯ M] :
    ∃ s : Finset M, IntermediateField.adjoin K (s : Set M) = ⊤ := by
  classical
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := K⟮y⟯) (M := M)
  refine ⟨insert y (Finset.univ.image b), ?_⟩
  rw [eq_top_iff]
  rintro m -
  have hm : m ∈ Submodule.span K⟮y⟯ (Set.range b) := by rw [hb]; exact Submodule.mem_top
  have hsub : K⟮y⟯ ≤ IntermediateField.adjoin K ((insert y (Finset.univ.image b) : Finset M) : Set M) := by
    apply IntermediateField.adjoin.mono
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    simp
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    apply IntermediateField.subset_adjoin
    simp
  | zero => exact zero_mem _
  | add z w _ _ hz hw => exact add_mem hz hw
  | smul a z _ hz =>
    change (a : M) * z ∈ _
    exact mul_mem (hsub a.2) hz

theorem lower_of_identity_of_upper {ι : Type*} [Fintype ι] (N : ι → ℕ) (A B : ℝ)
    (hsum : (Fintype.card ι : ℝ) * A = ∑ τ, (N τ : ℝ)) (hub : ∀ τ, (N τ : ℝ) ≤ A + B)
    (τ₀ : ι) : A - (Fintype.card ι - 1 : ℝ) * B ≤ N τ₀ := by
  classical
  have hsplit : ∑ τ, (N τ : ℝ) = N τ₀ + ∑ τ ∈ Finset.univ.erase τ₀, (N τ : ℝ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ₀)]
  have hrest : ∑ τ ∈ Finset.univ.erase τ₀, (N τ : ℝ) ≤ (Fintype.card ι - 1 : ℝ) * (A + B) := by
    calc ∑ τ ∈ Finset.univ.erase τ₀, (N τ : ℝ) ≤ ∑ _τ ∈ Finset.univ.erase τ₀, (A + B) :=
          Finset.sum_le_sum fun τ _ => hub τ
      _ = (Fintype.card ι - 1 : ℝ) * (A + B) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ τ₀),
            Finset.card_univ, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨τ₀⟩), Nat.cast_one]
  nlinarith [hsplit, hrest, hsum]

theorem le_of_mul_eq_sum_of_forall_le {ι : Type*} [Fintype ι] [Nonempty ι] (N : ι → ℕ)
    (S : ℕ) (L : ℝ) (hsum : Fintype.card ι * S = ∑ h, N h) (hlb : ∀ h, L ≤ N h) :
    L ≤ S := by
  have hpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hcast : (Fintype.card ι : ℝ) * S = ∑ h, (N h : ℝ) := by exact_mod_cast hsum
  have : (Fintype.card ι : ℝ) * L ≤ ∑ h, (N h : ℝ) := by
    calc (Fintype.card ι : ℝ) * L = ∑ _h : ι, L := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
      _ ≤ ∑ h, (N h : ℝ) := Finset.sum_le_sum fun h _ => hlb h
  rw [← hcast] at this
  exact le_of_mul_le_mul_left this hpos

theorem sub_le_of_identities {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (N : ι → ℕ) (e : κ → ι) (S : ℕ) (A B : ℝ)
    (hbig : (Fintype.card ι : ℝ) * A = ∑ τ, (N τ : ℝ)) (hub : ∀ τ, (N τ : ℝ) ≤ A + B)
    (hsmall : Fintype.card κ * S = ∑ h, N (e h)) :
    A - (Fintype.card ι - 1 : ℝ) * B ≤ S :=
  le_of_mul_eq_sum_of_forall_le (fun h => N (e h)) S _ hsmall
    fun h => lower_of_identity_of_upper N A B hbig hub (e h)

theorem exists_sq_lt_pow (q g : ℕ) (hq : 2 ≤ q) : ∃ s : ℕ, 0 < s ∧ (g + 1) ^ 2 < q ^ s :=
  ⟨(g + 1) ^ 2, by positivity,
    lt_of_lt_of_le ((g + 1) ^ 2).lt_two_pow_self (Nat.pow_le_pow_left hq _)⟩

end Generic

section Construction

variable (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]

abbrev Ω : Type v := AlgebraicClosure F

abbrev Kc : Type u := AlgebraicClosure k

def ιK : Kc k →ₐ[k] Ω F := IsAlgClosed.lift

scoped instance algKΩ : Algebra (Kc k) (Ω F) := (ιK k F).toRingHom.toAlgebra

scoped instance : IsScalarTower k (Kc k) (Ω F) :=
  IsScalarTower.of_algebraMap_eq fun c => ((ιK k F).commutes c).symm

theorem algebraMap_K_eq (c : Kc k) : algebraMap (Kc k) (Ω F) c = ιK k F c := rfl

def θ₀ : F ⊗[k] Kc k →ₐ[k] Ω F :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k F (Ω F)) (ιK k F) fun _ _ => Commute.all _ _

theorem θ₀_tmul (f : F) (c : Kc k) :
    θ₀ k F (f ⊗ₜ c) = algebraMap F (Ω F) f * algebraMap (Kc k) (Ω F) c := by
  rw [θ₀, Algebra.TensorProduct.lift_tmul]
  rfl

abbrev AF : IntermediateField k (Ω F) := (IsScalarTower.toAlgHom k F (Ω F)).fieldRange

theorem isIntegral_θ₀ (t : F ⊗[k] Kc k) : IsIntegral (AF k F) (θ₀ k F t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact isIntegral_zero
  | tmul f c =>
    rw [θ₀_tmul]
    refine IsIntegral.mul ?_ ?_
    · have : algebraMap F (Ω F) f = algebraMap (AF k F) (Ω F) ⟨algebraMap F (Ω F) f, f, rfl⟩ := rfl
      rw [this]
      exact isIntegral_algebraMap
    · have hc : IsIntegral k c := Algebra.IsIntegral.isIntegral c
      have hc' : IsIntegral k (algebraMap (Kc k) (Ω F) c) := hc.map (ιK k F)
      exact hc'.tower_top
  | add a b ha hb => rw [map_add]; exact ha.add hb

def FI : IntermediateField (Kc k) (Ω F) where
  carrier := Set.range (θ₀ k F)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul (θ₀ k F) _ _⟩
  one_mem' := ⟨1, map_one (θ₀ k F)⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add (θ₀ k F) _ _⟩
  zero_mem' := ⟨0, map_zero (θ₀ k F)⟩
  algebraMap_mem' c := ⟨1 ⊗ₜ c, by rw [θ₀_tmul, map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩

    let R : Subalgebra (AF k F) (Ω F) :=
      { carrier := Set.range (θ₀ k F)
        mul_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a * b, map_mul (θ₀ k F) _ _⟩
        one_mem' := ⟨1, map_one (θ₀ k F)⟩
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, map_add (θ₀ k F) _ _⟩
        zero_mem' := ⟨0, map_zero (θ₀ k F)⟩
        algebraMap_mem' := by
          rintro ⟨_, f, rfl⟩
          exact ⟨f ⊗ₜ 1, by rw [θ₀_tmul, map_one, mul_one]; rfl⟩ }
    have hle : Algebra.adjoin (AF k F) {θ₀ k F t} ≤ R := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨t, rfl⟩
    exact hle ((isIntegral_θ₀ k F t).inv_mem_adjoin)

theorem mem_FI {z : Ω F} : z ∈ FI k F ↔ ∃ t, θ₀ k F t = z := Iff.rfl

theorem algebraMap_mem_FI (f : F) : algebraMap F (Ω F) f ∈ FI k F :=
  ⟨f ⊗ₜ 1, by rw [θ₀_tmul]; simp⟩

theorem algebraMap_K_mem_FI (c : Kc k) : algebraMap (Kc k) (Ω F) c ∈ FI k F :=
  (FI k F).algebraMap_mem c

def Fb : Type v := ↥(FI k F)

scoped instance : Field (Fb k F) := inferInstanceAs (Field ↥(FI k F))
scoped instance : Algebra (Kc k) (Fb k F) := inferInstanceAs (Algebra (Kc k) ↥(FI k F))
scoped instance : Algebra (Fb k F) (Ω F) := inferInstanceAs (Algebra ↥(FI k F) (Ω F))
scoped instance : IsScalarTower (Kc k) (Fb k F) (Ω F) :=
  inferInstanceAs (IsScalarTower (Kc k) ↥(FI k F) (Ω F))

variable {k F} in

def mkFb (t : F ⊗[k] Kc k) : Fb k F := ⟨θ₀ k F t, t, rfl⟩

theorem mkFb_coe (t : F ⊗[k] Kc k) : (mkFb t : Fb k F).1 = θ₀ k F t := rfl

theorem mkFb_surjective : Function.Surjective (mkFb (k := k) (F := F)) := by
  rintro ⟨_, t, rfl⟩
  exact ⟨t, rfl⟩

theorem mkFb_add (s t : F ⊗[k] Kc k) : (mkFb (s + t) : Fb k F) = mkFb s + mkFb t :=
  Subtype.ext (map_add _ _ _)

theorem mkFb_mul (s t : F ⊗[k] Kc k) : (mkFb (s * t) : Fb k F) = mkFb s * mkFb t :=
  Subtype.ext (map_mul _ _ _)

theorem mkFb_zero : (mkFb 0 : Fb k F) = 0 := Subtype.ext (map_zero _)

theorem mkFb_one : (mkFb 1 : Fb k F) = 1 := Subtype.ext (map_one _)

scoped instance algebraFFb : Algebra F (Fb k F) :=
  ((algebraMap F (Ω F)).codRestrict (FI k F) fun f => algebraMap_mem_FI k F f).toAlgebra

theorem algebraMap_Fb_coe (f : F) :
    (algebraMap F (Fb k F) f).1 = algebraMap F (Ω F) f := rfl

theorem algebraMap_Fb_eq_mkFb (f : F) : algebraMap F (Fb k F) f = mkFb (f ⊗ₜ 1) :=
  Subtype.ext (by rw [algebraMap_Fb_coe, mkFb_coe, θ₀_tmul, map_one, mul_one])

theorem algebraMap_KFb_coe (c : Kc k) :
    (algebraMap (Kc k) (Fb k F) c).1 = algebraMap (Kc k) (Ω F) c := rfl

theorem mkFb_tmul (f : F) (c : Kc k) :
    (mkFb (f ⊗ₜ c) : Fb k F) = algebraMap F (Fb k F) f * algebraMap (Kc k) (Fb k F) c :=
  Subtype.ext (θ₀_tmul k F f c)

theorem algebraMap_Fb_Ω (y : Fb k F) : algebraMap (Fb k F) (Ω F) y = y.1 := rfl

theorem coe_add_Fb (a b : Fb k F) : (a + b).1 = a.1 + b.1 := rfl
theorem coe_mul_Fb (a b : Fb k F) : (a * b).1 = a.1 * b.1 := rfl

scoped instance : IsScalarTower F (Fb k F) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (x : F)

abbrev xΩ : Ω F := algebraMap F (Ω F) x

abbrev LI : IntermediateField (Kc k) (Ω F) := (Kc k)⟮xΩ F x⟯

def Lb : Type v := ↥(LI k F x)

scoped instance : Field (Lb k F x) := inferInstanceAs (Field ↥(LI k F x))
scoped instance : Algebra (Kc k) (Lb k F x) := inferInstanceAs (Algebra (Kc k) ↥(LI k F x))
scoped instance : Algebra (Lb k F x) (Ω F) := inferInstanceAs (Algebra ↥(LI k F x) (Ω F))
scoped instance : IsScalarTower (Kc k) (Lb k F x) (Ω F) :=
  inferInstanceAs (IsScalarTower (Kc k) ↥(LI k F x) (Ω F))

theorem algebraMap_Lb_Ω (y : Lb k F x) : algebraMap (Lb k F x) (Ω F) y = y.1 := rfl

theorem LI_le_FI : LI k F x ≤ FI k F := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact algebraMap_mem_FI k F x

scoped instance algLF : Algebra (Lb k F x) (Fb k F) :=
  (IntermediateField.inclusion (LI_le_FI k F x) : ↥(LI k F x) →ₐ[Kc k] ↥(FI k F)).toAlgebra

theorem algebraMap_LF (y : Lb k F x) : (algebraMap (Lb k F x) (Fb k F) y).1 = y.1 := rfl

scoped instance : IsScalarTower (Kc k) (Lb k F x) (Fb k F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (Lb k F x) (Fb k F) (Ω F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def EIL : IntermediateField (Lb k F x) (Ω F) :=
  IntermediateField.normalClosure (Lb k F x) (Fb k F) (Ω F)

def EI : IntermediateField (Kc k) (Ω F) := (EIL k F x).restrictScalars (Kc k)

def Eb : Type v := ↥(EI k F x)

scoped instance : Field (Eb k F x) := inferInstanceAs (Field ↥(EI k F x))
scoped instance : Algebra (Kc k) (Eb k F x) := inferInstanceAs (Algebra (Kc k) ↥(EI k F x))
scoped instance : Algebra (Eb k F x) (Ω F) := inferInstanceAs (Algebra ↥(EI k F x) (Ω F))
scoped instance : IsScalarTower (Kc k) (Eb k F x) (Ω F) :=
  inferInstanceAs (IsScalarTower (Kc k) ↥(EI k F x) (Ω F))

theorem algebraMap_Eb_Ω (y : Eb k F x) : algebraMap (Eb k F x) (Ω F) y = y.1 := rfl

theorem mem_EI {z : Ω F} : z ∈ EI k F x ↔ z ∈ EIL k F x := IntermediateField.mem_restrictScalars _

theorem LI_le_EI : LI k F x ≤ EI k F x := fun z hz =>
  (mem_EI k F x).mpr ((EIL k F x).algebraMap_mem ⟨z, hz⟩)

theorem FI_le_EI : FI k F ≤ EI k F x := fun z hz =>
  (mem_EI k F x).mpr
    (AlgHom.fieldRange_le_normalClosure (IsScalarTower.toAlgHom (Lb k F x) (Fb k F) (Ω F))
      ⟨⟨z, hz⟩, rfl⟩)

scoped instance algLE : Algebra (Lb k F x) (Eb k F x) :=
  (IntermediateField.inclusion (LI_le_EI k F x) : ↥(LI k F x) →ₐ[Kc k] ↥(EI k F x)).toAlgebra
scoped instance algFE : Algebra (Fb k F) (Eb k F x) :=
  (IntermediateField.inclusion (FI_le_EI k F x) : ↥(FI k F) →ₐ[Kc k] ↥(EI k F x)).toAlgebra

theorem algebraMap_LE (y : Lb k F x) : (algebraMap (Lb k F x) (Eb k F x) y).1 = y.1 := rfl
theorem algebraMap_FE (y : Fb k F) : (algebraMap (Fb k F) (Eb k F x) y).1 = y.1 := rfl

scoped instance : IsScalarTower (Kc k) (Lb k F x) (Eb k F x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
scoped instance : IsScalarTower (Kc k) (Fb k F) (Eb k F x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
scoped instance : IsScalarTower (Lb k F x) (Fb k F) (Eb k F x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
scoped instance : IsScalarTower (Lb k F x) (Eb k F x) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
scoped instance : IsScalarTower (Fb k F) (Eb k F x) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

def ebEquiv : ↥(EIL k F x) ≃ₐ[Lb k F x] Eb k F x where
  toFun z := ⟨z.1, z.2⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

abbrev kx : IntermediateField k F := k⟮x⟯

theorem algebraMap_kx_mem_LI (a : kx k F x) : algebraMap (kx k F x) (Ω F) a ∈ LI k F x := by
  have hmap : (kx k F x).map (IsScalarTower.toAlgHom k F (Ω F)) ≤ (LI k F x).restrictScalars k := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact IntermediateField.mem_adjoin_simple_self (Kc k) (xΩ F x)
  have : algebraMap (kx k F x) (Ω F) a = IsScalarTower.toAlgHom k F (Ω F) (a : F) := rfl
  rw [this]
  exact hmap ⟨a, a.2, rfl⟩

scoped instance algkxL : Algebra (kx k F x) (Lb k F x) :=
  ((algebraMap (kx k F x) (Ω F)).codRestrict (LI k F x) (algebraMap_kx_mem_LI k F x)).toAlgebra

scoped instance : IsScalarTower (kx k F x) (Lb k F x) (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (kx k F x) F (Ω F) := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem exists_span_FI [FiniteDimensional (kx k F x) F] :
    ∃ (n : ℕ) (b : Fin n → Ω F), (FI k F : Set (Ω F)) ⊆ Submodule.span (Lb k F x) (Set.range b) := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := kx k F x) (M := F)
  refine ⟨n, fun i => algebraMap F (Ω F) (b i), ?_⟩
  have hF : ∀ f : F, algebraMap F (Ω F) f ∈ Submodule.span (Lb k F x)
      (Set.range fun i => algebraMap F (Ω F) (b i)) := by
    intro f
    have hf : f ∈ Submodule.span (kx k F x) (Set.range b) := by rw [hb]; exact Submodule.mem_top
    have h1 : algebraMap F (Ω F) f ∈ (Submodule.span (kx k F x) (Set.range b)).map
        (IsScalarTower.toAlgHom (kx k F x) F (Ω F)).toLinearMap := ⟨f, hf, rfl⟩
    rw [Submodule.map_span] at h1
    have h2 : (IsScalarTower.toAlgHom (kx k F x) F (Ω F)).toLinearMap '' Set.range b =
        Set.range fun i => algebraMap F (Ω F) (b i) := by
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨b i, ⟨i, rfl⟩, rfl⟩
    rw [h2] at h1
    exact Submodule.span_le_restrictScalars (kx k F x) (Lb k F x) _ h1
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul f c =>
    rw [θ₀_tmul, mul_comm]
    have : algebraMap (Kc k) (Ω F) c * algebraMap F (Ω F) f =
        (⟨algebraMap (Kc k) (Ω F) c, (LI k F x).algebraMap_mem c⟩ : Lb k F x) •
          algebraMap F (Ω F) f := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (hF f)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

scoped instance finite_LF [FiniteDimensional (kx k F x) F] : Module.Finite (Lb k F x) (Fb k F) := by
  obtain ⟨n, b, hb⟩ := exists_span_FI k F x
  let N := Submodule.span (Lb k F x) (Set.range b)
  haveI : Module.Finite (Lb k F x) N := Module.Finite.span_of_finite _ (Set.finite_range b)
  let f : Fb k F →ₗ[Lb k F x] N :=
    LinearMap.codRestrict N (IsScalarTower.toAlgHom (Lb k F x) (Fb k F) (Ω F)).toLinearMap
      fun y => hb y.2
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg Subtype.val h :)

theorem FI_le_separableClosure [Algebra.IsSeparable (kx k F x) F] :
    (FI k F : Set (Ω F)) ⊆ separableClosure (Lb k F x) (Ω F) := by
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul f c =>
    rw [θ₀_tmul]
    refine mul_mem ?_ ?_
    · rw [mem_separableClosure_iff]
      have h1 : IsSeparable (kx k F x) (algebraMap F (Ω F) f) :=
        IsSeparable.map (IsScalarTower.toAlgHom (kx k F x) F (Ω F)) (RingHom.injective _)
          (Algebra.IsSeparable.isSeparable _ f)
      exact IsSeparable.tower_top (Lb k F x) h1
    · rw [mem_separableClosure_iff]
      exact isSeparable_algebraMap (⟨algebraMap (Kc k) (Ω F) c, (LI k F x).algebraMap_mem c⟩ : Lb k F x)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

scoped instance isSeparable_LF [Algebra.IsSeparable (kx k F x) F] : Algebra.IsSeparable (Lb k F x) (Fb k F) := by
  refine ⟨fun y => ?_⟩
  have hy : IsSeparable (Lb k F x) y.1 :=
    (mem_separableClosure_iff.mp (FI_le_separableClosure k F x y.2))
  unfold IsSeparable at hy ⊢
  rwa [← minpoly.algHom_eq (IsScalarTower.toAlgHom (Lb k F x) (Fb k F) (Ω F))
    (RingHom.injective _) y]

scoped instance isAlgebraic_FΩ : Algebra.IsAlgebraic (Fb k F) (Ω F) :=
  ⟨fun z => IsAlgebraic.tower_top (Fb k F) (Algebra.IsAlgebraic.isAlgebraic (R := F) z)⟩

scoped instance isAlgebraic_LΩ [FiniteDimensional (kx k F x) F] : Algebra.IsAlgebraic (Lb k F x) (Ω F) :=
  Algebra.IsAlgebraic.trans (Lb k F x) (Fb k F) (Ω F)

scoped instance isAlgClosure_LΩ [FiniteDimensional (kx k F x) F] : IsAlgClosure (Lb k F x) (Ω F) :=
  ⟨inferInstance, inferInstance⟩

scoped instance finite_LEIL [FiniteDimensional (kx k F x) F] : FiniteDimensional (Lb k F x) ↥(EIL k F x) := by
  unfold EIL; infer_instance

def fieldRangeToRange {A B C : Type*} [Field A] [Field B] [Field C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) : ↥f.fieldRange →ₐ[A] ↥f.range where
  toFun z := ⟨z.1, z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

scoped instance isSeparable_LEIL [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    Algebra.IsSeparable (Lb k F x) ↥(EIL k F x) := by
  unfold EIL
  rw [IntermediateField.normalClosure]
  haveI : ∀ f : Fb k F →ₐ[Lb k F x] Ω F, Algebra.IsSeparable (Lb k F x) f.fieldRange := fun f =>
    Algebra.IsSeparable.of_algHom (Lb k F x) (Fb k F)
      (((AlgEquiv.ofInjectiveField f).symm : f.range →ₐ[Lb k F x] Fb k F).comp (fieldRangeToRange f))
  exact IntermediateField.isSeparable_iSup (Lb k F x) (Ω F)

scoped instance isGalois_LEIL [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    IsGalois (Lb k F x) ↥(EIL k F x) := by
  haveI : Normal (Lb k F x) ↥(EIL k F x) := by unfold EIL; infer_instance
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

scoped instance finite_LE [FiniteDimensional (kx k F x) F] : FiniteDimensional (Lb k F x) (Eb k F x) :=
  LinearEquiv.finiteDimensional (ebEquiv k F x).toLinearEquiv

scoped instance isGalois_LE [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    IsGalois (Lb k F x) (Eb k F x) := IsGalois.of_algEquiv (ebEquiv k F x)

scoped instance finite_FE [FiniteDimensional (kx k F x) F] : FiniteDimensional (Fb k F) (Eb k F x) :=
  Module.Finite.of_restrictScalars_finite (Lb k F x) (Fb k F) (Eb k F x)

scoped instance isGalois_FE [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    IsGalois (Fb k F) (Eb k F x) :=
  IsGalois.tower_top_of_isGalois (Lb k F x) (Fb k F) (Eb k F x)

def xL : Lb k F x := ⟨xΩ F x, IntermediateField.mem_adjoin_simple_self (Kc k) (xΩ F x)⟩

theorem xL_coe : (xL k F x).1 = xΩ F x := rfl

variable {k F x}

theorem transcendental_xΩ (hx : Transcendental k x) : Transcendental (Kc k) (xΩ F x) := by
  intro halg
  have h1 : IsAlgebraic k (xΩ F x) := IsAlgebraic.restrictScalars k halg
  exact hx ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom k F (Ω F)) (RingHom.injective _)).mp h1)

theorem transcendental_xL (hx : Transcendental k x) : Transcendental (Kc k) (xL k F x) := by
  rw [← transcendental_algebraMap_iff (RingHom.injective (algebraMap (Lb k F x) (Ω F)))]
  exact transcendental_xΩ hx

variable (k F x)

theorem adjoin_xL_eq_top : (Kc k)⟮xL k F x⟯ = (⊤ : IntermediateField (Kc k) (Lb k F x)) := by
  let val := IsScalarTower.toAlgHom (Kc k) (Lb k F x) (Ω F)
  have hmap : ((Kc k)⟮xL k F x⟯).map val = LI k F x := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [eq_top_iff]
  rintro y -
  have hy : y.1 ∈ ((Kc k)⟮xL k F x⟯).map val := by rw [hmap]; exact y.2
  obtain ⟨y', hy', hyy⟩ := hy
  have : y' = y := Subtype.ext hyy
  rw [← this]
  exact hy'

variable {k F x}

theorem exists_ratFuncEquiv (hx : Transcendental k x) :
    ∃ e : RatFunc (Kc k) ≃ₐ[Kc k] Lb k F x, e RatFunc.X = xL k F x := by
  have htr := transcendental_xL (F := F) hx
  let φ : Polynomial (Kc k) →ₐ[Kc k] Lb k F x := Polynomial.aeval (xL k F x)
  have hφ : nonZeroDivisors (Polynomial (Kc k)) ≤ Submonoid.comap φ (nonZeroDivisors (Lb k F x)) := by
    intro p hp
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    intro h
    exact hp0 ((transcendental_iff_injective.mp htr) (by simpa [φ] using h))
  let e₀ : RatFunc (Kc k) →ₐ[Kc k] Lb k F x := RatFunc.liftAlgHom φ hφ
  have heX : e₀ RatFunc.X = xL k F x := by
    simp [e₀, φ, RatFunc.liftAlgHom_apply]
  have hsurj : Function.Surjective e₀ := by
    intro y
    have hy : y ∈ (⊤ : IntermediateField (Kc k) (Lb k F x)) := IntermediateField.mem_top
    rw [← adjoin_xL_eq_top, ← heX] at hy
    have hle : (Kc k)⟮e₀ RatFunc.X⟯ ≤ e₀.fieldRange := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨RatFunc.X, rfl⟩
    obtain ⟨z, hz⟩ := hle hy
    exact ⟨z, hz⟩
  exact ⟨AlgEquiv.ofBijective e₀ ⟨RingHom.injective _, hsurj⟩, heX⟩

section Uniform

variable (M : Type*) [Field M] [Algebra (Kc k) M] [Algebra (Lb k F x) M]
  [IsScalarTower (Kc k) (Lb k F x) M]

def xM : M := algebraMap (Lb k F x) M (xL k F x)

theorem fieldRange_eq_adjoin_xM :
    (IsScalarTower.toAlgHom (Kc k) (Lb k F x) M).fieldRange = (Kc k)⟮xM (k := k) (F := F) (x := x) M⟯ := by
  rw [AlgHom.fieldRange_eq_map, ← adjoin_xL_eq_top, IntermediateField.adjoin_map, Set.image_singleton]
  rfl

theorem transcendental_xM (hx : Transcendental k x) :
    Transcendental (Kc k) (xM (k := k) (F := F) (x := x) M) := by
  rw [xM, transcendental_algebraMap_iff (RingHom.injective _)]
  exact transcendental_xL hx

theorem finite_adjoin_xM [Module.Finite (Lb k F x) M] :
    Module.Finite (Kc k)⟮xM (k := k) (F := F) (x := x) M⟯ M := by
  classical
  let f := IsScalarTower.toAlgHom (Kc k) (Lb k F x) M
  let e : Lb k F x ≃ₐ[Kc k] (Kc k)⟮xM (k := k) (F := F) (x := x) M⟯ :=
    (AlgEquiv.ofInjectiveField f).trans (IntermediateField.equivOfEq (fieldRange_eq_adjoin_xM M))
  have he : ∀ l : Lb k F x, ((e l : (Kc k)⟮xM (k := k) (F := F) (x := x) M⟯) : M) = algebraMap (Lb k F x) M l := by
    intro l; rfl
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := Lb k F x) (M := M)
  refine Module.finite_def.mpr ⟨(Finset.univ.image b), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro m -
  have hm : m ∈ Submodule.span (Lb k F x) (Set.range b) := by rw [hb]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add z w _ _ hz hw => exact add_mem hz hw
  | smul a z _ hz =>
    have : a • z = (e a) • z := by
      rw [Algebra.smul_def, IntermediateField.smul_def, ← he a, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ hz

end Uniform

theorem isCurveOver_Fb [FiniteDimensional (kx k F x) F] (hx : Transcendental k x) :
    IsCurveOver (Kc k) (Fb k F) := by
  haveI := finite_adjoin_xM (k := k) (F := F) (x := x) (Fb k F)
  exact isCurveOver_of_isAlgClosed_of_transcendental (xM (k := k) (F := F) (x := x) (Fb k F))
    (transcendental_xM _ hx)

theorem isCurveOver_Eb [FiniteDimensional (kx k F x) F] (hx : Transcendental k x) :
    IsCurveOver (Kc k) (Eb k F x) := by
  haveI := finite_adjoin_xM (k := k) (F := F) (x := x) (Eb k F x)
  exact isCurveOver_of_isAlgClosed_of_transcendental (xM (k := k) (F := F) (x := x) (Eb k F x))
    (transcendental_xM _ hx)

variable (k F x)

theorem hfg_Eb [FiniteDimensional (kx k F x) F] :
    ∃ s : Finset (Eb k F x), IntermediateField.adjoin (Kc k) (s : Set (Eb k F x)) = ⊤ := by
  haveI := finite_adjoin_xM (k := k) (F := F) (x := x) (Eb k F x)
  exact exists_finset_adjoin_eq_top (xM (k := k) (F := F) (x := x) (Eb k F x))

theorem hfg_F [FiniteDimensional (kx k F x) F] : ∃ s : Finset F, IntermediateField.adjoin k (s : Set F) = ⊤ :=
  exists_finset_adjoin_eq_top x

theorem hgen_Fb : IntermediateField.adjoin (Kc k) (Set.range (algebraMap F (Fb k F))) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := mkFb_surjective k F y
  induction t using TensorProduct.induction_on with
  | zero => rw [mkFb_zero]; exact zero_mem _
  | tmul f c =>
    rw [mkFb_tmul]
    exact mul_mem (IntermediateField.subset_adjoin _ _ ⟨f, rfl⟩) (IntermediateField.algebraMap_mem _ c)
  | add a b ha hb => rw [mkFb_add]; exact add_mem ha hb

section Frobenius

variable {k F x}
variable (p n : ℕ) [Fact p.Prime] [CharP k p]

scoped instance charP_K : CharP (Kc k) p := charP_of_injective_algebraMap (algebraMap k (Kc k)).injective p
scoped instance expChar_K : ExpChar (Kc k) p := ExpChar.prime Fact.out

def eK : Kc k ≃+* Kc k := iterateFrobeniusEquiv (Kc k) p n

theorem eK_apply (c : Kc k) : eK (k := k) p n c = c ^ p ^ n := by
  rw [eK, iterateFrobeniusEquiv_apply, iterateFrobenius_def]

variable [Finite k]

omit [Fact p.Prime] [CharP k p] in
theorem pow_q_eq_of_mem_k (hq : Nat.card k = p ^ n) (c : k) : c ^ p ^ n = c := by
  haveI := Fintype.ofFinite k
  rw [← hq, Nat.card_eq_fintype_card, FiniteField.pow_card]

def eKinv (hq : Nat.card k = p ^ n) : Kc k ≃ₐ[k] Kc k :=
  { (eK (k := k) p n).symm with
    commutes' := fun c => by
      apply (eK (k := k) p n).injective
      change eK p n ((eK p n).symm (algebraMap k (Kc k) c)) = eK p n (algebraMap k (Kc k) c)
      rw [RingEquiv.apply_symm_apply, eK_apply, ← map_pow, pow_q_eq_of_mem_k p n hq] }

theorem eKinv_apply (hq : Nat.card k = p ^ n) (c : Kc k) :
    eKinv (k := k) p n hq c = (eK (k := k) p n).symm c := rfl

def η (hq : Nat.card k = p ^ n) : F ⊗[k] Kc k ≃ₐ[k] F ⊗[k] Kc k :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[k] F) (eKinv (k := k) p n hq)

def θ (hq : Nat.card k = p ^ n) : F ⊗[k] Kc k →ₐ[k] Ω F :=
  (θ₀ k F).comp (η (F := F) p n hq).toAlgHom

theorem θ_apply (hq : Nat.card k = p ^ n) (t : F ⊗[k] Kc k) :
    θ (F := F) p n hq t = θ₀ k F (η (F := F) p n hq t) := rfl

theorem θ_tmul (hq : Nat.card k = p ^ n) (f : F) (c : Kc k) :
    θ (F := F) p n hq (f ⊗ₜ c) =
      algebraMap F (Ω F) f * algebraMap (Kc k) (Ω F) ((eK (k := k) p n).symm c) := by
  rw [θ_apply, η, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  exact θ₀_tmul k F f _

variable (hq : Nat.card k = p ^ n)
  (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range)

include hconst

omit [Fact p.Prime] [CharP k p] in
theorem injective_θ₀ : Function.Injective (θ₀ k F) := by
  haveI : PerfectField k := PerfectField.ofFinite
  have hK : IsField (F ⊗[k] Kc k) :=
    Algebra.TensorProduct.isField_of_isSeparable_of_forall_isAlgebraic_mem_range k F (Kc k) hconst
  exact injective_of_isField hK (θ₀ k F).toRingHom

def θ₀inv : Fb k F → F ⊗[k] Kc k := fun y =>
  (AlgEquiv.ofInjective (θ₀ k F) (injective_θ₀ (F := F) hconst)).symm ⟨y.1, y.2⟩

omit [Fact p.Prime] [CharP k p] in
theorem θ₀_θ₀inv (y : Fb k F) : θ₀ k F (θ₀inv (F := F) hconst y) = y.1 := by
  have := AlgEquiv.ofInjective_apply (θ₀ k F) (injective_θ₀ (F := F) hconst)
    ((AlgEquiv.ofInjective (θ₀ k F) (injective_θ₀ (F := F) hconst)).symm ⟨y.1, y.2⟩)
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

omit [Fact p.Prime] [CharP k p] in
theorem θ₀inv_mkFb (t : F ⊗[k] Kc k) : θ₀inv (F := F) hconst (mkFb t) = t :=
  injective_θ₀ hconst (θ₀_θ₀inv hconst _)

include hq

def ϕ : Fb k F →ₐ[F] Ω F where
  toFun y := θ p n hq (θ₀inv hconst y)
  map_one' := by
    rw [← mkFb_one, θ₀inv_mkFb, map_one]
  map_mul' a b := by
    obtain ⟨s, rfl⟩ := mkFb_surjective k F a
    obtain ⟨t, rfl⟩ := mkFb_surjective k F b
    rw [← mkFb_mul, θ₀inv_mkFb, θ₀inv_mkFb, θ₀inv_mkFb, map_mul]
  map_zero' := by
    rw [← mkFb_zero, θ₀inv_mkFb, map_zero]
  map_add' a b := by
    obtain ⟨s, rfl⟩ := mkFb_surjective k F a
    obtain ⟨t, rfl⟩ := mkFb_surjective k F b
    rw [← mkFb_add, θ₀inv_mkFb, θ₀inv_mkFb, θ₀inv_mkFb, map_add]
  commutes' f := by
    change θ p n hq (θ₀inv hconst (algebraMap F (Fb k F) f)) = algebraMap F (Ω F) f
    rw [algebraMap_Fb_eq_mkFb, θ₀inv_mkFb, θ_tmul, map_one, map_one, mul_one]

theorem ϕ_mkFb (t : F ⊗[k] Kc k) : ϕ p n hq hconst (mkFb t) = θ p n hq t := by
  change θ p n hq (θ₀inv hconst _) = _
  rw [θ₀inv_mkFb]

def σ : Ω F →ₐ[F] Ω F := (ϕ p n hq hconst).liftNormal (Ω F)

theorem σ_coe (y : Fb k F) : σ p n hq hconst y.1 = ϕ p n hq hconst y :=
  (ϕ p n hq hconst).liftNormal_commutes (Ω F) y

theorem σ_θ₀ (t : F ⊗[k] Kc k) : σ p n hq hconst (θ₀ k F t) = θ p n hq t := by
  rw [← ϕ_mkFb p n hq hconst t]
  exact σ_coe p n hq hconst (mkFb t)

theorem σ_K (c : Kc k) :
    σ p n hq hconst (algebraMap (Kc k) (Ω F) c) = algebraMap (Kc k) (Ω F) ((eK (k := k) p n).symm c) := by
  have : algebraMap (Kc k) (Ω F) c = θ₀ k F (1 ⊗ₜ c) := by rw [θ₀_tmul, map_one, one_mul]
  rw [this, σ_θ₀, θ_tmul, map_one, one_mul]

theorem σ_F (f : F) : σ p n hq hconst (algebraMap F (Ω F) f) = algebraMap F (Ω F) f :=
  (σ p n hq hconst).commutes f

def σE : Ω F ≃ₐ[F] Ω F :=
  AlgEquiv.ofBijective (σ p n hq hconst) (Algebra.IsAlgebraic.algHom_bijective _)

theorem σE_apply (z : Ω F) : σE p n hq hconst z = σ p n hq hconst z := rfl

theorem σEsymm_K (c : Kc k) :
    (σE p n hq hconst).symm (algebraMap (Kc k) (Ω F) c) = algebraMap (Kc k) (Ω F) (eK (k := k) p n c) := by
  apply (σE p n hq hconst).injective
  rw [AlgEquiv.apply_symm_apply, σE_apply, σ_K, RingEquiv.symm_apply_apply]

theorem σEsymm_F (f : F) : (σE p n hq hconst).symm (algebraMap F (Ω F) f) = algebraMap F (Ω F) f := by
  apply (σE p n hq hconst).injective
  rw [AlgEquiv.apply_symm_apply, σE_apply, σ_F]

omit [Fact p.Prime] [CharP k p] [Finite k] hq hconst in
theorem mem_LI_of (g : Ω F ≃ₐ[F] Ω F)
    (hK : ∀ c : Kc k, g (algebraMap (Kc k) (Ω F) c) ∈ Set.range (algebraMap (Kc k) (Ω F)))
    {z : Ω F} (hz : z ∈ LI k F x) : g z ∈ LI k F x := by
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]
    change g (algebraMap F (Ω F) x) ∈ _
    rw [g.commutes]
    exact IntermediateField.mem_adjoin_simple_self _ _
  | algebraMap c =>
    obtain ⟨c', hc'⟩ := hK c
    rw [← hc']
    exact IntermediateField.algebraMap_mem _ _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem σ_mem_LI {z : Ω F} (hz : z ∈ LI k F x) : σE p n hq hconst z ∈ LI k F x :=
  mem_LI_of (g := σE p n hq hconst) (fun c => ⟨_, (σ_K p n hq hconst c).symm⟩) hz

theorem σsymm_mem_LI {z : Ω F} (hz : z ∈ LI k F x) : (σE p n hq hconst).symm z ∈ LI k F x :=
  mem_LI_of (g := (σE p n hq hconst).symm) (fun c => ⟨_, (σEsymm_K p n hq hconst c).symm⟩) hz

theorem σ_mem_FI {z : Ω F} (hz : z ∈ FI k F) : σE p n hq hconst z ∈ FI k F := by
  obtain ⟨t, rfl⟩ := hz
  rw [σE_apply, σ_θ₀, θ_apply]
  exact ⟨_, rfl⟩

theorem σsymm_mem_FI {z : Ω F} (hz : z ∈ FI k F) : (σE p n hq hconst).symm z ∈ FI k F := by
  obtain ⟨t, rfl⟩ := hz
  refine ⟨(η p n hq).symm t, ?_⟩
  apply (σE p n hq hconst).injective
  rw [AlgEquiv.apply_symm_apply, σE_apply, σ_θ₀, θ_apply, AlgEquiv.apply_symm_apply]

omit [Fact p.Prime] [CharP k p] [Finite k] hq hconst in

theorem mem_EIL_of [FiniteDimensional (kx k F x) F] (g : Ω F ≃ₐ[F] Ω F)
    (hL : ∀ z ∈ LI k F x, g z ∈ LI k F x) (hL' : ∀ z ∈ LI k F x, g.symm z ∈ LI k F x)
    (hF : ∀ z ∈ FI k F, g z ∈ FI k F) (hF' : ∀ z ∈ FI k F, g.symm z ∈ FI k F)
    {z : Ω F} (hz : z ∈ EIL k F x) : g z ∈ EIL k F x := by

  let P : IntermediateField (Lb k F x) (Ω F) :=
    { carrier := {w | g w ∈ EIL k F x}
      mul_mem' := fun {a b} ha hb => by
        change g (a * b) ∈ EIL k F x
        rw [map_mul]; exact mul_mem ha hb
      one_mem' := by change g 1 ∈ EIL k F x; rw [map_one]; exact one_mem _
      add_mem' := fun {a b} ha hb => by
        change g (a + b) ∈ EIL k F x
        rw [map_add]; exact add_mem ha hb
      zero_mem' := by change g 0 ∈ EIL k F x; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun l => by
        change g l.1 ∈ EIL k F x
        exact (EIL k F x).algebraMap_mem ⟨g l.1, hL _ l.2⟩
      inv_mem' := fun a ha => by
        change g a⁻¹ ∈ EIL k F x
        rw [map_inv₀]; exact inv_mem ha }
  suffices h : EIL k F x ≤ P from h hz
  unfold EIL
  rw [normalClosure_le_iff]
  intro τ

  let gF : Fb k F →+* Fb k F :=
    (g.symm : Ω F →+* Ω F).restrict (FI k F) (FI k F) fun w hw => hF' w hw
  have hgF : ∀ y : Fb k F, (gF y).1 = g.symm y.1 := fun _ => rfl
  let τ'' : Fb k F →+* Ω F := (g : Ω F →+* Ω F).comp (τ.toRingHom.comp gF)
  have hτ'' : ∀ y : Fb k F, τ'' y = g (τ (gF y)) := fun _ => rfl
  let τ' : Fb k F →ₐ[Lb k F x] Ω F :=
    { τ'' with
      commutes' := fun l => by
        change τ'' (algebraMap (Lb k F x) (Fb k F) l) = l.1
        rw [hτ'']
        have : gF (algebraMap (Lb k F x) (Fb k F) l) =
            algebraMap (Lb k F x) (Fb k F) ⟨g.symm l.1, hL' _ l.2⟩ := Subtype.ext rfl
        rw [this, τ.commutes]
        exact g.apply_symm_apply l.1 }
  have hτ' : ∀ y : Fb k F, τ' y = g (τ (gF y)) := fun _ => rfl
  rintro _ ⟨y, rfl⟩
  change g (τ y) ∈ EIL k F x
  have hy : g (τ y) = τ' ⟨g y.1, hF _ y.2⟩ := by
    rw [hτ']
    congr 2
    exact Subtype.ext (by rw [hgF]; exact (g.symm_apply_apply _).symm)
  rw [hy]
  exact AlgHom.fieldRange_le_normalClosure τ' ⟨_, rfl⟩

variable [FiniteDimensional (kx k F x) F]

theorem σ_mem_EI {z : Ω F} (hz : z ∈ EI k F x) : σE p n hq hconst z ∈ EI k F x :=
  (mem_EI k F x).mpr (mem_EIL_of (g := σE p n hq hconst)
    (fun _ h => σ_mem_LI p n hq hconst h) (fun _ h => σsymm_mem_LI p n hq hconst h)
    (fun _ h => σ_mem_FI p n hq hconst h) (fun _ h => σsymm_mem_FI p n hq hconst h)
    ((mem_EI k F x).mp hz))

theorem σsymm_mem_EI {z : Ω F} (hz : z ∈ EI k F x) : (σE p n hq hconst).symm z ∈ EI k F x :=
  (mem_EI k F x).mpr (mem_EIL_of (g := (σE p n hq hconst).symm)
    (fun _ h => σsymm_mem_LI p n hq hconst h)
    (fun _ h => by rw [AlgEquiv.symm_symm]; exact σ_mem_LI p n hq hconst h)
    (fun _ h => σsymm_mem_FI p n hq hconst h)
    (fun _ h => by rw [AlgEquiv.symm_symm]; exact σ_mem_FI p n hq hconst h)
    ((mem_EI k F x).mp hz))

end Frobenius

section Psi

variable {k F x}
variable (p n : ℕ) [Fact p.Prime] [CharP k p] [Finite k] (hq : Nat.card k = p ^ n)
  (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range)

include hq hconst

def ψΩ : Ω F →+* Ω F where
  toFun z := (σ p n hq hconst z) ^ p ^ n
  map_one' := by rw [map_one, one_pow]
  map_mul' a b := by rw [map_mul, mul_pow]
  map_zero' := by rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  map_add' a b := by
    haveI : CharP (Ω F) p := charP_of_injective_algebraMap (algebraMap k (Ω F)).injective p
    rw [map_add, add_pow_char_pow]

theorem ψΩ_apply (z : Ω F) : ψΩ p n hq hconst z = (σ p n hq hconst z) ^ p ^ n := rfl

theorem ψΩ_K (c : Kc k) : ψΩ p n hq hconst (algebraMap (Kc k) (Ω F) c) = algebraMap (Kc k) (Ω F) c := by
  rw [ψΩ_apply, σ_K, ← map_pow, ← eK_apply, RingEquiv.apply_symm_apply]

theorem ψΩ_F (f : F) : ψΩ p n hq hconst (algebraMap F (Ω F) f) = algebraMap F (Ω F) (f ^ p ^ n) := by
  rw [ψΩ_apply, σ_F, map_pow]

variable (S : IntermediateField (Kc k) (Ω F))
  (hS : ∀ z ∈ S, σE p n hq hconst z ∈ S)

include hS

theorem ψΩ_mem {z : Ω F} (hz : z ∈ S) : ψΩ p n hq hconst z ∈ S := by
  rw [ψΩ_apply]
  exact pow_mem (hS z hz) _

def ψS : S →ₐ[Kc k] S :=
  { (ψΩ p n hq hconst).restrict S S (fun _ hz => ψΩ_mem p n hq hconst S hS hz) with
    commutes' := fun c => Subtype.ext (ψΩ_K p n hq hconst c) }

theorem ψS_coe (z : S) : (ψS p n hq hconst S hS z).1 = ψΩ p n hq hconst z.1 := rfl

omit [Fact p.Prime] [CharP k p] [Finite k] hq hconst hS in

theorem pow_mem_of_stable (g : Ω F ≃ₐ[F] Ω F) (hg : ∀ z ∈ S, g z ∈ S) (r : ℕ) {z : Ω F}
    (hz : z ∈ S) : (g ^ r) z ∈ S := by
  induction r generalizing z with
  | zero => simpa using hz
  | succ r ih => rw [pow_succ, AlgEquiv.mul_apply]; exact ih (hg z hz)

theorem σpow_mem (r : ℕ) {z : Ω F} (hz : z ∈ S) : (σE p n hq hconst ^ r) z ∈ S :=
  pow_mem_of_stable S _ hS r hz

omit hS in
theorem σpow_symm_mem (hS' : ∀ z ∈ S, (σE p n hq hconst).symm z ∈ S) (r : ℕ) {z : Ω F}
    (hz : z ∈ S) : (σE p n hq hconst ^ r).symm z ∈ S := by
  rw [← AlgEquiv.aut_inv, ← inv_pow, AlgEquiv.aut_inv]
  exact pow_mem_of_stable S _ hS' r hz

theorem ψS_pow_coe (r : ℕ) (z : S) :
    ((ψS p n hq hconst S hS ^ r) z).1 = ((σE p n hq hconst ^ r) z.1) ^ (p ^ n) ^ r := by
  induction r generalizing z with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, AlgHom.mul_apply, ih, ψS_coe, ψΩ_apply, ← σE_apply p n hq hconst, map_pow, ← pow_mul,
      ← pow_succ', ← AlgEquiv.mul_apply, ← pow_succ]

theorem isFrobeniusEndo_ψS_pow (hS' : ∀ z ∈ S, (σE p n hq hconst).symm z ∈ S) (r : ℕ) :
    IsFrobeniusEndo ((p ^ n) ^ r) (ψS p n hq hconst S hS ^ r) where
  pow_mem_range z := by
    refine ⟨⟨(σE p n hq hconst ^ r).symm z.1, σpow_symm_mem p n hq hconst S hS' r z.2⟩, Subtype.ext ?_⟩
    rw [ψS_pow_coe]
    change ((σE p n hq hconst ^ r) ((σE p n hq hconst ^ r).symm z.1)) ^ (p ^ n) ^ r = z.1 ^ (p ^ n) ^ r
    rw [AlgEquiv.apply_symm_apply]
  mem_range_pow z := by
    refine ⟨⟨(σE p n hq hconst ^ r) z.1, σpow_mem p n hq hconst S hS r z.2⟩, Subtype.ext ?_⟩
    rw [ψS_pow_coe]
    rfl

theorem ψS_pow_isIntegral (hS' : ∀ z ∈ S, (σE p n hq hconst).symm z ∈ S) (r : ℕ) :
    ((ψS p n hq hconst S hS) ^ r).toRingHom.IsIntegral :=
  (isFrobeniusEndo_ψS_pow p n hq hconst S hS hS' r).isIntegral
    (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

theorem ψS_isIntegral (hS' : ∀ z ∈ S, (σE p n hq hconst).symm z ∈ S) :
    (ψS p n hq hconst S hS).toRingHom.IsIntegral := by
  simpa using ψS_pow_isIntegral p n hq hconst S hS hS' 1

end Psi

section Three

variable {k F x}
variable (p n : ℕ) [Fact p.Prime] [CharP k p] [Finite k] (hq : Nat.card k = p ^ n)
  (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range)

include hq hconst

def ψL : Lb k F x →ₐ[Kc k] Lb k F x :=
  ψS p n hq hconst (LI k F x) fun _ h => σ_mem_LI p n hq hconst h

def ψF : Fb k F →ₐ[Kc k] Fb k F :=
  ψS p n hq hconst (FI k F) fun _ h => σ_mem_FI p n hq hconst h

def ψE [FiniteDimensional (kx k F x) F] : Eb k F x →ₐ[Kc k] Eb k F x :=
  ψS p n hq hconst (EI k F x) fun _ h => σ_mem_EI (x := x) p n hq hconst h

theorem ψL_pow_isIntegral (r : ℕ) : (ψL (x := x) p n hq hconst ^ r).toRingHom.IsIntegral :=
  ψS_pow_isIntegral p n hq hconst (LI k F x) _ (fun _ h => σsymm_mem_LI p n hq hconst h) r

theorem ψF_pow_isIntegral (r : ℕ) : (ψF (F := F) p n hq hconst ^ r).toRingHom.IsIntegral :=
  ψS_pow_isIntegral p n hq hconst (FI k F) _ (fun _ h => σsymm_mem_FI p n hq hconst h) r

theorem ψF_isIntegral : (ψF (F := F) p n hq hconst).toRingHom.IsIntegral :=
  ψS_isIntegral p n hq hconst (FI k F) _ (fun _ h => σsymm_mem_FI p n hq hconst h)

theorem ψE_pow_isIntegral [FiniteDimensional (kx k F x) F] (r : ℕ) :
    (ψE (x := x) p n hq hconst ^ r).toRingHom.IsIntegral :=
  ψS_pow_isIntegral p n hq hconst (EI k F x) _ (fun _ h => σsymm_mem_EI p n hq hconst h) r

theorem isFrobeniusEndo_ψE_pow [FiniteDimensional (kx k F x) F] (r : ℕ) :
    IsFrobeniusEndo ((p ^ n) ^ r) (ψE (x := x) p n hq hconst ^ r) :=
  isFrobeniusEndo_ψS_pow p n hq hconst (EI k F x) _ (fun _ h => σsymm_mem_EI p n hq hconst h) r

theorem ψL_pow_coe (r : ℕ) (z : Lb k F x) :
    ((ψL (x := x) p n hq hconst ^ r) z).1 = ((σE p n hq hconst ^ r) z.1) ^ (p ^ n) ^ r :=
  ψS_pow_coe p n hq hconst (LI k F x) _ r z

theorem ψF_pow_coe (r : ℕ) (z : Fb k F) :
    ((ψF (F := F) p n hq hconst ^ r) z).1 = ((σE p n hq hconst ^ r) z.1) ^ (p ^ n) ^ r :=
  ψS_pow_coe p n hq hconst (FI k F) _ r z

theorem ψE_pow_coe [FiniteDimensional (kx k F x) F] (r : ℕ) (z : Eb k F x) :
    ((ψE (x := x) p n hq hconst ^ r) z).1 = ((σE p n hq hconst ^ r) z.1) ^ (p ^ n) ^ r :=
  ψS_pow_coe p n hq hconst (EI k F x) _ r z

theorem ψF_algebraMap (f : F) :
    ψF (F := F) p n hq hconst (algebraMap F (Fb k F) f) = algebraMap F (Fb k F) (f ^ Nat.card k) := by
  apply Subtype.ext
  rw [hq]
  change ψΩ p n hq hconst (algebraMap F (Ω F) f) = algebraMap F (Ω F) (f ^ p ^ n)
  exact ψΩ_F p n hq hconst f

theorem hcomp_LE [FiniteDimensional (kx k F x) F] (r : ℕ) (y : Lb k F x) :
    (ψE (x := x) p n hq hconst ^ r) (algebraMap (Lb k F x) (Eb k F x) y) =
      algebraMap (Lb k F x) (Eb k F x) ((ψL (x := x) p n hq hconst ^ r) y) := by
  apply Subtype.ext
  rw [ψE_pow_coe, algebraMap_LE, algebraMap_LE, ψL_pow_coe]

theorem hcomp_FE [FiniteDimensional (kx k F x) F] (r : ℕ) (y : Fb k F) :
    (ψE (x := x) p n hq hconst ^ r) (algebraMap (Fb k F) (Eb k F x) y) =
      algebraMap (Fb k F) (Eb k F x) ((ψF (F := F) p n hq hconst ^ r) y) := by
  apply Subtype.ext
  rw [ψE_pow_coe, algebraMap_FE, algebraMap_FE, ψF_pow_coe]

theorem ψL_pow_xL (r : ℕ) : (ψL (x := x) p n hq hconst ^ r) (xL k F x) = xL k F x ^ (p ^ n) ^ r := by
  apply Subtype.ext
  rw [ψL_pow_coe]
  have hfix : ∀ r, (σE p n hq hconst ^ r) (xL k F x).1 = (xL k F x).1 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, AlgEquiv.mul_apply, xL_coe, σE_apply, σ_F]; exact ih
  rw [hfix]
  rfl

theorem count_L (hx : Transcendental k x) (r : ℕ) (hr : 0 < r) :
    (Function.fixedPoints (Place.restrictAlong (ψL (x := x) p n hq hconst ^ r)
        (ψL_pow_isIntegral p n hq hconst r))).Finite ∧
      Nat.card (Function.fixedPoints (Place.restrictAlong (ψL (x := x) p n hq hconst ^ r)
        (ψL_pow_isIntegral p n hq hconst r))) = (p ^ n) ^ r + 1 := by
  obtain ⟨e, heX⟩ := exists_ratFuncEquiv (F := F) hx
  let φP : RatFunc (Kc k) →ₐ[Kc k] RatFunc (Kc k) :=
    (e.symm : Lb k F x →ₐ[Kc k] RatFunc (Kc k)).comp
      ((ψL (x := x) p n hq hconst ^ r).comp (e : RatFunc (Kc k) →ₐ[Kc k] Lb k F x))
  have hφP : ∀ a, e (φP a) = (ψL (x := x) p n hq hconst ^ r) (e a) := by
    intro a; simp [φP]
  have hφPX : φP RatFunc.X = RatFunc.X ^ (p ^ n) ^ r := by
    apply e.injective
    rw [hφP, heX, ψL_pow_xL, map_pow, heX]
  have hφPi : φP.toRingHom.IsIntegral := by
    have h1 : ((ψL (x := x) p n hq hconst ^ r).comp
        (e : RatFunc (Kc k) →ₐ[Kc k] Lb k F x)).toRingHom.IsIntegral :=
      RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ e.surjective)
        (ψL_pow_isIntegral p n hq hconst r)
    exact RingHom.IsIntegral.trans _ _ h1 (RingHom.isIntegral_of_surjective _ e.symm.surjective)
  have hp := (Fact.out : p.Prime)
  have hQ1 : 1 < (p ^ n) ^ r := by
    have hpn : 1 < p ^ n := by
      rw [← hq]
      haveI := Fintype.ofFinite k
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    exact Nat.one_lt_pow hr.ne' hpn
  have hn0 : n ≠ 0 := by
    rintro rfl
    haveI := Fintype.ofFinite k
    rw [pow_zero, Nat.card_eq_fintype_card] at hq
    exact absurd hq (Fintype.one_lt_card).ne'
  have hQK : (((p ^ n) ^ r : ℕ) : Kc k) = 0 := by
    rw [Nat.cast_pow, Nat.cast_pow, CharP.cast_eq_zero (Kc k) p, zero_pow hn0, zero_pow hr.ne']
  have hP := AlgebraicCurve.RationalFunctionField.finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
    (Kc k) ((p ^ n) ^ r) hQ1 hQK φP hφPi hφPX
  have htr := natCard_fixedPoints_congr e φP hφPi (ψL (x := x) p n hq hconst ^ r)
    (ψL_pow_isIntegral p n hq hconst r) hφP
  exact ⟨htr.1.mp hP.1, htr.2 ▸ hP.2⟩

end Three

end Construction

section Assembly

variable {k : Type u} {F : Type v} [Field k] [Finite k] [Field F] [Algebra k F]
  [IsCurveOver k F]

omit [Finite k] [IsCurveOver k F] in
theorem hconst_of_constantsAreBase (hC : ConstantsAreBase k F) (y : F) (hy : IsAlgebraic k y) :
    y ∈ (algebraMap k F).range := by
  have hmem : y ∈ LSpace (0 : Divisor k F) := by
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    rw [v.ord_eq_zero_of_isAlgebraic hy]
    simp
  have hC' : LSpace (0 : Divisor k F) = LinearMap.range (Algebra.linearMap k F) := hC
  rw [hC', LinearMap.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

theorem main (hC : ConstantsAreBase k F) (x : F) (hx : Transcendental k x)
    [FiniteDimensional (kx k F x) F] [Algebra.IsSeparable (kx k F x) F] :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℝ, ∀ r : ℕ, 0 < r → m ∣ r →
      (Nat.card k : ℝ) ^ r + 1 - c * Real.sqrt (Nat.card k : ℝ) ^ r ≤
        ((∑ d ∈ Nat.divisors r,
            d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} : ℕ) : ℝ) := by
  classical

  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI := Fintype.ofFinite k
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨n', -, hcard⟩ := FiniteField.card k p
  have hq : Nat.card k = p ^ (n' : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hq2 : 2 ≤ Nat.card k := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hconst := hconst_of_constantsAreBase hC

  haveI hcF : IsCurveOver (Kc k) (Fb k F) := isCurveOver_Fb (x := x) hx
  haveI hcE : IsCurveOver (Kc k) (Eb k F x) := isCurveOver_Eb hx

  obtain ⟨s, hs0, hs⟩ := exists_sq_lt_pow (Nat.card k) (genusFF (Kc k) (Eb k F x)) hq2
  refine ⟨2 * s, by omega,
    ((Fintype.card (Eb k F x ≃ₐ[Lb k F x] Eb k F x) : ℝ) - 1) *
      (2 * (genusFF (Kc k) (Eb k F x) : ℝ) + 1), fun r hr hmr => ?_⟩
  obtain ⟨j, rfl⟩ := hmr
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hr
    · exact h0

  set q : ℕ := Nat.card k with hqdef
  set g : ℕ := genusFF (Kc k) (Eb k F x) with hg
  set n : ℕ := (n' : ℕ) with hn
  set R : ℕ := 2 * s * j with hR
  set kk : ℕ := s * j with hkk
  have hr2 : R = 2 * kk := by rw [hR, hkk]; ring
  set q₀ : ℕ := q ^ kk with hq₀
  have hq₀g : (g + 1) ^ 2 < q₀ := lt_of_lt_of_le hs
    (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right s hj))
  have hRpos : 0 < R := hr
  have hqR : (p ^ n) ^ R = q₀ ^ 2 := by
    rw [← hq, hq₀, ← pow_mul, hr2]
    ring

  set ψEr := ψE (x := x) p n hq hconst ^ R with hψErdef
  have hψEr : ψEr.toRingHom.IsIntegral := ψE_pow_isIntegral p n hq hconst R
  set ψFr := ψF (F := F) p n hq hconst ^ R with hψFrdef
  have hψFr : ψFr.toRingHom.IsIntegral := ψF_pow_isIntegral p n hq hconst R
  set ψLr := ψL (x := x) p n hq hconst ^ R with hψLrdef
  have hψLr : ψLr.toRingHom.IsIntegral := ψL_pow_isIntegral p n hq hconst R

  have hD := AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
    k (Kc k) F (Fb k F) (hfg_F k F x) (hgen_Fb k F) (ψF (F := F) p n hq hconst)
    (ψF_isIntegral p n hq hconst) (ψF_algebraMap p n hq hconst) R hRpos
  rw [iterate_restrictAlong_eq _ _ R hψFr] at hD

  have hP := count_L (x := x) p n hq hconst hx R hRpos

  have hOL := AlgebraicCurve.finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
    (Kc k) (Lb k F x) (Eb k F x) ψLr hψLr ψEr hψEr (hcomp_LE p n hq hconst R) hP.1
  have hOF := AlgebraicCurve.finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
    (Kc k) (Fb k F) (Eb k F x) ψFr hψFr ψEr hψEr (hcomp_FE p n hq hconst R) hD.1

  let N : (Eb k F x ≃ₐ[Lb k F x] Eb k F x) → ℕ := fun τ =>
    Nat.card {W : Place (Kc k) (Eb k F x) |
      W.restrictAlong ψEr hψEr = SemilinearAut.ofAlgAut (τ.restrictScalars (Kc k)) • W}
  have hU : ∀ τ, (N τ : ℝ) ≤ ((q : ℝ) ^ (2 * kk) + 1) + (2 * (g : ℝ) + 1) * (q : ℝ) ^ kk := by
    intro τ
    let τK : Eb k F x ≃ₐ[Kc k] Eb k F x := τ.restrictScalars (Kc k)
    have hint := comp_algEquiv_isIntegral ψEr hψEr τK
    have hfrob : IsFrobeniusEndo (q₀ ^ 2) (ψEr.comp (τK : Eb k F x →ₐ[Kc k] Eb k F x)) := by
      rw [← hqR]
      exact IsFrobeniusEndo.comp_algEquiv (isFrobeniusEndo_ψE_pow p n hq hconst R) τK
    have hB := AlgebraicCurve.natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
      (Kc k) (Eb k F x) (hfg_Eb k F x) q₀ hq₀g _ hint hfrob
    rw [fixedPoints_restrictAlong_comp_algEquiv ψEr hψEr τK hint] at hB
    have h2 : (N τ : ℝ) < (q₀ : ℝ) ^ 2 + 1 + (2 * (g : ℝ) + 1) * q₀ := by
      have := hB.2
      exact_mod_cast this
    have hq₀R : (q₀ : ℝ) = (q : ℝ) ^ kk := by rw [hq₀]; push_cast; ring
    rw [hq₀R] at h2
    have : ((q : ℝ) ^ kk) ^ 2 = (q : ℝ) ^ (2 * kk) := by rw [← pow_mul, mul_comm]
    linarith

  have hbig : (Fintype.card (Eb k F x ≃ₐ[Lb k F x] Eb k F x) : ℝ) * ((q : ℝ) ^ (2 * kk) + 1) =
      ∑ τ, (N τ : ℝ) := by
    have h1 : Fintype.card (Eb k F x ≃ₐ[Lb k F x] Eb k F x) = Module.finrank (Lb k F x) (Eb k F x) := by
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    have h2 := hOL.2
    rw [hP.2] at h2
    have h3 : (Module.finrank (Lb k F x) (Eb k F x) : ℝ) * (((p ^ n) ^ R + 1 : ℕ) : ℝ) =
        ∑ τ, (N τ : ℝ) := by
      exact_mod_cast h2
    rw [h1, ← h3]
    congr 1
    rw [hr2, hq]
    push_cast
    ring

  let e : (Eb k F x ≃ₐ[Fb k F] Eb k F x) → (Eb k F x ≃ₐ[Lb k F x] Eb k F x) :=
    fun τ => τ.restrictScalars (Lb k F x)
  have hsmall : Fintype.card (Eb k F x ≃ₐ[Fb k F] Eb k F x) *
      (∑ d ∈ Nat.divisors R, d * Nat.card {v : Place k F | v.deg = d}) = ∑ h, N (e h) := by
    have h1 : Fintype.card (Eb k F x ≃ₐ[Fb k F] Eb k F x) = Module.finrank (Fb k F) (Eb k F x) := by
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [h1, ← hD.2, hOF.2]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : (τ.restrictScalars (Lb k F x)).restrictScalars (Kc k) = τ.restrictScalars (Kc k) :=
      AlgEquiv.ext fun _ => rfl
    simp only [N, e, this]
  have hfinal := sub_le_of_identities N e _ _ _ hbig hU hsmall

  have hsqrt : Real.sqrt (q : ℝ) ^ (2 * s * j) = (q : ℝ) ^ kk := by
    rw [show 2 * s * j = 2 * kk from hr2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsqrt]
  have hpow : (q : ℝ) ^ (2 * s * j) = (q : ℝ) ^ (2 * kk) := by rw [show 2 * s * j = 2 * kk from hr2]
  rw [hpow]
  linarith [hfinal]

end Assembly

end BombieriLower
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve.BombieriLower"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve.BombieriLower P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve"

p2m_open "AlgebraicCurve~genus" in open _root_.P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve AlgebraicCurve.BombieriLower in
theorem solution
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℝ, ∀ r : ℕ, 0 < r → m ∣ r →
      (Nat.card k : ℝ) ^ r + 1 - c * Real.sqrt (Nat.card k : ℝ) ^ r ≤
        ((∑ d ∈ Nat.divisors r,
            d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} : ℕ) : ℝ) := by
  haveI : PerfectField k := PerfectField.ofFinite
  obtain ⟨x, hx, hfin, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  haveI := hfin
  haveI := hsep
  exact main hC x hx

end
end S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places
end P2MW
export P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places (solution)
