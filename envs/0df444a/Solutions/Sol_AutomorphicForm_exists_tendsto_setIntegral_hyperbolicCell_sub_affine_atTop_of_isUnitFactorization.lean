-- Prove2me | solution 1 for AutomorphicForm.exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/33529d2f-550f-5562-918e-073a68d90095

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
import Theorems.Thm_AutomorphicForm_setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell
import Theorems.Thm_AutomorphicForm_isSemiLocalFactorization_self_of_finComponent_factorization
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.gl2Weyl_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply"
p2m_attr_erase "simp" "Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace HAKUnit

private theorem _root_.HAKUnit.exists_notMem_finset (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "HAKUnit" "exists_notMem_finset"

theorem exists_uniformizer_cosetSystem (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ (ϖ : v.adicCompletionIntegers K) (hirr : Irreducible ϖ)
      (h0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
      (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K)),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi ϖ h0) rT := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have h0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective (v.adicCompletionIntegers K) (v.adicCompletion K))).mp h)
  haveI : Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) := by
    rw [← hϖ.maximalIdeal_eq]
    exact (inferInstance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  obtain ⟨n, rT, h⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_integralSubgroup_diagPi hϖ h0
  exact ⟨ϖ, hϖ, h0, n, rT, h⟩

theorem ramificationIdx_under_self (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hu : HeightOneSpectrum.under (𝓞 K) w = w := HeightOneSpectrum.ext (Ideal.comap_id w.asIdeal)
  rw [hu]
  apply Ideal.ramificationIdx_spec
  · rw [pow_one, Algebra.algebraMap_self, Ideal.map_id]
  · rw [Algebra.algebraMap_self, Ideal.map_id]
    intro hle
    haveI := w.isPrime
    have hlt : w.asIdeal ^ (1 + 1) < w.asIdeal ^ 1 := Ideal.pow_succ_lt_pow w.ne_bot 1
    rw [pow_one] at hlt
    exact absurd (le_antisymm hle (le_of_lt hlt)) (ne_of_lt hlt).symm

end HAKUnit

open HAKUnit AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hff : ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
      (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      AutomorphicForm.IsUnitFactorization K S f fa ff fS) :
    ∃ a b : ℂ, Filter.Tendsto (fun R : ℝ =>
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ((R : ℂ) * a + b)) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨S, fa, ff, fS, hU⟩ := hff
  obtain ⟨hfa, hfin, hfS, hprod, hvan, hfeq⟩ := hU

  obtain ⟨v₁, hv₁⟩ := exists_notMem_finset K S
  obtain ⟨v₂, hv₂⟩ := exists_notMem_finset K (insert v₁ S)
  have hv₂₁ : v₂ ≠ v₁ := fun h => hv₂ (h ▸ Finset.mem_insert_self _ _)
  have hv₂S : v₂ ∉ S := fun h => hv₂ (Finset.mem_insert_of_mem h)
  set T : Finset (HeightOneSpectrum (𝓞 K)) := {v₁, v₂} with hTdef
  have hT2 : 2 ≤ T.card := by rw [hTdef, Finset.card_pair hv₂₁.symm]
  have hTS : ∀ v ∈ T, v ∉ S := by
    intro v hv
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hv₁
    · exact hv₂S

  choose ϖs hϖirr hϖ0 ns rTs hrTs using fun v : HeightOneSpectrum (𝓞 K) => exists_uniformizer_cosetSystem K v
  let zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) := fun v =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖs v) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; exact pow_ne_zero _ (hϖ0 v))
  have hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖs v) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    fun v _ => rfl

  have hprod' : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ v ∉ S ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
        ff h = ∏ v ∈ S ∪ T,
          (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin ((fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv) → Fin (ns v),
                (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ ((fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv))⁻¹ * x)
            else fS v) (AdelicLevel.finComponent (𝓞 K) K v h) := by
    intro h hint
    have hdisj : Disjoint S T := Finset.disjoint_right.2 fun v hv => hTS v hv
    rw [Finset.prod_union hdisj]

    have hTfac : ∀ v ∈ T, (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin ((fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv) → Fin (ns v),
                (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ ((fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv))⁻¹ * x)
            else fS v) (AdelicLevel.finComponent (𝓞 K) K v h) =
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (AdelicLevel.finComponent (𝓞 K) K v h) := by
      intro v hv
      rw [dif_pos hv]
      simp only [pow_zero, mul_one]
      rw [Fintype.sum_unique]
      · simp [List.ofFn_zero]
    have hSfac : ∀ v ∈ S, (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin ((fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv) → Fin (ns v),
                (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ ((fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv))⁻¹ * x)
            else fS v) (AdelicLevel.finComponent (𝓞 K) K v h) = fS v (AdelicLevel.finComponent (𝓞 K) K v h) := by
      intro v hv
      rw [dif_neg (Finset.disjoint_left.1 hdisj hv)]
    rw [Finset.prod_congr rfl hSfac, Finset.prod_congr rfl hTfac]
    by_cases hT : ∀ v ∈ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v
    · have hT1 : (∏ v ∈ T, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (AdelicLevel.finComponent (𝓞 K) K v h)) = 1 :=
        Finset.prod_eq_one fun v hv => by rw [Set.indicator_of_mem (hT v hv)]
      rw [hT1, mul_one]
      exact hprod h (fun v hvS => by
        by_cases hvT : v ∈ T
        · exact hT v hvT
        · exact hint v (by rw [Finset.mem_union, not_or]; exact ⟨hvS, hvT⟩))
    · push Not at hT
      obtain ⟨v, hvT, hv⟩ := hT
      have hT0 : (∏ v ∈ T, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (AdelicLevel.finComponent (𝓞 K) K v h)) = 0 :=
        Finset.prod_eq_zero hvT (by rw [Set.indicator_of_notMem hv])
      rw [hT0, mul_zero]
      exact hvan h ⟨v, hTS v hvT, hv⟩
  have hvan' : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∃ v ∉ S ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0 :=
    fun h ⟨v, hv, hh⟩ => hvan h ⟨v, fun hvS => hv (Finset.mem_union_left _ hvS), hh⟩
  have hSLF := AutomorphicForm.isSemiLocalFactorization_self_of_finComponent_factorization K S T fa fS ns rTs zs
    (fun _ _ => 0) (fun _ _ => 0) f ff hfa hfS hfin hprod' hvan' hfeq

  let D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K := M4aHerbrand.identityDescent (𝓞 K) K K
  have hgen : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K) := fun τ => by
    rw [Subsingleton.elim τ 1]; exact Subgroup.one_mem _
  have hSL : ∀ w : HeightOneSpectrum (𝓞 K),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))) :=
    fun w hw => absurd (ramificationIdx_under_self K w) hw
  obtain ⟨hc0, hTc, hΦ₀S, hΦ₀s, hΦ₀⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  let ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 K) :=
    fun v => ⟨v, HeightOneSpectrum.ext (Ideal.comap_id v.asIdeal)⟩

  obtain ⟨μ, ν, hmain⟩ :=
    AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
      K K α β hα hαβ ΦK νZK ΩK hΩK D 1 hgen ∅ ξ hξc hξt S fa
      (fun v => fun x : GL (Fin 2) (K ⊗[K] v.adicCompletion K) =>
          fS v (Matrix.GeneralLinearGroup.map
              ((Pi.evalRingHom (fun w : v.Extension (𝓞 K) => w.1.adicCompletion K) (⟨v, HeightOneSpectrum.ext (Ideal.comap_id v.asIdeal)⟩ : v.Extension (𝓞 K))).comp
                (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K K (𝓞 K) v).toRingEquiv.toRingHom) x))
      _ _ _ _ hc0 _ hTc _ hΦ₀S hΦ₀s hΦ₀
      T hT2 (fun v _ w _ hw => by simp at hw) ws (fun v => v)
      (fun v _ => by rw [one_smul])
      (fun v => ϖs v) (fun v _ => hϖirr v) (fun v _ => hϖ0 v) ns rTs (fun v _ => hrTs v) zs hzs
  obtain ⟨R₀, hR⟩ := hmain (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0)
    (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0) f ff hSLF
  refine ⟨ν (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0)
      (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0),
    μ (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0)
      (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0), ?_⟩
  have hev : ∀ R : ℝ, R₀ ≤ R →
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (R : ℂ) * ν (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0)
          (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0) +
        μ (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0)
          (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0) := by
    intro R hR0
    have h3 := (hR R hR0).2.2
    have hB := AutomorphicForm.setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell
      K α β ΦK ΦK νZK ΩK D hgen ξ f R
    exact hB.symm.trans h3
  have hE : (fun R : ℝ =>
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ((R : ℂ) * ν (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0)
          (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0) +
        μ (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0)
          (fun v => if hv : v ∈ T then (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : _ ∈ T) => (0 : ℕ)) v hv else 0))) =ᶠ[Filter.atTop] fun _ => (0 : ℂ) :=
    Filter.eventually_atTop.2 ⟨R₀, fun R hR0 => by dsimp only; rw [hev R hR0, sub_self]⟩
  exact (tendsto_const_nhds (x := (0 : ℂ))).congr' hE.symm

end S_AutomorphicForm_exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization (solution)
