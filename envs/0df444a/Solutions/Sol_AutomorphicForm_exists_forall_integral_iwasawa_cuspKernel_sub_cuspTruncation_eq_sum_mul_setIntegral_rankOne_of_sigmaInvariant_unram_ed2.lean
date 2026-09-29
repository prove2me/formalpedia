-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/157ac4d5-fb1d-5a4d-9a53-0dbdc8160a13

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
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_TwistedBruhat_integral_iwasawa_indicator_cuspKernel_sub_cuspTruncation_eq_measure_mul_integral_of_sigmaInvariant_ed2
import Theorems.Thm_AutomorphicForm_TwistedBruhat_lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
import Theorems.Thm_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub
import Theorems.Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_integral_finsum_tracePushforward_sub_eq_sum_mul_setIntegral_rankOne_of_transversal
import Theorems.Thm_NumberField_Idele_exists_forall_measure_eq_mul_idelicHaar
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_TraceFibrePushforward_exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq
import Theorems.Thm_TwistedUnipotentTerm_exists_transversal
import Theorems.Thm_AutomorphicForm_TwistedBruhat_apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_idelesBaseChange
import Theorems.Thm_AutomorphicForm_TransversalMeasure_exists_measurableSet_isFundamentalDomain_idelesBaseChange_principal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal
open scoped TensorProduct.RightActions

theorem thresh_loc
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (c R : ℝ) (hc : 0 < c) (t : (AdeleRing (𝓞 L) L)ˣ) (ht : NumberField.TateGlobal.ideleNorm L t = c)
    (y : (AdeleRing (𝓞 K) K)ˣ) :
    (Real.exp R < NumberField.AdelicHeight.adelicHeight L
        (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) ↔
      (c⁻¹ ^ ((Module.finrank K L : ℝ)⁻¹) * Real.exp ((Module.finrank K L : ℝ)⁻¹ * R) <
        NumberField.TateGlobal.ideleNorm K y)) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rw [NumberField.AdelicHeight.adelicHeight_diagOne, NumberField.TateGlobal.ideleNorm_mul, ht,
    NumberField.TateGlobal.ideleNorm_idelesBaseChange]
  have hℓ : (Module.finrank K L) ≠ 0 := Module.finrank_pos.ne'
  have hy : 0 < NumberField.TateGlobal.ideleNorm K y := NumberField.TateGlobal.ideleNorm_pos y
  have hA : 0 ≤ c⁻¹ * Real.exp R := mul_nonneg (inv_nonneg.mpr hc.le) (Real.exp_pos R).le
  have hprod : c⁻¹ ^ ((Module.finrank K L : ℝ)⁻¹) * Real.exp ((Module.finrank K L : ℝ)⁻¹ * R) =
      (c⁻¹ * Real.exp R) ^ ((Module.finrank K L : ℝ)⁻¹) := by
    rw [mul_comm ((Module.finrank K L : ℝ)⁻¹) R, Real.exp_mul,
      Real.mul_rpow (inv_nonneg.mpr hc.le) (Real.exp_pos R).le]
  rw [hprod]
  constructor
  · intro h
    have h1 : c⁻¹ * Real.exp R < NumberField.TateGlobal.ideleNorm K y ^ Module.finrank K L := by
      rw [inv_mul_lt_iff₀ hc]; exact h
    calc (c⁻¹ * Real.exp R) ^ ((Module.finrank K L : ℝ)⁻¹)
        < (NumberField.TateGlobal.ideleNorm K y ^ Module.finrank K L) ^ ((Module.finrank K L : ℝ)⁻¹) :=
          Real.rpow_lt_rpow hA h1 (by positivity)
      _ = NumberField.TateGlobal.ideleNorm K y := Real.pow_rpow_inv_natCast hy.le hℓ
  · intro h
    have h1 : ((c⁻¹ * Real.exp R) ^ ((Module.finrank K L : ℝ)⁻¹)) ^ Module.finrank K L <
        NumberField.TateGlobal.ideleNorm K y ^ Module.finrank K L :=
      pow_lt_pow_left₀ h (Real.rpow_nonneg hA _) hℓ
    rw [Real.rpow_inv_natCast_pow hA hℓ, inv_mul_lt_iff₀ hc] at h1
    exact h1

theorem setIntegral_eq_inv_mul_loc {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (d : ℝ≥0∞)
    (hd0 : d ≠ 0) (hdT : d ≠ ⊤) (hd : ∀ s : Set α, ν s = d * μ s) (s : Set α) (F : α → ℂ) :
    ∫ x in s, F x ∂μ = ((d.toReal⁻¹ : ℝ) : ℂ) * ∫ x in s, F x ∂ν := by
  have hν : ν = d • μ := Measure.ext fun t _ => by rw [hd t, Measure.smul_apply, smul_eq_mul]
  have h1 : ∫ x in s, F x ∂ν = ((d.toReal : ℝ) : ℂ) * ∫ x in s, F x ∂μ := by
    rw [hν, Measure.restrict_smul, integral_smul_measure, Complex.real_smul]
  have hd' : (d.toReal : ℂ) ≠ 0 := by exact_mod_cast (ENNReal.toReal_pos hd0 hdT).ne'
  rw [h1, ← mul_assoc]
  push_cast
  rw [inv_mul_cancel₀ hd', one_mul]

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure] (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νK : Measure (AdeleRing (𝓞 K) K)ˣ) [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)) [∀ v, (μf v).IsAddHaarMeasure]
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L))
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
            ∃ (n : ℕ) (κw : Fin n → ℂ) (a : Fin n → ℝ) (b : ℝ) (Sx : Finset (HeightOneSpectrum (𝓞 K)))
        (g : Fin n → InfiniteAdeleRing K → ℂ)
        (h₀ : Fin n → (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ),
        (∀ j, 0 < a j) ∧ b ≠ 0 ∧ S ∪ T ⊆ Sx ∧
      (∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (j : Fin n),
        ((fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) ∈ NumberField.AdelicFourier.schwartzBruhat K ∧
          HasCompactSupport (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x))) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∀ R : ℝ,
      ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            ‖Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)‖ₑ
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤ →
      ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * g))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * g)‖ₑ ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤ →
      (∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) =
        ∑ j : Fin n, κw j * ∫ y in ΩK,
          ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
            ((∑ᶠ η : Kˣ, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x)
                (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
              (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
                ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK else 0)) ∂νK := by
  intro T hT ws w' hw' ϖs hϖ hϖs0 ns rTs hrT zs hzs
  classical

  have hmK : ‹MeasurableSpace (AdeleRing (𝓞 K) K)› = NumberField.AdelicHaar.adeleBorel (𝓞 K) K :=
    BorelSpace.measurable_eq
  subst hmK
  have hmKu : ‹MeasurableSpace (AdeleRing (𝓞 K) K)ˣ› = NumberField.Idele.ideleBorel K :=
    BorelSpace.measurable_eq
  subst hmKu
  letI iK : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  letI iKu : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.ideleBorel K
  letI iLa : MeasurableSpace (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.adeleBorel (𝓞 L) L
  haveI iLab : BorelSpace (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 L) L
  haveI iLah : (adelicAddHaar (𝓞 L) L).IsAddHaarMeasure := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 L) L

  obtain ⟨Sτ, n, c, τ, τfin, τarch, πs, cτ, hSτ, hcτ0, hcτT, hcpos, hlev, hτfin, hmeas, hmul, hτ0, hτ2, hgood,
    hgood', hbad, hlevels, harch, hfac3⟩ := TwistedUnipotentTerm.exists_transversal K L SL hSL S T
  obtain ⟨ctr, hctr0, hctrT, hctr, -⟩ :=
    TraceFibrePushforward.exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre K L μK (adelicAddHaar (𝓞 L) L)
  obtain ⟨d, hd0, hdT, hd⟩ := NumberField.Idele.exists_forall_measure_eq_mul_idelicHaar K νK
  obtain ⟨Ω₂K, hΩ₂Km, hΩ₂K⟩ := AutomorphicForm.TransversalMeasure.exists_measurableSet_isFundamentalDomain_idelesBaseChange_principal K L
  obtain ⟨Sx, g, h₀, hSx, hSB, hD⟩ := AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram K L νZL D σ hgen SL ξL hSL hξc hξt S φa φS μK hξσ T hT ws ns rTs zs
    Sτ hSτ n c τ τfin τarch πs hcpos hlev hτfin hτ0 hgood hgood' hbad harch hfac3
  refine ⟨n, fun j => (((NumberField.Idele.idelicHaar L
      (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β})).toReal * ctr.toReal *
        (cτ.toReal * (c j)⁻¹) * d.toReal⁻¹ : ℝ) : ℂ),
    fun j => (c j)⁻¹ ^ ((Module.finrank K L : ℝ)⁻¹), (Module.finrank K L : ℝ)⁻¹, Sx, g, h₀,
    ?_, ?_, hSx, hSB, ?_⟩
  · intro j; exact Real.rpow_pos_of_pos (inv_pos.mpr (hcpos j)) _
  · haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
    exact inv_ne_zero (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
  intro ks js φ φf hfac R hFIN hREF
  obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
    ⟨φa, φf, hfac.1, hfac.2.1, hfac.2.2.2.2.2⟩
  have eA := AutomorphicForm.TwistedBruhat.integral_iwasawa_indicator_cuspKernel_sub_cuspTruncation_eq_measure_mul_integral_of_sigmaInvariant_ed2
    K L α β hα hαβ.le νZL ΩL hΩL D σ hgen ξL hξc hξt hξσ φ hφc hφs R X Ω₁ Ω₂ hΩ₁ hFIN
  rw [eA]
  by_cases hV0 : NumberField.Idele.idelicHaar L
      (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) = 0
  · beta_reduce
    rw [hV0]
    simp
  have eApp := AutomorphicForm.TwistedBruhat.lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
    K L α β hα hαβ.le νZL ΩL hΩL D σ hgen ξL hξc hξt hξσ φ hφc hφs R X Ω₁ Ω₂ hΩ₁
  obtain ⟨finJ, eB⟩ := AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub
    K L νZL ΩL hΩL D σ hgen ξL hξc hξt φ hφc hφs R X Ω₂ Ω₂K hX hΩ₂ hΩ₂Km hΩ₂K μK hμK1 ctr hctr0 hctrT hctr (by
      intro h3
      apply hREF
      rw [eApp, h3]
      exact ENNReal.mul_top hV0)
  rw [eB]
  have hsupp := AutomorphicForm.TwistedBruhat.apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram
    K L D σ hgen SL hSL S φa φS T hT ws ns rTs zs ks js φ φf hfac Sτ hSτ
  have hDbc : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) =
        AutomorphicForm.TransversalMeasure.idelesBaseChange K L y := fun y => M4aHerbrand.IdeleGaloisDescent.unitsAct_idelesBaseChange K L D σ y
  have habs : NumberField.Idele.idelicHaar K ≪ νK :=
    Measure.AbsolutelyContinuous.mk fun s _ h0 => (mul_eq_zero.mp ((hd s).symm.trans h0)).resolve_left hd0
  have hΩK' := hΩK.mono habs
  obtain ⟨-, eC⟩ := AutomorphicForm.TwistedBruhat.integrableOn_and_integral_finsum_tracePushforward_sub_eq_sum_mul_setIntegral_rankOne_of_transversal
    K L νZL D σ ξL hξc φ hφc hφs R Ω₂K hΩ₂Km hΩ₂K μK Sτ n c τ cτ hcτ0 hcτT hcpos hlev hτfin hmeas hmul hτ0 hτ2 ΩK hΩK'
    (fun j => (c j)⁻¹ ^ ((Module.finrank K L : ℝ)⁻¹)) ((Module.finrank K L : ℝ)⁻¹)
    (fun j t ht y => thresh_loc K L (c j) R (hcpos j) t ht y) hDbc hsupp finJ
  rw [eC, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  beta_reduce
  have eD := fun y θ => (hD ks js φ φf hfac j y θ).2
  simp only [eD]
  rw [setIntegral_eq_inv_mul_loc (NumberField.Idele.idelicHaar K) νK d hd0 hdT hd ΩK]
  push_cast
  ring

end S_AutomorphicForm_exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2 (solution)
