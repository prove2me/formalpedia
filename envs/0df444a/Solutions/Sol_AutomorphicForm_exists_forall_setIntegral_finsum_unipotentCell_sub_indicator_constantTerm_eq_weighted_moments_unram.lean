-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/62150f02-55cf-5845-b6ef-13a7776b0a15

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

import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram
import Theorems.Thm_TwistedUnipotentTerm_exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram
import Theorems.Thm_TwistedUnipotentTerm_twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram
import Theorems.Thm_TwistedUnipotentTerm_exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram
import Theorems.Thm_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul
import Theorems.Thm_AutomorphicForm_apply_det_heckeGen_eq_of_asIdeal_eq_smul_of_sigmaInvariant_unram
import Theorems.Thm_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem ALG_1a17 {ι : Type} [Fintype ι] [DecidableEq ι] (Λ' κ' c' R : ℂ) (Z Zd A B u e₁ e₂ : ι → ℂ)
    (hu : ∀ i, u i ≠ 0) (hZ : ∀ i, Z i = u i * A i) (hZd : ∀ i, Zd i = e₁ i * B i + e₂ i * A i) :
    Λ' * (R * ∏ i, Z i + c' * ∑ p, Zd p * ∏ i ∈ Finset.univ.erase p, Z i) + κ' * ∏ i, Z i =
      (Λ' * ∏ i, u i) * (R * ∏ i, A i +
          ∑ p, (c' * e₁ p / u p * B p + c' * e₂ p / u p * A p) * ∏ i ∈ Finset.univ.erase p, A i) +
        (κ' * ∏ i, u i) * ∏ i, A i := by
  have key : ∀ p : ι, (∏ i ∈ Finset.univ.erase p, u i) * u p = ∏ i, u i := fun p =>
    Finset.prod_erase_mul (Finset.univ) u (Finset.mem_univ p)
  simp_rw [hZ, hZd, Finset.prod_mul_distrib]
  have hsum : c' * ∑ p, (e₁ p * B p + e₂ p * A p) * ((∏ i ∈ Finset.univ.erase p, u i) * ∏ i ∈ Finset.univ.erase p, A i)
      = (∏ i, u i) * ∑ p, (c' * e₁ p / u p * B p + c' * e₂ p / u p * A p) * ∏ i ∈ Finset.univ.erase p, A i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← key p]
    field_simp [hu p]
  rw [hsum]
  ring

open AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem
    solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
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
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
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
      ∃ Λ κ₀ : ℂ, ∃ c₁ c₂ : HeightOneSpectrum (𝓞 K) → ℂ,
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
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        Λ * ((R : ℂ) *
            ∏ i : T,
              ((1 + (-1 : ℂ) ^ ks i) / 2 * (4 * (HeckeEigensystem.cNorm (w' i) *
                  ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks i / 2) *
                ((∏ n ∈ Finset.range (ks i / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js i) +
            ∑ p : T,
              (c₁ p *
                  ((1 + (-1 : ℂ) ^ ks p) * (4 * (HeckeEigensystem.cNorm (w' p) *
                      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks p / 2) *
                    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js p) +
                  c₂ p *
                  ((1 + (-1 : ℂ) ^ ks p) / 2 * (4 * (HeckeEigensystem.cNorm (w' p) *
                      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks p / 2) *
                    ((∏ n ∈ Finset.range (ks p / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js p)) *
                ∏ i ∈ Finset.univ.erase p,
                  ((1 + (-1 : ℂ) ^ ks i) / 2 * (4 * (HeckeEigensystem.cNorm (w' i) *
                      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks i / 2) *
                    ((∏ n ∈ Finset.range (ks i / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js i)) +
          κ₀ * ∏ i : T,
            ((1 + (-1 : ℂ) ^ ks i) / 2 * (4 * (HeckeEigensystem.cNorm (w' i) *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks i / 2) *
              ((∏ n ∈ Finset.range (ks i / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js i) := by
  intro T hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hrT zs hzs
  classical

  letI mK : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K) := fun v => borel _
  haveI bK : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K) := fun v => ⟨rfl⟩
  let μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K) := fun v => Measure.addHaar
  haveI hμf : ∀ v : HeightOneSpectrum (𝓞 K), (μf v).IsAddHaarMeasure := fun v => by
    show (Measure.addHaar : Measure (v.adicCompletion K)).IsAddHaarMeasure
    infer_instance

  have hunr : ∀ v ∈ T, ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1 := by
    intro v hv w₂ hw₂
    by_contra h
    exact hTSL v hv w₂ hw₂ (hSL w₂ h)

  obtain ⟨Λ', κ', c', hC1⟩ := AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen SL ξL hSL hξc hξt S φa φS
    c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ μf T hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hrT zs hzs
  by_cases hσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩
  swap
  ·
    refine ⟨0, 0, fun _ => 0, fun _ => 0, ?_⟩
    intro ks js φ φf hfac
    obtain ⟨R₁, hR₁⟩ := hC1 ks js φ φf hfac
    obtain ⟨R₂, hR₂⟩ := AutomorphicForm.setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen SL ξL hSL hξc hξt S φa φS
      c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ T hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hrT zs hzs hσ ks js φ φf hfac
    refine ⟨max R₁ R₂, fun R hR => ?_⟩
    obtain ⟨ha, hb, -⟩ := hR₁ R ((le_max_left _ _).trans hR)
    refine ⟨ha, hb, ?_⟩
    rw [hR₂ R ((le_max_right _ _).trans hR)]
    ring
  by_cases hP : ∀ v ∈ T, ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1
  swap
  ·
    push_neg at hP
    obtain ⟨v₀, hv₀, ζ, hζ, hne⟩ := hP
    have h0 : ∀ k j : ℕ, twistedLocalFactor K L D σ ξL v₀ (ws v₀) (ns v₀) (rTs v₀) (zs v₀) k j = 0 :=
      TwistedUnipotentTerm.twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram K L D σ ξL hξc v₀ (ws v₀) (hunr v₀ hv₀) ⟨ζ, hζ, hne⟩
        (ϖs v₀) (hϖ v₀ hv₀) (hϖs0 v₀ hv₀) (ns v₀) (rTs v₀) (hrT v₀ hv₀) (zs v₀) (hzs v₀ hv₀) (μf v₀)
    refine ⟨0, 0, fun _ => 0, fun _ => 0, ?_⟩
    intro ks js φ φf hfac
    obtain ⟨R₁, hR₁⟩ := hC1 ks js φ φf hfac
    refine ⟨R₁, fun R hR => ?_⟩
    obtain ⟨ha, hb, hc'⟩ := hR₁ R hR
    refine ⟨ha, hb, ?_⟩
    rw [hc']
    have hZ0 : LanglandsTunnell.TateLocal.localZeta (μf v₀) (twistedLocalFactor K L D σ ξL v₀ (ws v₀) (ns v₀) (rTs v₀) (zs v₀) (ks v₀) (js v₀)) 1 1 = 0 := by
      rw [h0]; exact LanglandsTunnell.TateLocal.localZeta_zero_fun _ _ _
    have hprod : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (⟨v₀, hv₀⟩ : T)) hZ0
    have hsum : ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (ks p) (js p)) 1 s) 1 *
        ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : p = ⟨v₀, hv₀⟩
      · subst hp
        have hfun : (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v₀) (twistedLocalFactor K L D σ ξL v₀ (ws v₀) (ns v₀) (rTs v₀) (zs v₀) (ks v₀) (js v₀)) 1 s) = fun _ => (0 : ℂ) := by
          funext s; rw [h0]; exact LanglandsTunnell.TateLocal.localZeta_zero_fun _ _ _
        rw [show (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K))) (twistedLocalFactor K L D σ ξL ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K)) (ws ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K))) (ns ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K))) (rTs ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K))) (zs ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K))) (ks ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K))) (js ((⟨v₀, hv₀⟩ : T) : HeightOneSpectrum (𝓞 K)))) 1 s) = fun _ => (0 : ℂ) from hfun]
        simp
      · refine mul_eq_zero_of_right _ ?_
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hp h.symm, Finset.mem_univ _⟩) hZ0
    rw [hprod, hsum]
    ring

  have hval : ∀ v ∈ T, ∃ uu : ℂ, uu ≠ 0 ∧ ∀ k j : ℕ, LanglandsTunnell.TateLocal.localZeta (μf v) (twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) k j) 1 1 =
      uu * ((1 + (-1 : ℂ) ^ k) / 2 * (4 * (AutomorphicForm.HeckeEigensystem.cNorm (ws v).1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) *
            ((∏ n ∈ Finset.range (k / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) := fun v hv =>
    TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram K L D σ ξL hξc v (ws v) (hunr v hv) (hP v hv)
      (ϖs v) (hϖ v hv) (hϖs0 v hv) (ns v) (rTs v) (hrT v hv) (zs v) (hzs v hv) (μf v)
  choose! uf huf0 huf using hval
  have hder : ∀ v ∈ T, ∃ e₁ e₂ : ℂ, ∀ k j : ℕ, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) k j) 1 s) 1 =
      e₁ * ((1 + (-1 : ℂ) ^ k) * (4 * (AutomorphicForm.HeckeEigensystem.cNorm (ws v).1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) +
      e₂ * ((1 + (-1 : ℂ) ^ k) / 2 * (4 * (AutomorphicForm.HeckeEigensystem.cNorm (ws v).1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) *
            ((∏ n ∈ Finset.range (k / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) := fun v hv =>
    TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram K L D σ ξL hξc v (ws v) (hunr v hv) (hP v hv)
      (ϖs v) (hϖ v hv) (hϖs0 v hv) (ns v) (rTs v) (hrT v hv) (zs v) (hzs v hv) (μf v)
  choose! e₁f e₂f hef using hder
  have htr : ∀ i : T, ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws i).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := fun i =>
    AutomorphicForm.apply_det_heckeGen_eq_of_asIdeal_eq_smul_of_sigmaInvariant_unram K L D σ ξL hσ i (ws i) (hunr i i.2) (w' i) (hw' i i.2) (hP i i.2)
  have hN : ∀ i : T, AutomorphicForm.HeckeEigensystem.cNorm (w' i) = AutomorphicForm.HeckeEigensystem.cNorm (ws i).1 :=
    fun i => AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul K L σ (ws i).1 (w' i) (hw' i i.2)
  refine ⟨Λ' * ∏ i : T, uf i, κ' * ∏ i : T, uf i, fun p => c' * e₁f p / uf p, fun p => c' * e₂f p / uf p, ?_⟩
  intro ks js φ φf hfac
  obtain ⟨R₁, hR₁⟩ := hC1 ks js φ φf hfac
  refine ⟨R₁, fun R hR => ?_⟩
  obtain ⟨ha, hb, hc'⟩ := hR₁ R hR
  refine ⟨ha, hb, ?_⟩
  rw [hc']
  simp_rw [htr, hN]
  exact ALG_1a17 (ι := T) Λ' κ' c' (R : ℂ)
    (fun i : T => LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1)
    (fun p : T => deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (ks p) (js p)) 1 s) 1)
    (fun i : T => ((1 + (-1 : ℂ) ^ (ks i)) / 2 * (4 * (AutomorphicForm.HeckeEigensystem.cNorm (ws i).1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws i).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((ks i) / 2) *
            ((∏ n ∈ Finset.range ((ks i) / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws i).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (js i)))
    (fun i : T => ((1 + (-1 : ℂ) ^ (ks i)) * (4 * (AutomorphicForm.HeckeEigensystem.cNorm (ws i).1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws i).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((ks i) / 2) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws i).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (js i)))
    (fun i : T => uf i) (fun i : T => e₁f i) (fun i : T => e₂f i)
    (fun i => huf0 i i.2) (fun i => huf i i.2 (ks i) (js i)) (fun i => hef i i.2 (ks i) (js i))

end S_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram (solution)
