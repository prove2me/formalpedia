-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/66f9f080-c466-5e16-9e78-946c4fbd1e2d

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

import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram
import Theorems.Thm_TwistedUnipotentTerm_exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
import Theorems.Thm_NumberField_TateGlobal_exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator
import Theorems.Thm_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top
import Theorems.Thm_TwistedUnipotentTerm_differentiableOn_localZeta_twistedLocalFactor_one_unram
import Theorems.Thm_TwistedUnipotentTerm_exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram
import Theorems.Thm_TwistedUnipotentTerm_twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

/-!                                                                                               -/

theorem ALG2_1a17 {n : ℕ} (κw m la c₀ : Fin n → ℂ) (V b c₁ R P P₀ D : ℂ) (hbV : b * V ≠ 0) :
    ∑ j, κw j * (V * (m j * P) * (la j + b * R) + (c₀ j * P + c₁ * (m j * P₀) * D)) =
      (b * V * ∑ j, κw j * m j) * (R * P + (c₁ * P₀ / (b * V)) * D) +
        (∑ j, κw j * (V * m j * la j + c₀ j)) * P := by
  have : ∀ j, κw j * (V * (m j * P) * (la j + b * R) + (c₀ j * P + c₁ * (m j * P₀) * D)) =
      (b * V * R * P + c₁ * P₀ * D) * (κw j * m j) + P * (κw j * (V * m j * la j + c₀ j)) := fun j => by ring
  obtain ⟨hb, hV⟩ := mul_ne_zero_iff.mp hbV
  simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp

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
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)) [∀ v, (μf v).IsAddHaarMeasure] :
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
      ∃ Λ κ₀ c : ℂ,
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
        Λ * ((R : ℂ) * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i)
                (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 +
            c * ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p)
                (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (ks p) (js p)) 1 s) 1 *
                ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i)
                (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1) +
          κ₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i)
                (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 := by
  intro T hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hrT zs hzs
  classical

  letI mAK : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI bAK : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  letI mIK : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := borel _
  haveI bIK : BorelSpace (AdeleRing (𝓞 K) K)ˣ := ⟨rfl⟩
  obtain ⟨μK, hμKH, hμK1⟩ := NumberField.AdelicBox.exists_isAddHaarMeasure_adelicBox_eq_one K
  haveI := hμKH
  obtain ⟨νK, ΩK, hνKH, hΩK, hV0, hVtop⟩ := NumberField.TateGlobal.exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top K
  haveI := hνKH
  have hTT : T ⊆ S ∪ T := Finset.subset_union_right

  have hunr : ∀ v ∈ T, ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1 := by
    intro v hv w₂ hw₂
    by_contra h
    exact hTSL v hv w₂ hw₂ (hSL w₂ h)

  obtain ⟨n, κw, a, b, Sx, g, h₀, ha, hb, hSx, hSB, hmain⟩ :=
    AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram
      K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen SL ξL hSL hξc hξt S φa φS c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀
      μK hμK1 νK ΩK hΩK μf T hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hrT zs hzs
  have hTSx : T ⊆ Sx := fun v hv => hSx (Finset.mem_union_right _ hv)
  by_cases hP : ∀ v ∈ T, ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1
  swap
  ·
    push_neg at hP
    obtain ⟨v₀, hv₀, ζ, hζ, hne⟩ := hP
    have h0 : ∀ k j : ℕ, twistedLocalFactor K L D σ ξL v₀ (ws v₀) (ns v₀) (rTs v₀) (zs v₀) k j = 0 :=
      TwistedUnipotentTerm.twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram K L D σ ξL hξc v₀ (ws v₀) (hunr v₀ hv₀) ⟨ζ, hζ, hne⟩
        (ϖs v₀) (hϖ v₀ hv₀) (hϖs0 v₀ hv₀) (ns v₀) (rTs v₀) (hrT v₀ hv₀) (zs v₀) (hzs v₀ hv₀) (μf v₀)
    refine ⟨0, 0, 0, ?_⟩
    intro ks js φ φf hfac
    obtain ⟨R₁, hR₁⟩ := hmain ks js φ φf hfac
    refine ⟨R₁, fun R hR => ?_⟩
    obtain ⟨hA, hB, hC⟩ := hR₁ R hR
    refine ⟨hA, hB, ?_⟩
    rw [hC]
    have hΨ0 : ∀ j : Fin n, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) ((ks, js).1 v) ((ks, js).2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) = fun _ => 0 := by
      intro j; funext x
      have hprod : ∏ v ∈ Sx, (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) ((ks, js).1 v) ((ks, js).2 v) else h₀ j v)
          ((x.2 : FiniteAdeleRing (𝓞 K) K) v) = 0 := by
        apply Finset.prod_eq_zero (hTSx hv₀)
        rw [if_pos hv₀, h0]; rfl
      simp only [Set.indicator_apply, hprod, mul_zero, ite_self]
    have hZ0 : LanglandsTunnell.TateLocal.localZeta (μf v₀) (twistedLocalFactor K L D σ ξL v₀ (ws v₀) (ns v₀) (rTs v₀) (zs v₀) (ks v₀) (js v₀)) 1 1 = 0 := by
      rw [h0]; exact LanglandsTunnell.TateLocal.localZeta_zero_fun _ _ _
    have hprodZ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (⟨v₀, hv₀⟩ : T)) hZ0
    have hsumZ : ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (ks p) (js p)) 1 s) 1 *
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
    rw [hprodZ, hsumZ]

    have hΨ0' : ∀ j : Fin n, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) = fun _ => 0 := fun j => hΨ0 j
    simp only [hΨ0']
    simp

  have hval : ∀ v ∈ T, ∃ uu : ℂ, uu ≠ 0 ∧ ∀ k j : ℕ, LanglandsTunnell.TateLocal.localZeta (μf v) (twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) k j) 1 1 =
      uu * ((1 + (-1 : ℂ) ^ k) / 2 * (4 * (AutomorphicForm.HeckeEigensystem.cNorm (ws v).1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) *
            ((∏ n ∈ Finset.range (k / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) := fun v hv =>
    TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram K L D σ ξL hξc v (ws v) (hunr v hv) (hP v hv)
      (ϖs v) (hϖ v hv) (hϖs0 v hv) (ns v) (rTs v) (hrT v hv) (zs v) (hzs v hv) (μf v)
  have hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) 0 0) 1 1 ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    obtain ⟨uu, huu, hZ⟩ := hval i i.2
    rw [hZ 0 0]
    refine mul_ne_zero huu ?_
    norm_num
  have hloc : ∀ θ : (HeightOneSpectrum (𝓞 K) → ℕ) × (HeightOneSpectrum (𝓞 K) → ℕ), ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v)) 1 s) {s : ℂ | 0 < s.re} := fun θ v hv =>
    TwistedUnipotentTerm.differentiableOn_localZeta_twistedLocalFactor_one_unram K L D σ ξL hξc v (ws v) (hunr v hv)
      (ϖs v) (hϖ v hv) (hϖs0 v hv) (ns v) (rTs v) (hrT v hv) (zs v) (hzs v hv) (μf v) (θ.1 v) (θ.2 v)

  obtain ⟨c₁, hc₁⟩ := TwistedUnipotentTerm.exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
    K μK hμK1 νK ΩK hΩK Sx μf T hTSx ((HeightOneSpectrum (𝓞 K) → ℕ) × (HeightOneSpectrum (𝓞 K) → ℕ))
    (fun θ v => twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v)) hloc
    ((fun _ => 0), (fun _ => 0)) hθ₀

  have hTate : ∀ j : Fin n, ∃ c₀ : ℂ, ∀ θ : (HeightOneSpectrum (𝓞 K) → ℕ) × (HeightOneSpectrum (𝓞 K) → ℕ), ∀ X : ℝ, 0 < X →
      IntegrableOn (fun y : (AdeleRing (𝓞 K) K)ˣ =>
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Kˣ, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
              AdeleRing (𝓞 K) K))) -
            (if X < NumberField.TateGlobal.ideleNorm K y then
              ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK else 0))) ΩK νK ∧
      (∫ y in ΩK,
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Kˣ, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
              AdeleRing (𝓞 K) K))) -
            (if X < NumberField.TateGlobal.ideleNorm K y then
              ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK else 0)) ∂νK) =
        ((νK (ΩK ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm K y ∧ NumberField.TateGlobal.ideleNorm K y ≤ Real.exp 1})).toReal : ℂ) *
          (∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK) * (Real.log X : ℂ) +
        (c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (θ.1 i) (θ.2 i)) 1 1 +
          c₁ * (∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (((fun _ => 0 : HeightOneSpectrum (𝓞 K) → ℕ), (fun _ => 0 : HeightOneSpectrum (𝓞 K) → ℕ)).1 v) (((fun _ => 0 : HeightOneSpectrum (𝓞 K) → ℕ), (fun _ => 0 : HeightOneSpectrum (𝓞 K) → ℕ)).2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK) *
            ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (θ.1 p) (θ.2 p)) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (θ.1 i) (θ.2 i)) 1 1) :=
    fun j => hc₁ (g j) (h₀ j) (fun θ => (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x)) (fun θ x => rfl) (fun θ => (hSB θ.1 θ.2 j).1) (fun θ => (hSB θ.1 θ.2 j).2)
  choose c₀f hc₀f using hTate
  have hMass : ∀ j : Fin n, ∃ m : ℂ, ∀ θ : (HeightOneSpectrum (𝓞 K) → ℕ) × (HeightOneSpectrum (𝓞 K) → ℕ),
      ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK = m * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (θ.1 i) (θ.2 i)) 1 1 :=
    fun j => NumberField.TateGlobal.exists_forall_integral_eq_mul_prod_localZeta_of_eq_indicator K μK Sx μf T hTSx (g j) (h₀ j) ((HeightOneSpectrum (𝓞 K) → ℕ) × (HeightOneSpectrum (𝓞 K) → ℕ))
      (fun θ v => twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v))
      (fun θ => (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (θ.1 v) (θ.2 v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x)) (fun θ x => rfl) (fun θ => (hSB θ.1 θ.2 j).1)
  choose mf hmf using hMass

  set V : ℂ := ((νK (ΩK ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm K y ∧ NumberField.TateGlobal.ideleNorm K y ≤ Real.exp 1})).toReal : ℂ) with hVdef
  have hV : V ≠ 0 := by
    rw [hVdef]; exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hV0, hVtop⟩)
  have hbV : (b : ℂ) * V ≠ 0 := mul_ne_zero (by exact_mod_cast hb) hV
  set P₀ : ℂ := ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) 0 0) 1 1 with hP₀def
  refine ⟨(b : ℂ) * V * ∑ j, κw j * mf j, ∑ j, κw j * (V * mf j * (Real.log (a j) : ℂ) + c₀f j), c₁ * P₀ / ((b : ℂ) * V), ?_⟩
  intro ks js φ φf hfac
  obtain ⟨R₁, hR₁⟩ := hmain ks js φ φf hfac
  refine ⟨R₁, fun R hR => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hR₁ R hR
  refine ⟨hA, hB, ?_⟩
  rw [hC]

  have hX : ∀ j, 0 < a j * Real.exp (b * R) := fun j => mul_pos (ha j) (Real.exp_pos _)
  have hlog : ∀ j, (Real.log (a j * Real.exp (b * R)) : ℂ) = (Real.log (a j) : ℂ) + (b : ℂ) * (R : ℂ) := by
    intro j; rw [Real.log_mul (ha j).ne' (Real.exp_pos _).ne', Real.log_exp]; push_cast; ring
  have hpiece : ∀ j : Fin n, (∫ y in ΩK,
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Kˣ, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
              AdeleRing (𝓞 K) K))) -
            (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
              ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK else 0)) ∂νK) =
      V * (mf j * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1) * ((Real.log (a j) : ℂ) + (b : ℂ) * (R : ℂ)) +
        (c₀f j * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 + c₁ * (mf j * P₀) *
          ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (ks p) (js p)) 1 s) 1 *
            ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1) := by
    intro j
    have h := (hc₀f j (ks, js) _ (hX j)).2
    have hm := hmf j (ks, js)
    have hm0 := hmf j ((fun _ => 0), (fun _ => 0))
    dsimp only at h hm hm0
    rw [hm0, hlog j] at h
    conv at h => rhs; rw [hm]
    exact h
  rw [Finset.sum_congr rfl fun j _ => by rw [hpiece j]]
  exact ALG2_1a17 κw mf (fun j => (Real.log (a j) : ℂ)) c₀f V (b : ℂ) c₁ (R : ℂ)
    (∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1) P₀
    (∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (ks p) (js p)) 1 s) 1 *
      ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1) hbV

end S_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram (solution)
