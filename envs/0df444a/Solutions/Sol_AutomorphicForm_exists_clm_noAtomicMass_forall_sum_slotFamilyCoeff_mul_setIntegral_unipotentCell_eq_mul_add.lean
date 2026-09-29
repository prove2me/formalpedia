-- Prove2me | solution 1 for AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/13985c5b-c702-56bc-8577-fc9830599fae

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
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self
import Theorems.Thm_AutomorphicForm_setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one
import Theorems.Thm_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
import Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
import Theorems.Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
import Theorems.Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
import Theorems.Thm_AutomorphicForm_exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsLocalTestFn localIntegralSet IsBiInvariantUnder IsArchTestFactor IsFinTestFactor ArchTypeFamily IsArchBiFinite productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 constantTerm HeckeEigensystem.cNorm HeckeEigensystem highSet adelicKernelUnipotentPart SatakeCombination.slotDeg SatakeCombination.slotIndex SatakeCombination.slotFamilyCoeff canonicalTruncationDomain exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass"
p2m_open "AutomorphicForm"

section CylSmall

variable {K L : Type} [Field K] [Field L]
  (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (T : Finset (HeightOneSpectrum (𝓞 K)))
  (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))

def CylSmall (Δ : C(X, ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
    ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(X, ℂ),
        (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
        (∀ y, ‖g y‖ ≤ 1) → ‖Δ g‖ < ε

theorem cylSmall_zero : CylSmall X T w' 0 := by
  intro τ ε hε
  refine ⟨fun _ => Set.univ, fun v _ => ⟨isOpen_univ, Set.mem_univ _⟩, fun g _ _ => ?_⟩
  simpa using hε

theorem cylSmall_add {Δ₁ Δ₂ : C(X, ℂ) →L[ℂ] ℂ} (h₁ : CylSmall X T w' Δ₁) (h₂ : CylSmall X T w' Δ₂) :
    CylSmall X T w' (Δ₁ + Δ₂) := by
  intro τ ε hε
  obtain ⟨U₁, hU₁, hg₁⟩ := h₁ τ (ε / 2) (by positivity)
  obtain ⟨U₂, hU₂, hg₂⟩ := h₂ τ (ε / 2) (by positivity)
  refine ⟨fun v => U₁ v ∩ U₂ v, fun v hv => ⟨(hU₁ v hv).1.inter (hU₂ v hv).1, (hU₁ v hv).2, (hU₂ v hv).2⟩,
    fun g hg0 hg1 => ?_⟩
  have e₁ := hg₁ g (fun y ⟨v, hv, hy⟩ => hg0 y ⟨v, hv, fun hm => hy hm.1⟩) hg1
  have e₂ := hg₂ g (fun y ⟨v, hv, hy⟩ => hg0 y ⟨v, hv, fun hm => hy hm.2⟩) hg1
  calc ‖(Δ₁ + Δ₂) g‖ = ‖Δ₁ g + Δ₂ g‖ := rfl
    _ ≤ ‖Δ₁ g‖ + ‖Δ₂ g‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e₁ e₂
    _ = ε := by ring

theorem cylSmall_smul (a : ℂ) {Δ : C(X, ℂ) →L[ℂ] ℂ} (h : CylSmall X T w' Δ) :
    CylSmall X T w' (a • Δ) := by
  intro τ ε hε
  have hpos : (0 : ℝ) < ‖a‖ + 1 := by positivity
  obtain ⟨U, hU, hg⟩ := h τ (ε / (‖a‖ + 1)) (div_pos hε hpos)
  refine ⟨U, hU, fun g hg0 hg1 => ?_⟩
  have e := hg g hg0 hg1
  calc ‖(a • Δ) g‖ = ‖a‖ * ‖Δ g‖ := by simp
    _ ≤ (‖a‖ + 1) * ‖Δ g‖ := by gcongr; linarith
    _ < (‖a‖ + 1) * (ε / (‖a‖ + 1)) := by gcongr
    _ = ε := by field_simp

theorem cylSmall_sum {ι : Type} (s : Finset ι) (Δ : ι → (C(X, ℂ) →L[ℂ] ℂ))
    (h : ∀ i ∈ s, CylSmall X T w' (Δ i)) : CylSmall X T w' (∑ i ∈ s, Δ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cylSmall_zero X T w'
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact cylSmall_add X T w' (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end CylSmall

open scoped TensorProduct.RightActions in
theorem _root_.P2MW.S_AutomorphicForm_exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add.solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (σ : L ≃ₐ[K] L)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
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
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξKt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξKN : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξK ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∃ ν' μ' : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ' g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ,
        (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)
        ) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
        IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        (R : ℂ) * ν' g + μ' g := by
  intro T hTS hT2 hTSL ws w' hw' ϖKs hϖKs hϖKs0 nKs rKs hrKs zKs hzKs
  classical

  have hwu : ∀ v ∈ T, HeightOneSpectrum.under (𝓞 K) (w' v) = v := by
    intro v hv
    rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, hw' v hv, Ideal.under_smul,
      ← HeightOneSpectrum.under_asIdeal, (ws v).2]
  have hw'S : ∀ v ∈ T, w' v ∉ SL := fun v hv => hTSL v hv (w' v) (hwu v hv)
  have hw'i : ∀ v ∈ T, ∀ v' ∈ T, w' v = w' v' → v = v' := fun v hv v' hv' h => by
    rw [← hwu v hv, ← hwu v' hv', h]

  obtain ⟨Λ, κ₀, c₁, c₂, hKE⟩ :=
    exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self
      K L α β hα hαβ SK faK fSK ΦK hΦKs hΦK νZK ΩK hΩK ξK hξKc hξKt N' hN' tysK T hTS ws ϖKs hϖKs hϖKs0 nKs rKs hrKs zKs hzKs
  by_cases hram : ∃ v ∈ T, ∃ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 ∧
      ξK ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ ≠ 1
  ·
    refine ⟨0, 0, cylSmall_zero X T w', ?_⟩
    intro ks js fam hfam
    obtain ⟨R₀, hR₀⟩ := hKE ks js fam hfam
    refine ⟨R₀, fun R hR => ⟨fun m hm => ⟨(hR₀ R hR m hm).1, (hR₀ R hR m hm).2.1⟩, fun g hg => ?_⟩⟩
    have hvan := setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one
      K L α β hα hαβ SK faK fSK ΦK hΦKs hΦK νZK ΩK hΩK ξK hξKc hξKt N' hN' tysK T hTS ws ϖKs hϖKs hϖKs0 nKs rKs hrKs zKs hzKs hram ks js fam hfam
    rw [Finset.sum_eq_zero]
    · simp
    intro m hm
    rw [mul_eq_zero]; right
    refine setIntegral_eq_zero_of_forall_eq_zero fun x _ => ?_
    exact hvan m hm R x
  ·
    push Not at hram

    have hf : ∀ v ∈ T, v.asIdeal.inertiaDeg' (w' v).asIdeal = SatakeCombination.slotDeg K L ws v := by
      intro v hv
      show _ = v.asIdeal.inertiaDeg' (ws v).1.asIdeal
      rw [hw' v hv]
      exact Ideal.inertiaDeg_map_eq v.asIdeal (ws v).1.asIdeal
        (MulSemiringAction.toAlgEquiv (𝓞 K) (𝓞 L) σ.symm)
    have hNP : ∀ w : HeightOneSpectrum (𝓞 L), Ideal.absNorm w.asIdeal =
        Ideal.absNorm (HeightOneSpectrum.under (𝓞 K) w).asIdeal ^
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal := by
      intro w
      haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := by
        rw [HeightOneSpectrum.under_asIdeal]; exact ⟨rfl⟩
      exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal _
        (HeightOneSpectrum.under (𝓞 K) w).isPrime (HeightOneSpectrum.under (𝓞 K) w).ne_bot
    have hNws : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal =
        Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v := by
      intro v hv
      have h := hNP (ws v).1
      rw [(ws v).2] at h
      exact h
    have hNw' : ∀ v ∈ T, Ideal.absNorm (w' v).asIdeal =
        Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v := by
      intro v hv
      have h := hNP (w' v)
      rw [hwu v hv, hf v hv] at h
      exact h

    have hζ : ∀ v ∈ T, ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ SatakeCombination.slotDeg K L ws v =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
      intro v hv
      rw [← hf v hv]
      exact apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
        K L ξL ξK hξKN v (w' v) (hwu v hv) (hram v hv)

    set σr : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
      (HeckeEigensystem.cNorm v * ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℕ) : ℂ)⁻¹ with hσr
    have hσ : ∀ v ∈ T, σr v ^ 2 = HeckeEigensystem.cNorm v * ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
      intro v _
      simp only [σr]
      exact Complex.cpow_nat_inv_pow _ two_ne_zero
    have hsq : ∀ v ∈ T, ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ)) ≠ 0 := by
      intro v hv
      have hpos : (0 : ℝ) < (Ideal.absNorm (w' v).asIdeal : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (w' v).ne_bot)
      exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
    set s : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
      σr v ^ SatakeCombination.slotDeg K L ws v / ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ)) with hsdef
    have hs : ∀ v ∈ T, ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ)) * s v =
        σr v ^ SatakeCombination.slotDeg K L ws v := by
      intro v hv
      simp only [s]
      rw [mul_div_cancel₀ _ (hsq v hv)]
    have hs2 : ∀ v ∈ T, s v ^ 2 =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
      intro v hv
      have hN : ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ)) ^ 2 =
          (HeckeEigensystem.cNorm v) ^ SatakeCombination.slotDeg K L ws v := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        simp only [HeckeEigensystem.cNorm]
        rw [← Nat.cast_pow, ← hNw' v hv]
        norm_cast
      have h1 : (((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ)) * s v) ^ 2 =
          (HeckeEigensystem.cNorm v * ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ SatakeCombination.slotDeg K L ws v := by
        rw [hs v hv, ← pow_mul, mul_comm, pow_mul, hσ v hv]
      rw [mul_pow, hN, mul_pow] at h1
      have hc : (HeckeEigensystem.cNorm v) ^ SatakeCombination.slotDeg K L ws v ≠ 0 := by
        apply pow_ne_zero
        simp only [HeckeEigensystem.cNorm]
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
      rw [← hζ v hv]
      exact mul_left_cancel₀ hc h1

    have hT1 : 1 ≤ T.card := le_trans (by norm_num) hT2
    obtain ⟨μA, hμA, hμAc⟩ :=
      MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero T.card hT1
    choose μE hμE hμEc using fun p : T =>
      MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
        T.card hT2 (T.equivFin p) (SatakeCombination.slotDeg K L ws p.1)
    obtain ⟨ΔA, hΔAcyl, hΔA⟩ :=
      exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
        K L SL ξL X hXc hX T w' hw'S hw'i s hs2 μA hμA
        (fun n => ∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0)) hμAc
    choose ΔE hΔEcyl hΔE using fun p : T =>
      exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
        K L SL ξL X hXc hX T w' hw'S hw'i s hs2 (μE p) (hμE p)
        (fun n => (∏ i ∈ Finset.univ.erase (T.equivFin p), (if n i = 0 then (1 : ℂ) else 0)) *
          (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws p.1 * (n (T.equivFin p)).natAbs))) (hμEc p)

    refine ⟨Λ • ΔA, Λ • ∑ p : T, c₁ p.1 • ΔE p + (Λ * ∑ p : T, c₂ p.1 + κ₀) • ΔA, ?_, ?_⟩
    · exact cylSmall_add X T w'
        (cylSmall_smul X T w' Λ (cylSmall_sum X T w' _ _ fun p _ => cylSmall_smul X T w' _ (hΔEcyl p)))
        (cylSmall_smul X T w' _ hΔAcyl)
    · intro ks js fam hfam
      obtain ⟨R₀, hR₀⟩ := hKE ks js fam hfam
      refine ⟨R₀, fun R hR => ⟨fun m hm => ⟨(hR₀ R hR m hm).1, (hR₀ R hR m hm).2.1⟩, fun g hg => ?_⟩⟩
      rw [Finset.sum_congr rfl (fun m hm => by rw [(hR₀ R hR m hm).2.2])]
      rw [sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
        K L ws T w' ξK ξL σr s hσ hs hζ hNws ks js Λ κ₀ c₁ c₂ R]
      have hA := hΔA ks js g hg
      have hE := fun p : T => hΔE p ks js g hg
      beta_reduce at hA hE
      rw [← hA, Finset.sum_congr rfl (fun p _ => by rw [← hE p])]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

end AutomorphicForm

end S_AutomorphicForm_exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add
end P2MW
export P2MW.S_AutomorphicForm_exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add (solution)
