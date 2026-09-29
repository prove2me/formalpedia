-- Prove2me | solution 1 for AutomorphicForm.memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2e713f7f-01d1-5420-856c-3b55b3b13355

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace P2mSqsum

theorem memLp_two_of_majorant {m : ℝ → ℝ} (hm : Integrable m) {B : ℝ} (hB : ∀ t, m t ≤ B) (h0 : ∀ t, 0 ≤ m t) :
    MemLp m 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine Integrable.mono' (hm.const_mul B) (hm.aestronglyMeasurable.pow 2) (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (by positivity), pow_two]
  exact mul_le_mul_of_nonneg_right (hB t) (h0 t)

theorem memLp_comp_sub {m : ℝ → ℝ} (hm : MemLp m 2 (volume : Measure ℝ)) (c : ℝ) :
    MemLp (fun s => m (s - c)) 2 (volume : Measure ℝ) :=
  hm.comp_measurePreserving (measurePreserving_sub_right volume c)

theorem memLp_comp_sub' {m : ℝ → ℝ} (hm : MemLp m 2 (volume : Measure ℝ)) (c : ℝ) :
    MemLp (fun s => m (c - s)) 2 (volume : Measure ℝ) := by
  have h := hm.comp_measurePreserving
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).comp (measurePreserving_sub_right volume c))
  have e : (m ∘ Neg.neg ∘ fun x : ℝ => x - c) = fun s => m (c - s) := by
    funext s; simp [neg_sub]
  rw [e] at h
  exact h

section CS

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem integral_mul_conj_self_eq (f : X → ℂ) :
    ∫ x, f x * conj (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have e : (fun x => f x * conj (f x)) = fun x => (((‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e]
  exact integral_ofReal

theorem norm_integral_mul_conj_le (F G : X → ℂ) {M : ℝ} (hM : 0 ≤ M) (hF : ∀ x, ‖F x‖ ≤ M)
    (hG : MemLp G 2 μ) (hG1 : ∫ x, ‖G x‖ ^ 2 ∂μ ≤ 1) :
    ‖∫ x, F x * conj (G x) ∂μ‖ ≤ M := by
  have hGi : Integrable (fun x => ‖G x‖) μ := (hG.integrable one_le_two).norm
  have hG2i : Integrable (fun x => ‖G x‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hG.1).mp hG
  have h1 : ‖∫ x, F x * conj (G x) ∂μ‖ ≤ ∫ x, M * ‖G x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) (hGi.const_mul M)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖F x * conj (G x)‖ ≤ M * ‖G x‖
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hF x) (norm_nonneg _)
  have h2 : ∫ x, ‖G x‖ ∂μ ≤ 1 := by
    have hle : ∀ x, ‖G x‖ ≤ (1 + ‖G x‖ ^ 2) / 2 := fun x => by
      nlinarith [sq_nonneg (‖G x‖ - 1), norm_nonneg (G x)]
    have hint : Integrable (fun x => (1 + ‖G x‖ ^ 2) / 2) μ := ((integrable_const 1).add hG2i).div_const 2
    calc ∫ x, ‖G x‖ ∂μ ≤ ∫ x, (1 + ‖G x‖ ^ 2) / 2 ∂μ := integral_mono hGi hint hle
      _ = (1 + ∫ x, ‖G x‖ ^ 2 ∂μ) / 2 := by
        rw [integral_div, integral_add (integrable_const _) hG2i, integral_const, probReal_univ, one_smul]
      _ ≤ 1 := by linarith
  calc ‖∫ x, F x * conj (G x) ∂μ‖ ≤ ∫ x, M * ‖G x‖ ∂μ := h1
    _ = M * ∫ x, ‖G x‖ ∂μ := integral_const_mul _ _
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM
    _ = M := mul_one _

end CS

end P2mSqsum

open P2mSqsum in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹),
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ (2 : ℕ)) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _instE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE
    _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _instP
    μP νP _hμP _hνP _hμPic _hνPic _hμPc _hμPν rP _hr _hdistP ψf _hψf _hψjc _hψhol _hνPc _hψdec ψ _hψ _hψrep em τ _hem
  classical

  obtain ⟨κ, hκ, hCP⟩ :=
    AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
  obtain ⟨h1, h2⟩ := hCP ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE
    _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP
    μP νP _hμP _hνP _hμPic _hνPic _hμPc _hμPν rP _hr _hdistP ψf _hψf _hψjc _hψhol _hνPc _hψdec ψ _hψ _hψrep em τ _hem

  set Θ : ∀ e : ιE, Fin (nE e) → ℝ → ℂ := fun e j t =>
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
      AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
    with hΘ

  have hzero : ∀ e : ιE, (∀ i : ιP, em i ≠ e) → ∀ j, Θ e j = 0 := by
    intro e he j
    funext t
    exact h1 e he j t

  have hKc : IsCompact (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) := isCompact_adelicMaximalCompact K
  have haxis : ∀ (e : ιE) (j : Fin (nE e)) (s : ℝ), ((s : ℂ) * Complex.I) ∈ OE e j := fun e j s =>
    (_hEE e j).2.2.1 (by simp)

  have hNEc : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ),
      Continuous (fun p : ℝ × adelicMaximalCompact K =>
        NE e j ((((p.1 + c : ℝ)) : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K)) := by
    intro e j c
    have hco := (_hEE e j).2.2.2.2.2.2.2.1
    have hmap : Continuous (fun p : ℝ × adelicMaximalCompact K =>
        (((((p.1 + c : ℝ)) : ℂ) * Complex.I), (p.2 : AdelicGL2 (𝓞 K) K))) :=
      ((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const)).mul continuous_const).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact hco.comp_continuous hmap fun p => ⟨haxis e j _, Set.mem_univ _⟩
  have hNEc1 : ∀ (e : ιE) (j : Fin (nE e)) (s : ℝ),
      Continuous (fun k : adelicMaximalCompact K => NE e j ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) := by
    intro e j s
    have h := (hNEc e j 0).comp (Continuous.prodMk_right (X := ℝ) s)
    first | exact h | simpa [Function.comp_def] using h | (simp [Function.comp_def] at h; exact h) | (simp [Function.comp_def]; exact h) | (simp [Function.comp_def] at h ⊢; exact h)
  have hφc1 : ∀ (e : ιE) (j : Fin (nE e)) (s : ℂ),
      Continuous (fun k : adelicMaximalCompact K => φE e j s (k : AdelicGL2 (𝓞 K) K)) := fun e j s =>
    (_hφEjc e j).comp (continuous_const.prodMk continuous_subtype_val)

  have hφnorm : ∀ (e : ιE) (j : Fin (nE e)) (s : ℂ),
      ∫ k, ‖φE e j s (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
    intro e j s
    have hon := _hφEon e j j
    rw [if_pos rfl] at hon
    have e1 : (fun k : adelicMaximalCompact K => φE e j 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)))
        = fun k : adelicMaximalCompact K => φE e j s (k : AdelicGL2 (𝓞 K) K) * conj (φE e j s (k : AdelicGL2 (𝓞 K) K)) := by
      funext k; rw [_hφEflat e j s k]
    rw [e1, integral_mul_conj_self_eq] at hon
    exact_mod_cast hon

  have hNnorm : ∀ (e : ιE) (j : Fin (nE e)) (s : ℝ),
      ∫ k, ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
        NE e j ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
    intro e j s
    have hu := AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
      K hαm (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
      (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j)
      (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j)
      (OE e j) (EE e j) (NE e j) (_hEE e j) (OE e j) (EE e j) (NE e j) (_hEE e j) s
    dsimp only at hu
    rw [integral_mul_conj_self_eq, integral_mul_conj_self_eq, hφnorm e j] at hu
    exact_mod_cast hu

  have hmemK : ∀ (f : adelicMaximalCompact K → ℂ), Continuous f → MemLp f 2 (maximalCompactHaar K) := by
    intro f hf
    obtain ⟨C, hC⟩ := (isCompact_univ (X := adelicMaximalCompact K)).exists_bound_of_continuousOn hf.continuousOn
    exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

  have hpk : ∀ (i : ιP) (j : Fin (nE (em i))),
      ∃ (m₁ m₂ : ℝ → ℝ), MemLp m₁ 2 (volume : Measure ℝ) ∧ MemLp m₂ 2 (volume : Measure ℝ) ∧
        Continuous (Θ (em i) j) ∧
        ∀ s : ℝ, ‖Θ (em i) j s‖ ≤ κ * (m₁ (s - τ i) + m₂ (τ i - s)) := by
    intro i j

    obtain ⟨m₁, hm₁i, ⟨B₁, hB₁⟩, hm₁⟩ := _hψdec i 0 0 _ hKc
    obtain ⟨m₂, hm₂i, ⟨B₂, hB₂⟩, hm₂⟩ := _hψdec (rP i) 0 0 _ hKc
    have hb₁ : ∀ (t : ℝ) (k : adelicMaximalCompact K), ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ m₁ t := by
      intro t k
      have := hm₁ 0 (by simp) t k k.2
      simpa using this
    have hb₂ : ∀ (t : ℝ) (k : adelicMaximalCompact K), ‖ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)‖ ≤ m₂ (-t) := by
      intro t k
      have := hm₂ 0 (by simp) (-t) k k.2
      have e : (((0 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by push_cast; ring
      rw [e] at this
      simpa using this
    have h0₁ : ∀ t, 0 ≤ m₁ t := fun t => (norm_nonneg _).trans (hb₁ t ⟨1, (adelicMaximalCompact K).one_mem⟩)
    have h0₂ : ∀ t, 0 ≤ m₂ t := fun t => by
      have := (norm_nonneg _).trans (hb₂ (-t) ⟨1, (adelicMaximalCompact K).one_mem⟩)
      simpa using this
    have hM₁ : MemLp m₁ 2 (volume : Measure ℝ) := memLp_two_of_majorant hm₁i hB₁ h0₁
    have hM₂ : MemLp m₂ 2 (volume : Measure ℝ) := memLp_two_of_majorant hm₂i hB₂ h0₂

    set T1 : ℝ → ℂ := fun t => ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hT1
    set T2 : ℝ → ℂ := fun t => ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
        conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
          NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hT2

    have hform : ∀ s : ℝ, Θ (em i) j s = (κ : ℂ) * (T1 (s - τ i) + T2 (s - τ i)) := by
      intro s
      have h := h2 i j (s - τ i)
      dsimp only at h
      have e : ((s - τ i + τ i : ℝ) : ℂ) * Complex.I = (s : ℂ) * Complex.I := by rw [sub_add_cancel]
      rw [show Θ (em i) j s = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g *
            conj (EE (em i) j (((s - τ i + τ i : ℝ) : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) from by
        rw [e]]
      exact h

    have hT1c : Continuous T1 := by
      have hf : Continuous (Function.uncurry fun (t : ℝ) (k : adelicMaximalCompact K) =>
          ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) := by
        refine Continuous.mul ?_ (Complex.continuous_conj.comp ?_)
        · exact (_hψjc i).comp (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk
            (continuous_subtype_val.comp continuous_snd))
        · exact (_hφEjc (em i) j).comp
            (((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const)).mul continuous_const).prodMk
              (continuous_subtype_val.comp continuous_snd))
      have h := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hf
        (isCompact_univ (X := adelicMaximalCompact K))
      simp only [Measure.restrict_univ] at h
      exact h
    have hT2c : Continuous T2 := by
      have hf : Continuous (Function.uncurry fun (t : ℝ) (k : adelicMaximalCompact K) =>
          ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
              NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) := by
        refine Continuous.mul ?_ (Complex.continuous_conj.comp (continuous_const.mul ?_))
        · exact (_hψjc (rP i)).comp ((((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).neg).prodMk
            (continuous_subtype_val.comp continuous_snd))
        · exact hNEc (em i) j (τ i)
      have h := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hf
        (isCompact_univ (X := adelicMaximalCompact K))
      simp only [Measure.restrict_univ] at h
      exact h

    have hT1b : ∀ t, ‖T1 t‖ ≤ m₁ t := by
      intro t
      refine norm_integral_mul_conj_le (maximalCompactHaar K) _ _ (h0₁ t) (hb₁ t) (hmemK _ (hφc1 _ _ _)) ?_
      exact (hφnorm (em i) j _).le
    have hT2b : ∀ t, ‖T2 t‖ ≤ m₂ (-t) := by
      intro t
      refine norm_integral_mul_conj_le (maximalCompactHaar K) _ _ (h0₂ (-t)) (hb₂ t)
        (hmemK _ (continuous_const.mul ?_)) ?_
      · have := hNEc1 (em i) j (t + τ i)
        simpa using this
      · have := hNnorm (em i) j (t + τ i)
        simpa using this.le
    refine ⟨m₁, m₂, hM₁, hM₂, ?_, fun s => ?_⟩
    · have e : Θ (em i) j = fun s => (κ : ℂ) * (T1 (s - τ i) + T2 (s - τ i)) := funext hform
      rw [e]
      exact continuous_const.mul ((hT1c.comp (continuous_id.sub continuous_const)).add
        (hT2c.comp (continuous_id.sub continuous_const)))
    · rw [hform s, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hT1b _) ?_)) hκ.le
      have := hT2b (s - τ i)
      rwa [neg_sub] at this

  have hmem : ∀ (e : ιE) (j : Fin (nE e)), MemLp (Θ e j) 2 (volume : Measure ℝ) := by
    intro e j
    by_cases he : ∃ i : ιP, em i = e
    · obtain ⟨i, rfl⟩ := he
      obtain ⟨m₁, m₂, hM₁, hM₂, hc, hbd⟩ := hpk i j
      refine MemLp.mono' (g := fun s => κ * (m₁ (s - τ i) + m₂ (τ i - s))) ?_ hc.aestronglyMeasurable
        (Filter.Eventually.of_forall hbd)
      exact ((memLp_comp_sub hM₁ (τ i)).add (memLp_comp_sub' hM₂ (τ i))).const_mul κ
    · rw [hzero e (fun i hi => he ⟨i, hi⟩) j]
      exact MemLp.zero
  refine ⟨fun e j => hmem e j, ?_⟩

  refine summable_of_ne_finset_zero (s := Finset.univ.image em) fun e he => ?_
  have he' : ∀ i : ιP, em i ≠ e := by
    intro i hi
    exact he (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have : (fun t : ℝ => ∑ j : Fin (nE e), ‖Θ e j t‖ ^ (2 : ℕ)) = fun _ => 0 := by
    funext t
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hzero e he' j]
    simp
  show ∫ t : ℝ, ∑ j : Fin (nE e), ‖Θ e j t‖ ^ (2 : ℕ) = 0
  rw [this, integral_zero]

end
end S_AutomorphicForm_memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener (solution)
