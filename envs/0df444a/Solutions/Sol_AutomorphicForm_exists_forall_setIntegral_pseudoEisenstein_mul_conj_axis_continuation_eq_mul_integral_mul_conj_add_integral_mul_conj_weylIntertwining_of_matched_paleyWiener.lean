-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/56955c2d-bbfa-5896-b86a-e0e150214365

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
import Theorems.Thm_AutomorphicForm_analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_rationalTorusUnipotentQuotient_slab_mul_conj_eq_mul_setIntegral_inv_ideleNorm_smul_integral_maximalCompact
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace CoeffPWGlue

variable (F : Type) [Field F] [NumberField F]

def leftInvariantSubgroup (c : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {h | ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g}
  one_mem' := by
    intro g
    rw [one_mul]
  mul_mem' := by
    intro a b ha hb
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    have hb' : ∀ g : AdelicGL2 (𝓞 F) F, c (b * g) = c g := hb
    intro g
    rw [mul_assoc, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    intro g
    have h := ha' (a⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    exact h.symm

theorem mem_leftInvariantSubgroup {c : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} :
    h ∈ leftInvariantSubgroup F c ↔ ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g :=
  Iff.rfl

omit [NumberField F] in
theorem scalar_mem_borelSubgroup (a : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a ∈ borelSubgroup F := by
  show ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  have hval : ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (a : F) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

omit [NumberField F] in
theorem diagOne_mem_borelSubgroup (a : Fˣ) : diagOne a ∈ borelSubgroup F := by
  show ((diagOne a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem forall_mem_rationalTorusUnipotent_mul_eq (c : AdelicGL2 (𝓞 F) F → ℂ)
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), c (unipotentGL2 x * g) = c g)
    (hB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, c (globalPoints (𝓞 F) F γ * g) = c g) :
    ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g := by
  have hle : rationalTorusUnipotent F ≤ leftInvariantSubgroup F c := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (scalar_mem_borelSubgroup F a) g
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (diagOne_mem_borelSubgroup F a) g
    · rintro _ ⟨x, rfl⟩ g
      exact hN x.toAdd g
  intro h hh g
  have hmem : h ∈ leftInvariantSubgroup F c := hle hh
  exact (mem_leftInvariantSubgroup F).mp hmem g

variable {F}

theorem apply_mul_of_mem_of_isSlabProfile {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : AutomorphicForm.IsSlabProfile F Z ξ φ) :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, φ (x * g) = φ g :=
  forall_mem_rationalTorusUnipotent_mul_eq F φ hφ.unipotent_mul hφ.borel_mul

theorem apply_globalPoints_mul_of_isInducedSection {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (h₁ : IsIdeleClassChar (𝓞 F) F χ₁) (h₂ : IsIdeleClassChar (𝓞 F) F χ₂) :
    ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, f (globalPoints (𝓞 F) F γ * g) = f g := by
  intro γ hγ g
  have hmem : globalPoints (𝓞 F) F γ ∈ adelicBorel (𝓞 F) F := globalPoints_mem_adelicBorel (R := 𝓞 F) (K := F) hγ
  rw [hf _ hmem g, borelDiagFst_globalPoints (R := 𝓞 F) (K := F) hγ hmem,
    borelDiagSnd_globalPoints (R := 𝓞 F) (K := F) hγ hmem, h₁, h₂]
  simp

theorem apply_mul_of_mem_of_isInducedSection {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (h₁ : IsIdeleClassChar (𝓞 F) F χ₁) (h₂ : IsIdeleClassChar (𝓞 F) F χ₂) :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g :=
  forall_mem_rationalTorusUnipotent_mul_eq F f
    (fun x g => isInducedSection_unipotent_mul hf x g) (apply_globalPoints_mul_of_isInducedSection hf h₁ h₂)

theorem ideleNorm_eq_one_of_mem_principalIdeles {γ : (AdeleRing (𝓞 F) F)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F) : NumberField.TateGlobal.ideleNorm F γ = 1 := by
  obtain ⟨η, rfl⟩ := MonoidHom.mem_range.mp hγ
  have h : distribHaarChar (AdeleRing (𝓞 F) F)
      ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) η) = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap F η
  simp [NumberField.TateGlobal.ideleNorm, h]

theorem mul_conj_mul_eq_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) (x y : ℂ) :
    a * x * conj (a * y) = x * conj y := by
  rw [map_mul, mul_mul_mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
  simp

end CoeffPWGlue

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
    ∃ κ : ℝ, 0 < κ ∧
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
    (∀ (e : ιE), (∀ i : ιP, em i ≠ e) → ∀ (j : Fin (nE e)) (t : ℝ),
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0) ∧
    ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
    let vol : ℂ := (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)
    let tE : ℂ := (((t + τ i : ℝ) : ℂ)) * Complex.I
    (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (EE (em i) j tE g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (κ : ℂ) *
        ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) +
          ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (vol⁻¹ * NE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
  intro αm hαm
  letI hMSA : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  letI hMSI : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.ideleBorel K
  haveI : BorelSpace (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.borelSpace_ideleBorel K

  obtain ⟨c, hc0, hcT, hc⟩ :=
    AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa K

  haveI : (NumberField.Idele.idelicHaar K).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨D, hDm, hDF, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K
      (NumberField.Idele.idelicHaar K)
  obtain ⟨V, hV0, hVT, hV⟩ := NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi K D hDm hDF

  obtain ⟨-, -, -, hΦs, hΦF⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hcT
  have hVpos : 0 < V.toReal := ENNReal.toReal_pos hV0 hVT
  have hlog : 0 < Real.log (β / α) := Real.log_pos ((one_lt_div hα).mpr hαβ)

  obtain ⟨C, hC, hTP⟩ := AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK SK ξK hξc hξt N hN tysK hξu hαm
    D hDm hDF V hV0 hVT hV

  refine ⟨(c.toReal * (V.toReal * (Real.log (β / α) / 2))) * C, by positivity, ?_⟩
  intro ι b cls hb hbn hbo hbs hbc ιE _instC μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP _instF μP νP hμPu hνPu hμPic hνPic hμPc hμPν rP hr hdistP ψf hψf hψjc hψhol hνPc hψdec ψ hψ hψrep em τ hem

  have hvol0 : ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos K).ne' (adelicAddHaar_adelicBox_lt_top K).ne).ne'
  have hNEind : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ),
      IsInducedSection (𝓞 K) K (etaFst (ν e) αm hαm (-((t : ℂ) * Complex.I)))
        (etaSnd (μ e) αm hαm (-((t : ℂ) * Complex.I))) (NE e j ((t : ℂ) * Complex.I)) := by
    have hsmul : ∀ {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (a : ℂ),
        IsInducedSection (𝓞 K) K χ₁ χ₂ φ → IsInducedSection (𝓞 K) K χ₁ χ₂ (fun g => a * φ g) :=
      fun a h b hb g => by
        show a * _ = _ * (a * _)
        rw [h b hb g]
        ring
    intro e j t
    have H := (AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
      K hαm (μ e) (ν e) (hμu e) (hνu e) (hμic e) (hνic e) (hμc e) (hνc e) N (φE e j) (hφE e j) (hφEK e j) (hφEf e j)
      (hφEjc e j) (hφEhol e j) (hφEKu e j) (hφElev e j) (OE e j) (EE e j) (NE e j) (hEE e j) t).1
    have H2 := hsmul ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)) H
    have hfun : (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)) *
        (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)) =
        NE e j ((t : ℂ) * Complex.I) :=
      funext fun g => by rw [← mul_assoc, mul_inv_cancel₀ hvol0, one_mul]
    rw [hfun] at H2
    exact H2
  obtain ⟨h0, h45A, h45B⟩ := hTP ι b cls hb hbn hbo hbs hbc ιE μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμPu hνPu hμPic hνPic hμPc hμPν rP hr hdistP ψf hψf hψjc hψhol hνPc hψdec ψ hψ hψrep em τ hem hNEind
  refine ⟨?_, ?_⟩

  ·
    intro e he j t
    have h1 : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ∫ q in {q : RationalTorusUnipotentQuotient K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β},
          ψ q.out * conj (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun x => AutomorphicForm.unipotentGL2 x) (EE e j ((t : ℂ) * Complex.I)) q.out) ∂(rationalTorusUnipotentQuotientMeasure K) := by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE e j
      have htE : ((t : ℂ) * Complex.I) ∈ OE e j := hOax (by
        show (((t : ℂ)) * Complex.I).re = 0
        simp)
      have hls : AutomorphicForm.IsLsXiFunction (𝓞 K) K
          (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun N => levelOne (𝓞 K) K N)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z ξK (EE e j ((t : ℂ) * Complex.I)) := by
        refine ⟨fun γ g => ?_, fun z g => ?_⟩
        · exact AutomorphicForm.axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family K hαm
            (μ e) (ν e) (hμu e) (hνu e) (hμic e) (hνic e) (hμc e) (hνc e) (φE e j)
            (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j)
            (OE e j) (EE e j) (NE e j) (hEE e j) ((t : ℂ) * Complex.I) htE γ g
        · rw [AutomorphicForm.axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family K hαm
            (μ e) (ν e) (hμu e) (hνu e) (hμic e) (hνic e) (hμc e) (hνc e) (φE e j)
            (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j)
            (OE e j) (EE e j) (NE e j) (hEE e j) ((t : ℂ) * Complex.I) htE (z : (AdeleRing (𝓞 K) K)ˣ) g,
            ← Units.val_mul, hμν e]
          rfl
      have hcont : Continuous (EE e j ((t : ℂ) * Complex.I)) :=
        hEjc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨htE, Set.mem_univ g⟩
      exact AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous
        K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦF ξK (EE e j ((t : ℂ) * Complex.I)) hls hcont ψ hψ
    have h2 : ∀ g : AdelicGL2 (𝓞 K) K, constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun x => AutomorphicForm.unipotentGL2 x) (EE e j ((t : ℂ) * Complex.I)) g =
        φE e j ((t : ℂ) * Complex.I) g +
          ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g := by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE e j
      have H := AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family K hαm
        (μ e) (ν e) (hμu e) (hνu e) (hμic e) (hνic e) (φE e j) (hφE e j)
        (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j) (OE e j)
        (EE e j) (NE e j) hO hOc hOhalf hEa hNa hEjc hNjc
        (fun s hs g => by rw [hEser s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNser
      have htE : ((t : ℂ) * Complex.I) ∈ OE e j := hOax (by
        show (((t : ℂ)) * Complex.I).re = 0
        simp)
      intro g
      exact H.2.2 _ htE g
    have h3 : (∫ q in {q : RationalTorusUnipotentQuotient K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β},
          ψ q.out * conj (φE e j ((t : ℂ) * Complex.I) q.out +
            ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) q.out)
            ∂(rationalTorusUnipotentQuotientMeasure K)) =
        ((c.toReal * (V.toReal * (Real.log (β / α) / 2)) : ℝ) : ℂ) *
          ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) := by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE e j
      have htE : ((t : ℂ) * Complex.I) ∈ OE e j := hOax (by
        show (((t : ℂ)) * Complex.I).re = 0
        simp)
      haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K

      have hprin : IsPrincipalTrivial (R := 𝓞 K) (K := K) αm := fun u =>
        Units.val_eq_one.mp (CoeffPWGlue.ideleNorm_eq_one_of_mem_principalIdeles (MonoidHom.mem_range.mpr ⟨u, rfl⟩))

      have hΦ₂m : Measurable (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) := by
        have h1c : Continuous fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g :=
          (hφEjc e j).comp (continuous_const.prodMk continuous_id)
        have h2c : Continuous fun g : AdelicGL2 (𝓞 K) K => NE e j ((t : ℂ) * Complex.I) g :=
          hNjc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨htE, Set.mem_univ g⟩
        exact (h1c.add (continuous_const.mul h2c)).measurable
      have hΦ₁inv := CoeffPWGlue.apply_mul_of_mem_of_isSlabProfile hψ
      have hφinv := CoeffPWGlue.apply_mul_of_mem_of_isInducedSection (hφE e j ((t : ℂ) * Complex.I))
        (etaFst_isIdeleClassChar (hμic e) hprin _) (etaSnd_isIdeleClassChar (hνic e) hprin _)
      have hNinv := CoeffPWGlue.apply_mul_of_mem_of_isInducedSection (hNEind e j t)
        (etaFst_isIdeleClassChar (hνic e) hprin _) (etaSnd_isIdeleClassChar (hμic e) hprin _)
      have hΦ₂inv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K,
          (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (x * g) =
            (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) g := by
        intro x hx g
        show φE e j ((t : ℂ) * Complex.I) (x * g) + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) (x * g) = _
        rw [hφinv x hx g, hNinv x hx g]

      have hψcen : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          ψ (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ψ g :=
        fun z g => hψ.central_transform ⟨z, Subgroup.mem_top z⟩ g
      have hφcen : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φE e j ((t : ℂ) * Complex.I) (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φE e j ((t : ℂ) * Complex.I) g := by
        intro z g
        rw [isInducedSection_centralScalar_mul (hφE e j ((t : ℂ) * Complex.I)) z g, ← Units.val_mul, etaFst_mul_etaSnd, hμν e]
      have hNcen : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          NE e j ((t : ℂ) * Complex.I) (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * NE e j ((t : ℂ) * Complex.I) g := by
        intro z g
        rw [isInducedSection_centralScalar_mul (hNEind e j t) z g, ← Units.val_mul, etaFst_mul_etaSnd, mul_comm ((ν e) z), hμν e]
      have hcen : ∀ (z y : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
          ψ (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) *
              starRingEnd ℂ ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
                (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K))) =
            ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) *
              starRingEnd ℂ ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
                (diagOne y * (k : AdelicGL2 (𝓞 K) K))) := by
        intro z y k
        simp only [mul_assoc]
        rw [hψcen, hφcen, hNcen, mul_left_comm ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹, ← mul_add]
        exact CoeffPWGlue.mul_conj_mul_eq_of_norm_eq_one (hξu z) _ _
      have hint := h0 e j t
      exact (AutomorphicForm.integrableOn_and_setIntegral_rationalTorusUnipotentQuotient_slab_mul_conj_eq_mul_setIntegral_inv_ideleNorm_smul_integral_maximalCompact
        K c hcT hc D hDm hDF V hV0 hVT hV α β hα hαβ.le ψ
        (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
        hψ.measurable hΦ₂m hΦ₁inv hΦ₂inv hcen hint).2

    have h45 : ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) = 0 := by
      exact h45A e he j t
    rw [h1]
    have h1' : (∫ q in {q : RationalTorusUnipotentQuotient K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β},
          ψ q.out * conj (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun x => AutomorphicForm.unipotentGL2 x) (EE e j ((t : ℂ) * Complex.I)) q.out) ∂(rationalTorusUnipotentQuotientMeasure K)) =
        ∫ q in {q : RationalTorusUnipotentQuotient K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β},
          ψ q.out * conj (φE e j ((t : ℂ) * Complex.I) q.out +
            ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) q.out)
            ∂(rationalTorusUnipotentQuotientMeasure K) := by
      congr 1
      funext q
      rw [h2]
    rw [h1', h3, h45, mul_zero]

  ·
    intro i j t vol tE

    have h1 : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (EE (em i) j tE g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ∫ q in {q : RationalTorusUnipotentQuotient K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β},
          ψ q.out * conj (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun x => AutomorphicForm.unipotentGL2 x) (EE (em i) j tE) q.out) ∂(rationalTorusUnipotentQuotientMeasure K) := by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE (em i) j
      have htE : tE ∈ OE (em i) j := hOax (by
        show ((((t + τ i : ℝ) : ℂ)) * Complex.I).re = 0
        simp)
      have hls : AutomorphicForm.IsLsXiFunction (𝓞 K) K
          (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun N => levelOne (𝓞 K) K N)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z ξK (EE (em i) j tE) := by
        refine ⟨fun γ g => ?_, fun z g => ?_⟩
        · exact AutomorphicForm.axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family K hαm
            (μ (em i)) (ν (em i)) (hμu (em i)) (hνu (em i)) (hμic (em i)) (hνic (em i)) (hμc (em i)) (hνc (em i)) (φE (em i) j)
            (hφE (em i) j) (hφEK (em i) j) (hφEf (em i) j) (hφEjc (em i) j) (hφEhol (em i) j) (hφEKu (em i) j)
            (OE (em i) j) (EE (em i) j) (NE (em i) j) (hEE (em i) j) tE htE γ g
        · rw [AutomorphicForm.axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family K hαm
            (μ (em i)) (ν (em i)) (hμu (em i)) (hνu (em i)) (hμic (em i)) (hνic (em i)) (hμc (em i)) (hνc (em i)) (φE (em i) j)
            (hφE (em i) j) (hφEK (em i) j) (hφEf (em i) j) (hφEjc (em i) j) (hφEhol (em i) j) (hφEKu (em i) j)
            (OE (em i) j) (EE (em i) j) (NE (em i) j) (hEE (em i) j) tE htE (z : (AdeleRing (𝓞 K) K)ˣ) g,
            ← Units.val_mul, hμν (em i)]
          rfl
      have hcont : Continuous (EE (em i) j tE) :=
        hEjc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨htE, Set.mem_univ g⟩
      exact AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous
        K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦF ξK (EE (em i) j tE) hls hcont ψ hψ

    have h2 : ∀ g : AdelicGL2 (𝓞 K) K, constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun x => AutomorphicForm.unipotentGL2 x) (EE (em i) j tE) g =
        φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g := by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE (em i) j
      have H := AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family K hαm
        (μ (em i)) (ν (em i)) (hμu (em i)) (hνu (em i)) (hμic (em i)) (hνic (em i)) (φE (em i) j) (hφE (em i) j)
        (hφEK (em i) j) (hφEf (em i) j) (hφEjc (em i) j) (hφEhol (em i) j) (hφEKu (em i) j) (OE (em i) j)
        (EE (em i) j) (NE (em i) j) hO hOc hOhalf hEa hNa hEjc hNjc
        (fun s hs g => by rw [hEser s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNser
      have htE : tE ∈ OE (em i) j := hOax (by
        show ((((t + τ i : ℝ) : ℂ)) * Complex.I).re = 0
        simp)
      intro g
      exact H.2.2 tE htE g

    have h3 : (∫ q in {q : RationalTorusUnipotentQuotient K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β},
          ψ q.out * conj (φE (em i) j tE q.out + vol⁻¹ * NE (em i) j tE q.out) ∂(rationalTorusUnipotentQuotientMeasure K)) =
        ((c.toReal * (V.toReal * (Real.log (β / α) / 2)) : ℝ) : ℂ) *
          ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) := by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE (em i) j
      have htE : tE ∈ OE (em i) j := hOax (by
        show ((((t + τ i : ℝ) : ℂ)) * Complex.I).re = 0
        simp)
      haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K

      have hprin : IsPrincipalTrivial (R := 𝓞 K) (K := K) αm := fun u =>
        Units.val_eq_one.mp (CoeffPWGlue.ideleNorm_eq_one_of_mem_principalIdeles (MonoidHom.mem_range.mpr ⟨u, rfl⟩))

      have hΦ₂m : Measurable (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) := by
        have h1c : Continuous fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g :=
          (hφEjc (em i) j).comp (continuous_const.prodMk continuous_id)
        have h2c : Continuous fun g : AdelicGL2 (𝓞 K) K => NE (em i) j tE g :=
          hNjc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨htE, Set.mem_univ g⟩
        exact (h1c.add (continuous_const.mul h2c)).measurable
      have hΦ₁inv := CoeffPWGlue.apply_mul_of_mem_of_isSlabProfile hψ
      have hφinv := CoeffPWGlue.apply_mul_of_mem_of_isInducedSection (hφE (em i) j tE)
        (etaFst_isIdeleClassChar (hμic (em i)) hprin _) (etaSnd_isIdeleClassChar (hνic (em i)) hprin _)
      have hNinv := CoeffPWGlue.apply_mul_of_mem_of_isInducedSection (hNEind (em i) j (t + τ i))
        (etaFst_isIdeleClassChar (hνic (em i)) hprin _) (etaSnd_isIdeleClassChar (hμic (em i)) hprin _)
      have hΦ₂inv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K,
          (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) (x * g) =
            (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) g := by
        intro x hx g
        show φE (em i) j tE (x * g) + vol⁻¹ * NE (em i) j tE (x * g) = _
        rw [hφinv x hx g, hNinv x hx g]

      have hψcen : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          ψ (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ψ g :=
        fun z g => hψ.central_transform ⟨z, Subgroup.mem_top z⟩ g
      have hφcen : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φE (em i) j tE (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φE (em i) j tE g := by
        intro z g
        rw [isInducedSection_centralScalar_mul (hφE (em i) j tE) z g, ← Units.val_mul, etaFst_mul_etaSnd, hμν (em i)]
      have hNcen : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          NE (em i) j tE (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * NE (em i) j tE g := by
        intro z g
        rw [isInducedSection_centralScalar_mul (hNEind (em i) j (t + τ i)) z g, ← Units.val_mul, etaFst_mul_etaSnd, mul_comm ((ν (em i)) z), hμν (em i)]
      have hcen : ∀ (z y : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
          ψ (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) *
              starRingEnd ℂ ((fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g)
                (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K))) =
            ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) *
              starRingEnd ℂ ((fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g)
                (diagOne y * (k : AdelicGL2 (𝓞 K) K))) := by
        intro z y k
        simp only [mul_assoc]
        rw [hψcen, hφcen, hNcen, mul_left_comm vol⁻¹, ← mul_add]
        exact CoeffPWGlue.mul_conj_mul_eq_of_norm_eq_one (hξu z) _ _
      have hint := h0 (em i) j (t + τ i)
      exact (AutomorphicForm.integrableOn_and_setIntegral_rationalTorusUnipotentQuotient_slab_mul_conj_eq_mul_setIntegral_inv_ideleNorm_smul_integral_maximalCompact
        K c hcT hc D hDm hDF V hV0 hVT hV α β hα hαβ.le ψ
        (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g)
        hψ.measurable hΦ₂m hΦ₁inv hΦ₂inv hcen hint).2

    have h45 : ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) =
        (C : ℂ) *
          ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (vol⁻¹ * NE (em i) j tE (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) := by
      exact h45B i j t

    have h1' : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (EE (em i) j tE g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ∫ q in {q : RationalTorusUnipotentQuotient K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β},
          ψ q.out * conj (φE (em i) j tE q.out + vol⁻¹ * NE (em i) j tE q.out)
            ∂(rationalTorusUnipotentQuotientMeasure K) := by
      rw [h1]
      congr 1
      funext q
      rw [h2]
    rw [h1', h3, h45, ← mul_assoc]
    congr 1
    push_cast
    ring

end S_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener (solution)
