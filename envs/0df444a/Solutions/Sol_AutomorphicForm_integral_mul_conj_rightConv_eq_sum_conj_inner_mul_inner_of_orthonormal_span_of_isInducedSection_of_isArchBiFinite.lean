-- Prove2me | solution 1 for AutomorphicForm.integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7d84bc7e-4112-5c49-bf29-03b3abe6fc22

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
import Theorems.Thm_AutomorphicForm_star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous
import Theorems.Thm_AutomorphicForm_integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis
import Theorems.Thm_AutomorphicForm_isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_conj_comp_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws31
namespace Bilinear

open MeasureTheory AutomorphicForm

theorem integrable_mul_conj_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => f x * conj (g x)) μ := by
  have hc : Continuous fun x => f x * conj (g x) := hf.mul (Complex.continuous_conj.comp hg)
  have := hc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ (μ := μ)
  simpa using this

theorem integral_mul_conj_symm {X : Type*} [MeasurableSpace X] (μ : Measure X) (a b : X → ℂ) :
    ∫ x, a x * conj (b x) ∂μ = conj (∫ x, b x * conj (a x) ∂μ) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_conj, mul_comm]

variable (K : Type) [Field K] [NumberField K]

def star (f : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ := fun y => conj (f y⁻¹)

theorem star_apply (f : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) : star K f y = conj (f y⁻¹) := rfl

theorem star_star (f : AdelicGL2 (𝓞 K) K → ℂ) : star K (star K f) = f := by
  funext y; simp [star]

theorem continuous_star {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) : Continuous (star K f) :=
  Complex.continuous_conj.comp (hf.comp continuous_inv)

theorem hasCompactSupport_star {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (star K f) := by
  have h1 : HasCompactSupport (f ∘ (Homeomorph.inv (AdelicGL2 (𝓞 K) K))) := hf.comp_homeomorph _
  have h2 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => f y⁻¹) := h1
  exact h2.comp_left (g := fun z : ℂ => conj z) (map_zero _)

theorem isBiInvariantUnder_star {U : Subgroup (AdelicGL2 (𝓞 K) K)} {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsBiInvariantUnder K U f) : IsBiInvariantUnder K U (star K f) := by
  intro u hu g
  have hu' := hf u⁻¹ (U.inv_mem hu)
  refine ⟨?_, ?_⟩
  · show conj (f (u * g)⁻¹) = conj (f g⁻¹)
    rw [mul_inv_rev, (hu' g⁻¹).2]
  · show conj (f (g * u)⁻¹) = conj (f g⁻¹)
    rw [mul_inv_rev, (hu' g⁻¹).1]

theorem isArchBiFinite_star (tysK : ArchTypeFamily K) {f : AdelicGL2 (𝓞 K) K → ℂ} (hfc : Continuous f)
    (hf : IsArchBiFinite K tysK f) : IsArchBiFinite K tysK (star K f) := by
  refine ⟨?_, ?_⟩
  · have h := (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous K tysK f hfc).1 hf.2
    have : (fun x : AdelicGL2 (𝓞 K) K => star K f x⁻¹) = fun x => conj (f x) := by funext x; simp [star]
    rw [this]; exact h
  · have hc' : Continuous (fun x : AdelicGL2 (𝓞 K) K => f x⁻¹) := hfc.comp continuous_inv
    exact (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous K tysK _ hc').2 hf.1

theorem main
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (n : ℕ) (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφEc : ∀ j s, Continuous (φE j s))
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (t : ℝ)
      (_hφEspan : ∀ (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
      (_hfF : IsFactorizableTestFn K f)
      (_hfbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
      (_hfty : IsArchBiFinite K tysK f)
      (Φ Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΦc : Continuous Φ)
      (_hΨ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) Ψ)
      (_hΨc : Continuous Ψ),
    ∫ k, Φ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∑ i : Fin n, ∑ j : Fin n,
        conj (∫ k, rightConv K (φE j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) *
        ((∫ k, Φ (k : AdelicGL2 (𝓞 K) K) * conj (φE i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          conj (∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) := by
  intro αm hαm μ ν _hμ _hν n φE _hφE _hφEflat _hφEc _hφEon t _hφEspan f _hf _hfc _hfF _hfbi _hfty Φ Ψ _hΦc _hΨ _hΨc
  classical
  set s₀ : ℂ := (t : ℂ) * Complex.I with hs₀
  set mK := maximalCompactHaar K with hmK

  have hcK : ∀ (u : AdelicGL2 (𝓞 K) K → ℂ), Continuous u → Continuous fun k : adelicMaximalCompact K => u (k : AdelicGL2 (𝓞 K) K) :=
    fun u hu => hu.comp continuous_subtype_val
  have hint : ∀ (u v : AdelicGL2 (𝓞 K) K → ℂ), Continuous u → Continuous v →
      Integrable (fun k : adelicMaximalCompact K => u (k : AdelicGL2 (𝓞 K) K) * conj (v (k : AdelicGL2 (𝓞 K) K))) mK :=
    fun u v hu hv => integrable_mul_conj_of_continuous mK _ _ (hcK u hu) (hcK v hv)

  have hon : ∀ i j, ∫ k, φE i s₀ (k : AdelicGL2 (𝓞 K) K) * conj (φE j s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK = if i = j then 1 else 0 := by
    intro i j
    rw [← _hφEon i j]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => by
      show φE i s₀ (k : AdelicGL2 (𝓞 K) K) * conj (φE j s₀ (k : AdelicGL2 (𝓞 K) K)) = φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K))
      rw [_hφEflat i s₀ k, _hφEflat j s₀ k])
  have hcoef : ∀ (c : Fin n → ℂ) (i : Fin n),
      ∫ k, (∑ j, c j * φE j s₀ (k : AdelicGL2 (𝓞 K) K)) * conj (φE i s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK = c i := by
    intro c i
    have : (fun k : adelicMaximalCompact K => (∑ j, c j * φE j s₀ (k : AdelicGL2 (𝓞 K) K)) * conj (φE i s₀ (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => ∑ j, c j * (φE j s₀ (k : AdelicGL2 (𝓞 K) K) * conj (φE i s₀ (k : AdelicGL2 (𝓞 K) K))) := by
      funext k; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, integral_finset_sum _ fun j _ => (hint _ _ (_hφEc j s₀) (_hφEc i s₀)).const_mul (c j)]
    simp only [integral_const_mul, hon, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']; simp
  have hpair : ∀ (Φ' : AdelicGL2 (𝓞 K) K → ℂ), Continuous Φ' → ∀ (c : Fin n → ℂ),
      ∫ k, Φ' (k : AdelicGL2 (𝓞 K) K) * conj (∑ j, c j * φE j s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK =
        ∑ j, conj (c j) * ∫ k, Φ' (k : AdelicGL2 (𝓞 K) K) * conj (φE j s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK := by
    intro Φ' hΦ' c
    have : (fun k : adelicMaximalCompact K => Φ' (k : AdelicGL2 (𝓞 K) K) * conj (∑ j, c j * φE j s₀ (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => ∑ j, conj (c j) * (Φ' (k : AdelicGL2 (𝓞 K) K) * conj (φE j s₀ (k : AdelicGL2 (𝓞 K) K))) := by
      funext k; rw [map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; ring
    rw [this, integral_finset_sum _ fun j _ => (hint _ _ hΦ' (_hφEc j s₀)).const_mul _]
    simp only [integral_const_mul]

  have hfs_c : Continuous (star K f) := continuous_star K _hf
  have hfs_cs : HasCompactSupport (star K f) := hasCompactSupport_star K _hfc
  have hfs_F : IsFactorizableTestFn K (star K f) := AutomorphicForm.isFactorizableTestFn_conj_comp_inv K f _hfF
  have hfs_bi := isBiInvariantUnder_star K _hfbi
  have hfs_ty := isArchBiFinite_star K tysK _hf _hfty

  obtain ⟨hR1, hR2, hR3, hR4, hR5⟩ :=
    AutomorphicForm.isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
      K N tysK (etaFst μ αm hαm s₀) (etaSnd ν αm hαm s₀) Ψ _hΨ _hΨc f _hf _hfc _hfF _hfbi _hfty
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (_hφEspan _ hR1 hR2 hR3 hR4 hR5)
  have hRΨ : rightConv K Ψ f = fun x => ∑ j, e j * φE j s₀ x := by
    rw [← he]; funext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hRs : ∀ i : Fin n, ∃ b : Fin n → ℂ, rightConv K (φE i s₀) (star K f) = fun x => ∑ j, b j * φE j s₀ x := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      AutomorphicForm.isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
        K N tysK (etaFst μ αm hαm s₀) (etaSnd ν αm hαm s₀) (φE i s₀) (_hφE i s₀) (_hφEc i s₀) (star K f) hfs_c hfs_cs hfs_F hfs_bi hfs_ty
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (_hφEspan _ h1 h2 h3 h4 h5)
    exact ⟨b, by rw [← hb]; funext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]⟩
  choose b hb using hRs

  have hadj := AutomorphicForm.integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis K hαm μ ν _hμ _hν t
  have he_i : ∀ i, e i = ∑ j, conj (b i j) * ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (φE j s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK := by
    intro i
    have h1 : ∫ k, rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K) * conj (φE i s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK = e i := by
      rw [hRΨ]; exact hcoef e i
    rw [← h1, hmK, hadj Ψ (φE i s₀) _hΨ (_hφE i s₀) _hΨc (_hφEc i s₀) f _hf _hfc]
    show ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K (φE i s₀) (star K f) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = _
    rw [hb i, ← hmK, hpair Ψ _hΨc (b i)]

  have hb_ij : ∀ i j, b i j = conj (∫ k, rightConv K (φE j s₀) f (k : AdelicGL2 (𝓞 K) K) * conj (φE i s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK) := by
    intro i j
    have h2 : ∫ k, rightConv K (φE i s₀) (star K f) (k : AdelicGL2 (𝓞 K) K) * conj (φE j s₀ (k : AdelicGL2 (𝓞 K) K)) ∂mK = b i j := by
      rw [hb i]; exact hcoef (b i) j
    rw [← h2, hmK, hadj (φE i s₀) (φE j s₀) (_hφE i s₀) (_hφE j s₀) (_hφEc i s₀) (_hφEc j s₀) (star K f) hfs_c hfs_cs]
    show ∫ k, φE i s₀ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K (φE j s₀) (star K (star K f)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = _
    rw [star_star, integral_mul_conj_symm]

  rw [hRΨ, hpair Φ _hΦc e]
  simp only [he_i, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb_ij i j]
  ring

end Ws31.Bilinear

end

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (n : ℕ) (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφEc : ∀ j s, Continuous (φE j s))
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (t : ℝ)
      (_hφEspan : ∀ (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
      (_hfF : IsFactorizableTestFn K f)
      (_hfbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
      (_hfty : IsArchBiFinite K tysK f)
      (Φ Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΦc : Continuous Φ)
      (_hΨ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) Ψ)
      (_hΨc : Continuous Ψ),
    ∫ k, Φ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∑ i : Fin n, ∑ j : Fin n,
        conj (∫ k, rightConv K (φE j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) *
        ((∫ k, Φ (k : AdelicGL2 (𝓞 K) K) * conj (φE i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          conj (∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) :=
  Ws31.Bilinear.main K N tysK

end S_AutomorphicForm_integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite (solution)
