-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b31d8412-1ed3-5c9f-a6e0-f442da940055

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_AutomorphicForm_exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (_hfact : IsUnitFactorization K SK f₀ faK ff₀ fSK)
    (N' : ℕ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ C : ℝ, 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (φf ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hφfK : ∀ s, IsArchKFinite K (φf s)) (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hφff : ∀ s, IsKfSmooth K (φf s)) (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g)) (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hφfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => φf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φf s (k : AdelicGL2 (𝓞 K) K) = φf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φf s (g * u) = φf s g)
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule K tysK) (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hφfn : ∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1),
    let a : ℝ → ℂ := fun t =>
      ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
        conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
    let D : ℝ → ℝ := fun t => ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)
    ∃ a' : ℝ → ℂ, (∀ t : ℝ, HasDerivAt a (a' t) t) ∧ Continuous a' ∧
      ∀ t : ℝ, ‖a t‖ + ‖a' t‖ ≤ C * (1 + D t) ^ (-(N' : ℝ)) := by
  intro αm
  obtain ⟨c, hc, hunf⟩ :=
    AutomorphicForm.exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat K
  obtain ⟨C', hC', hdec⟩ :=
    AutomorphicForm.exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
      K SK ξK hξc hξt N hN tysK faK fSK w hξw f₀ _hf₀ _hf₀c ff₀ _hfact N'
  refine ⟨c * C', mul_pos hc hC', ?_⟩
  intro hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν τμ τν _hτμ _hτν φf ψf _hφf _hψf _hφfK _hψfK _hφff _hψff
    _hφfjc _hψfjc _hφfhol _hψfhol _hφfKu _hψfKu _hφfflat _hψfflat _hφflev _hψflev _hφfty _hψfty _hφfn _hψfn
  intro a D
  obtain ⟨J', hJ'd, hJ'c, hJb⟩ := hdec hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν τμ τν _hτμ _hτν φf ψf _hφf _hψf
    _hφfK _hψfK _hφff _hψff _hφfjc _hψfjc _hφfhol _hψfhol _hφfKu _hψfKu _hφfflat _hψfflat _hφflev _hψflev
    _hφfty _hψfty _hφfn _hψfn
  have hid := hunf hαm μ ν _hμc _hνc w f₀ _hf₀ _hf₀c φf ψf _hφf _hψf _hφfjc _hψfjc _hφfflat _hψfflat

  have ha : a = fun t => (c : ℂ) * (fun t : ℝ => ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K)) t := by
    funext t
    exact hid t
  refine ⟨fun t => (c : ℂ) * J' t, fun t => ?_, continuous_const.mul hJ'c, fun t => ?_⟩
  · rw [ha]
    exact (hJ'd t).const_mul (c : ℂ)
  · have hb := hJb t
    have e1 : ‖a t‖ = c * ‖(fun t : ℝ => ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K)) t‖ := by
      rw [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have e2 : ‖(c : ℂ) * J' t‖ = c * ‖J' t‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [e1, e2, ← mul_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left hb hc.le

end S_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization (solution)
