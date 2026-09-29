-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5d6db9ed-1f02-5a90-afa7-bcdf8faacb21

import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_exists_sum_isUnitFactorization_of_isFactorizableTestFn
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

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
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
    (_hfact : IsFactorizableTestFn K f₀)
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
  obtain ⟨n, c, T, fa, fi, ffi, fSi, hT, hfi, hsum⟩ :=
    AutomorphicForm.exists_sum_isUnitFactorization_of_isFactorizableTestFn K SK f₀ _hfact
  have key := fun i : Fin n =>
    AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
      K (T i) ξK hξc hξt N (fun v hv => hT i (hN v hv)) tysK fa (fSi i) w hξw (fi i) (hfi i).1 (hfi i).2.1
      (ffi i) (hfi i).2.2 N'
  choose Ci hCi hbi using key
  refine ⟨∑ i, ‖c i‖ * Ci i + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hCi i).le) one_pos, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν φf ψf hφf hψf hφfK hψfK hφff hψff hφfjc hψfjc
    hφfhol hψfhol hφfKu hψfKu hφfflat hψfflat hφflev hψflev hφfty hψfty hφfn hψfn
  have hb := fun i : Fin n => hbi i hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν φf ψf hφf hψf hφfK hψfK
    hφff hψff hφfjc hψfjc hφfhol hψfhol hφfKu hψfKu hφfflat hψfflat hφflev hψflev hφfty hψfty hφfn hψfn
  choose a' ha' hca' hbd using hb

  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  have hψc : ∀ t : ℝ, Continuous (ψf ((t : ℂ) * Complex.I)) := fun t =>
    hψfjc.comp (continuous_const.prodMk continuous_id)
  have hφc : ∀ t : ℝ, Continuous (φf ((t : ℂ) * Complex.I)) := fun t =>
    hφfjc.comp (continuous_const.prodMk continuous_id)
  have hΨc : ∀ t : ℝ, Continuous (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) := fun t =>
    (hψc t).mul (Complex.continuous_ofReal.comp
      ((NumberField.TateGlobal.continuous_ideleNorm_det K).rpow_const
        fun g => Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'))

  have hfact : ∀ i : Fin n, IsFactorizableTestFn K (fi i) := fun i =>
    ⟨fa, ffi i, (hfi i).2.2.1, (hfi i).2.2.2.1, (hfi i).2.2.2.2.2.2.2⟩

  have hrc : ∀ (t : ℝ) (k : AdelicGL2 (𝓞 K) K),
      rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ k =
        ∑ i, c i * rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) k := by
    intro t k
    simp only [rightConv_apply]
    have hint : ∀ i : Fin n, Integrable (fun x : AdelicGL2 (𝓞 K) K => (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (k * x) * fi i x)
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := fun i =>
      Continuous.integrable_of_hasCompactSupport
        (((hΨc t).comp (continuous_const.mul continuous_id)).mul (hfi i).1)
        (hfi i).2.1.mul_left
    calc (∫ x : AdelicGL2 (𝓞 K) K, (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (k * x) * f₀ x ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
        = ∫ x : AdelicGL2 (𝓞 K) K, ∑ i, c i * ((fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (k * x) * fi i x)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
          congr 1; funext x
          rw [hsum x, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∫ x : AdelicGL2 (𝓞 K) K, c i * ((fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (k * x) * fi i x)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
          integral_finsetSum _ fun i _ => (hint i).const_mul (c i)
      _ = _ := Finset.sum_congr rfl fun i _ => integral_const_mul _ _

  have hlin : ∀ t : ℝ,
      (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
          conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
        ∑ i, c i * ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) *
          conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro t
    have hcont : ∀ i : Fin n, Continuous (rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i)) := fun i =>
      (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K _ (hΨc t) (fi i) (hfact i)).1
    have hintK : ∀ i : Fin n, Integrable (fun k : ↥(adelicMaximalCompact K) =>
        rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) * conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)))
        (maximalCompactHaar K) := fun i =>
      Continuous.integrable_of_hasCompactSupport
        (((hcont i).comp continuous_subtype_val).mul
          (Complex.continuous_conj.comp ((hφc t).comp continuous_subtype_val)))
        (HasCompactSupport.of_compactSpace _)
    calc (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
          conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
        = ∫ k, ∑ i, c i * (rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) *
            conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) := by
          congr 1; funext k
          rw [hrc t k, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∫ k, c i * (rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) *
            conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) :=
          integral_finsetSum _ fun i _ => (hintK i).const_mul (c i)
      _ = _ := Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  refine ⟨fun t => ∑ i, c i * a' i t, ?_, ?_, ?_⟩
  · intro t
    have hA : (fun t : ℝ => ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
          conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
        fun t : ℝ => ∑ i, c i * ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) *
          conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := funext hlin
    rw [hA]
    exact HasDerivAt.fun_sum fun i _ => (ha' i t).const_mul (c i)
  · exact continuous_finsetSum _ fun i _ => continuous_const.mul (hca' i)
  · intro t
    dsimp only at hbd ⊢
    rw [hlin t]
    have hρ : 0 ≤ (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)) ^ (-(N' : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    calc ‖∑ i, c i * ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) *
            conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ + ‖∑ i, c i * a' i t‖
        ≤ ∑ i, ‖c i‖ * ‖∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) *
            conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ + ∑ i, ‖c i‖ * ‖a' i t‖ := by
          gcongr
          · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
          · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
      _ = ∑ i, ‖c i‖ * (‖∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
            (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (fi i) (k : AdelicGL2 (𝓞 K) K) *
            conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ + ‖a' i t‖) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, ‖c i‖ * (Ci i * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)) ^ (-(N' : ℝ))) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbd i t) (norm_nonneg _)
      _ = (∑ i, ‖c i‖ * Ci i) * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)) ^ (-(N' : ℝ)) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (∑ i, ‖c i‖ * Ci i + 1) * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)) ^ (-(N' : ℝ)) := by
          gcongr; linarith

end S_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn (solution)
