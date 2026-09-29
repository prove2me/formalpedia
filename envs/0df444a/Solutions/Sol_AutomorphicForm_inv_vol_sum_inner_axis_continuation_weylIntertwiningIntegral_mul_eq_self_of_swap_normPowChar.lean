-- Prove2me | solution 1 for AutomorphicForm.inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/aca6033a-c27d-5bbe-92c2-157653d2c351

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
import Theorems.Thm_AutomorphicForm_orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
import Theorems.Thm_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift
import Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
import Theorems.Thm_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws31
namespace CtInversion

open MeasureTheory AutomorphicForm NumberField.TateGlobal

variable (K : Type) [Field K] [NumberField K]

theorem shifted_datum (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ) (O : Set ℂ) (E Nn : ℂ → AdelicGL2 (𝓞 K) K → ℂ) (c : ℝ)
    (h : IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => E s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nn s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nn p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        E s g = φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nn s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φ s) g)) :
    IsOpen ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧ IsPreconnected ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧ {s : ℂ | s.re = 0} ⊆ ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => (fun s' g' => E (s' + ((c : ℂ) * Complex.I)) g') s g) ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => (fun s' g' => Nn (s' + ((c : ℂ) * Complex.I)) g') s g) ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => (fun s' g' => E (s' + ((c : ℂ) * Complex.I)) g') p.1 p.2) (((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => (fun s' g' => Nn (s' + ((c : ℂ) * Complex.I)) g') p.1 p.2) (((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        (fun s' g' => E (s' + ((c : ℂ) * Complex.I)) g') s g = (fun s' => φ (s' + ((c : ℂ) * Complex.I))) s g + ∑' ξ : K, (fun s' => φ (s' + ((c : ℂ) * Complex.I))) s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        (fun s' g' => Nn (s' + ((c : ℂ) * Complex.I)) g') s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) ((fun s' => φ (s' + ((c : ℂ) * Complex.I))) s) g) := by
  obtain ⟨hO, hOc, hax, hhalf, hEa, hNa, hEc, hNc, hEid, hNid⟩ := h
  have hre : ∀ s : ℂ, (s + ((c : ℂ) * Complex.I)).re = s.re := fun s => by simp
  have hmaps : Set.MapsTo (fun s : ℂ => s + ((c : ℂ) * Complex.I)) ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) O :=
    fun s hs => hs
  refine ⟨hO.preimage (continuous_id.add continuous_const), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O = (fun s : ℂ => s - ((c : ℂ) * Complex.I)) '' O := by
      ext s
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h; exact ⟨s + ((c : ℂ) * Complex.I), h, by ring⟩
      · rintro ⟨s', h', rfl⟩; simpa using h'
    rw [this]
    exact hOc.image _ (continuous_id.sub continuous_const).continuousOn
  · intro s hs; show s + ((c : ℂ) * Complex.I) ∈ O; exact hax (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre, hs])
  · intro s hs; show s + ((c : ℂ) * Complex.I) ∈ O; exact hhalf (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre]; exact hs)
  · intro g; exact (hEa g).comp ((analyticOnNhd_id).add analyticOnNhd_const) hmaps
  · intro g; exact (hNa g).comp ((analyticOnNhd_id).add analyticOnNhd_const) hmaps
  · exact hEc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn)
      (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  · exact hNc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn)
      (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  · intro s hs g; exact hEid (s + ((c : ℂ) * Complex.I)) (by rw [hre]; exact hs) g
  · intro s hs g; exact hNid (s + ((c : ℂ) * Complex.I)) (by rw [hre]; exact hs) g

theorem integral_mul_conj_symm {X : Type*} [MeasurableSpace X] (μ : Measure X) (a b : X → ℂ) :
    ∫ x, a x * conj (b x) ∂μ = conj (∫ x, b x * conj (a x) ∂μ) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_conj, mul_comm]

theorem integrable_mul_conj_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => f x * conj (g x)) μ := by
  have hc : Continuous fun x => f x * conj (g x) := hf.mul (Complex.continuous_conj.comp hg)
  have := hc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ (μ := μ)
  simpa using this

theorem isArchKFinite_of_uniform (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (h : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K, (fun k : ↥(archRowIsometrySubgroup K w) => φ (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) :
    IsArchKFinite K φ := by
  classical
  intro w
  obtain ⟨W, hWfd, hW⟩ := h w
  haveI := hWfd
  let b := Module.finBasis ℂ W

  let a : Fin (Module.finrank ℂ W) → AdelicGL2 (𝓞 K) K → ℂ := fun i g => b.repr ⟨_, hW g⟩ i
  refine ⟨(Finset.univ : Finset (Fin (Module.finrank ℂ W))).image a, ?_⟩
  rintro k hk
  have hrep : ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = ∑ i, a i g * ((b i : W) : ↥(archRowIsometrySubgroup K w) → ℂ) ⟨k, hk⟩ := by
    intro g
    have := b.sum_repr (⟨_, hW g⟩ : W)
    have h2 := congrArg (fun v : W => (v : ↥(archRowIsometrySubgroup K w) → ℂ) ⟨k, hk⟩) this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2]
  have : (fun x : AdelicGL2 (𝓞 K) K => φ (x * k)) = ∑ i, ((b i : W) : ↥(archRowIsometrySubgroup K w) → ℂ) ⟨k, hk⟩ • a i := by
    funext x; rw [hrep x]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem isInducedSection_sum {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {m : ℕ} (c : Fin m → ℂ) (W : Fin m → AdelicGL2 (𝓞 K) K → ℂ)
    (hW : ∀ l, IsInducedSection (𝓞 K) K χ₁ χ₂ (W l)) :
    IsInducedSection (𝓞 K) K χ₁ χ₂ (fun g => ∑ l, c l * W l g) := by
  intro b hb g
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hW l b hb g]; ring

theorem main
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (φ₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ₁ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ₁ s))
      (_hφ₁K : ∀ s, IsArchKFinite K (φ₁ s)) (_hφ₁sm : ∀ s, IsKfSmooth K (φ₁ s))
      (_hφ₁jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ₁ p.1 p.2))
      (_hφ₁hol : ∀ g, Differentiable ℂ (fun s => φ₁ s g))
      (_hφ₁Ku : ∀ (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φ₁ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφ₁lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₁ s (g * u) = φ₁ s g)
      (_hφ₁ty : ∀ (s : ℂ), φ₁ s ∈ archCutSubmodule K tysK)
      (O₁ : Set ℂ) (E₁ N₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hE₁ :
      IsOpen O₁ ∧ IsPreconnected O₁ ∧ {s : ℂ | s.re = 0} ⊆ O₁ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O₁ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => E₁ s g) O₁) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => N₁ s g) O₁) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E₁ p.1 p.2) (O₁ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => N₁ p.1 p.2) (O₁ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        E₁ s g = φ₁ s g + ∑' ξ : K, φ₁ s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        N₁ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φ₁ s) g))
      (σ : ℝ) (μb νb : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hsw : μb = ν * NumberField.TateGlobal.normPowChar K σ ∧ νb = μ * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (_hμb : IsUnitaryChar (𝓞 K) K μb) (_hνb : IsUnitaryChar (𝓞 K) K νb)
      (_hμbic : IsIdeleClassChar (𝓞 K) K μb) (_hνbic : IsIdeleClassChar (𝓞 K) K νb)
      (_hμbc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μb z : ℂˣ) : ℂ))
      (_hνbc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((νb z : ℂˣ) : ℂ))
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μb αm hαm s) (etaSnd νb αm hαm s) (φE j s))
      (_hφEK : ∀ j s, IsArchKFinite K (φE j s))
      (_hφEf : ∀ j s, IsKfSmooth K (φE j s))
      (_hφEjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j p.1 p.2))
      (_hφEhol : ∀ j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE j s g))
      (_hφEKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE j s (g * u) = φE j s g)
      (_hφEty : ∀ j (s : ℂ), φE j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μb αm hαm ((t : ℂ) * Complex.I)) (etaSnd νb αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
      (OE : Fin n → Set ℂ) (EE NE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (j : Fin n),
      IsOpen (OE j) ∧ IsPreconnected (OE j) ∧ {s : ℂ | s.re = 0} ⊆ (OE j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE j s g) (OE j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE j s g) (OE j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE j s g = φE j s g + ∑' ξ : K, φE j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE j s) g))
      (t : ℝ) (g : AdelicGL2 (𝓞 K) K),
    ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * ∑ j' : Fin n,
        (∫ k, (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          NE j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g =
      φ₁ ((t : ℂ) * Complex.I) g := by
  intro αm hαm μ ν hμ hν hμic hνic hμc hνc φ₁ hφ₁ hφ₁K hφ₁sm hφ₁jc hφ₁hol hφ₁Ku hφ₁lev hφ₁ty O₁ E₁ N₁ hE₁
    σ μb νb hsw hμb hνb hμbic hνbic hμbc hνbc n φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan
    OE EE NE hEE t g
  classical
  have hαI : ∀ x, ((αm x : ℝˣ) : ℝ) = ideleNorm K x := fun _ => rfl
  have hcs : ∀ (F : ℂ → AdelicGL2 (𝓞 K) K → ℂ), Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => F p.1 p.2) → ∀ s, Continuous (F s) :=
    fun F hF s => hF.comp (continuous_const.prodMk continuous_id)
  have hcK : ∀ (u : AdelicGL2 (𝓞 K) K → ℂ), Continuous u → Continuous fun k : adelicMaximalCompact K => u (k : AdelicGL2 (𝓞 K) K) :=
    fun u hu => hu.comp continuous_subtype_val
  have hint : ∀ (u v : AdelicGL2 (𝓞 K) K → ℂ), Continuous u → Continuous v →
      Integrable (fun k : adelicMaximalCompact K => u (k : AdelicGL2 (𝓞 K) K) * conj (v (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
    fun u v hu hv => integrable_mul_conj_of_continuous (maximalCompactHaar K) _ _ (hcK u hu) (hcK v hv)
  have hpair : ∀ (Φ' : AdelicGL2 (𝓞 K) K → ℂ), Continuous Φ' → ∀ (m : ℕ) (W : Fin m → AdelicGL2 (𝓞 K) K → ℂ), (∀ l, Continuous (W l)) → ∀ (c : Fin m → ℂ),
      ∫ k, Φ' (k : AdelicGL2 (𝓞 K) K) * conj (∑ l, c l * W l (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∑ l, conj (c l) * ∫ k, Φ' (k : AdelicGL2 (𝓞 K) K) * conj (W l (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro Φ' hΦ' m W hW c
    have : (fun k : adelicMaximalCompact K => Φ' (k : AdelicGL2 (𝓞 K) K) * conj (∑ l, c l * W l (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => ∑ l, conj (c l) * (Φ' (k : AdelicGL2 (𝓞 K) K) * conj (W l (k : AdelicGL2 (𝓞 K) K))) := by
      funext k; rw [map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by rw [map_mul]; ring
    rw [this, integral_finset_sum _ fun l _ => (hint _ _ hΦ' (hW l)).const_mul _]
    simp only [integral_const_mul]
  have hpairL : ∀ (Φ' : AdelicGL2 (𝓞 K) K → ℂ), Continuous Φ' → ∀ (m : ℕ) (W : Fin m → AdelicGL2 (𝓞 K) K → ℂ), (∀ l, Continuous (W l)) → ∀ (c : Fin m → ℂ),
      ∫ k, (∑ l, c l * W l (k : AdelicGL2 (𝓞 K) K)) * conj (Φ' (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∑ l, c l * ∫ k, W l (k : AdelicGL2 (𝓞 K) K) * conj (Φ' (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro Φ' hΦ' m W hW c
    have : (fun k : adelicMaximalCompact K => (∑ l, c l * W l (k : AdelicGL2 (𝓞 K) K)) * conj (Φ' (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => ∑ l, c l * (W l (k : AdelicGL2 (𝓞 K) K) * conj (Φ' (k : AdelicGL2 (𝓞 K) K))) := by
      funext k; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, integral_finset_sum _ fun l _ => (hint _ _ (hW l) hΦ').const_mul (c l)]
    simp only [integral_const_mul]
  have hcoef : ∀ (m : ℕ) (W : Fin m → AdelicGL2 (𝓞 K) K → ℂ), (∀ l, Continuous (W l)) →
      (∀ l l', ∫ k, W l (k : AdelicGL2 (𝓞 K) K) * conj (W l' (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = if l = l' then 1 else 0) →
      ∀ (c : Fin m → ℂ) (l : Fin m),
      ∫ k, (∑ l', c l' * W l' (k : AdelicGL2 (𝓞 K) K)) * conj (W l (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = c l := by
    intro m W hW hon c l
    rw [hpairL (W l) (hW l) m W hW c]
    simp only [hon, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']; simp

  have hc1 : (((-(t + σ) : ℝ) : ℂ) * Complex.I) = (-((((t + σ : ℝ) : ℂ)) * Complex.I)) := by push_cast; ring
  have hc2 : -((t : ℂ) * Complex.I) + (((-σ : ℝ) : ℂ) * Complex.I) = (-((((t + σ : ℝ) : ℂ)) * Complex.I)) := by push_cast; ring

  have hSh := AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift K αm hαm hαI
  have hPb : ∀ s : ℂ, etaFst μb αm hαm s = etaFst ν αm hαm (s + (((σ : ℝ) : ℂ) * Complex.I)) ∧ etaSnd νb αm hαm s = etaSnd μ αm hαm (s + (((σ : ℝ) : ℂ) * Complex.I)) := by
    intro s; refine ⟨?_, ?_⟩
    · rw [hsw.1]; exact (hSh ν σ s).1
    · rw [hsw.2]; exact (hSh μ σ s).2.2.2
  have hPb' : ∀ s : ℂ, etaFst νb αm hαm s = etaFst μ αm hαm (s - (((σ : ℝ) : ℂ) * Complex.I)) ∧ etaSnd μb αm hαm s = etaSnd ν αm hαm (s - (((σ : ℝ) : ℂ) * Complex.I)) := by
    intro s; refine ⟨?_, ?_⟩
    · rw [hsw.2]; exact (hSh μ σ s).2.1
    · rw [hsw.1]; exact (hSh ν σ s).2.2.1

  have hGsec : ∀ (l : Fin n) (s : ℂ), IsInducedSection (𝓞 K) K (etaFst ν αm hαm s) (etaSnd μ αm hαm s)
      ((fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) s) := by
    intro l s
    have h := hφE l (s + (((-σ : ℝ) : ℂ) * Complex.I))
    rw [(hPb _).1, (hPb _).2] at h
    have e : s + (((-σ : ℝ) : ℂ) * Complex.I) + (((σ : ℝ) : ℂ) * Complex.I) = s := by push_cast; ring
    rw [e] at h; exact h
  have hShK : ∀ (l : Fin n) (s : ℂ), IsArchKFinite K ((fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) s) := fun l s => hφEK l _
  have hShsm : ∀ (l : Fin n) (s : ℂ), IsKfSmooth K ((fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) s) := fun l s => hφEf l _
  have hShjc : ∀ (l : Fin n), Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => (fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) p.1 p.2) :=
    fun l => (hφEjc l).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  have hShhol : ∀ (l : Fin n) (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => (fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) s g) :=
    fun l g => (hφEhol l g).comp (differentiable_id.add_const _)
  have hShKu : ∀ (l : Fin n) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k : ↥(archRowIsometrySubgroup K w) => (fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W :=
    fun l w => (hφEKu l w).imp fun W hW => ⟨hW.1, fun s g => hW.2 _ g⟩
  have hShlev : ∀ (l : Fin n) (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      (fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) s (g * u) = (fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) s g :=
    fun l s g u hu => hφElev l _ g u hu
  have hdatG : ∀ l : Fin n, _ := fun l => shifted_datum K (φE l) (OE l) (EE l) (NE l) (-σ) (hEE l)

  have hA : ∀ l : Fin n,
      ∫ k, φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro l
    have h := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
      K N hN hαm μ ν hμ hν hμic hνic hμc hνc
      φ₁ hφ₁ hφ₁K hφ₁sm hφ₁jc hφ₁hol hφ₁Ku hφ₁lev
      (fun s' => φE l (s' + (((-σ : ℝ) : ℂ) * Complex.I))) (hGsec l) (hShK l) (hShsm l) (hShjc l) (hShhol l) (hShKu l) (hShlev l)
      O₁ E₁ N₁ hE₁ _ _ _ (hdatG l) t
    simp only [hc2] at h
    exact h

  obtain ⟨hUsec0, hUc, hUlev, hUKu⟩ :=
    AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
      K hαm μ ν hμ hν hμic hνic hμc hνc N φ₁ hφ₁ hφ₁K hφ₁sm hφ₁jc hφ₁hol hφ₁Ku hφ₁lev O₁ E₁ N₁ hE₁ t
  have hUty0 := AutomorphicForm.axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
      K tysK hαm μ ν hμ hν hμic hνic hμc hνc φ₁ hφ₁ hφ₁K hφ₁sm hφ₁jc hφ₁hol hφ₁Ku hφ₁ty O₁ E₁ N₁ hE₁ t
  have hUty : (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') ∈ archCutSubmodule K tysK := by
    have : (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') = ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ • N₁ ((t : ℂ) * Complex.I) := by
      funext g'; simp only [Pi.smul_apply, smul_eq_mul]
    rw [this]; exact Submodule.smul_mem _ _ hUty0
  have hUKf : IsArchKFinite K (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') := isArchKFinite_of_uniform K _ hUKu
  have hc3 : ((((-(t + σ) : ℝ) : ℂ)) * Complex.I) + (((σ : ℝ) : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by push_cast; ring
  have hUsec : IsInducedSection (𝓞 K) K (etaFst μb αm hαm ((((-(t + σ) : ℝ) : ℂ)) * Complex.I)) (etaSnd νb αm hαm ((((-(t + σ) : ℝ) : ℂ)) * Complex.I)) (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') := by
    rw [(hPb _).1, (hPb _).2, hc3]; exact hUsec0
  have hUlev' : ∀ (g' : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') (g' * u) = (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') g' := by
    intro g' u hu; beta_reduce; rw [hUlev g' u hu]

  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hφEspan (-(t + σ)) _ hUsec hUc hUKf hUlev' hUty)
  have hUeq : (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') = fun x => ∑ j, c' j * φE j (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x := by
    rw [← hc']; funext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc1]

  have hφc : ∀ j : Fin n, Continuous (fun g' : AdelicGL2 (𝓞 K) K => φE j (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g') := fun j => hcs _ (hφEjc j) _
  have hφon' : ∀ l l' : Fin n,
      ∫ k, φE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (φE l' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = if l = l' then 1 else 0 := by
    intro l l'
    rw [← hφEon l l']
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => by
      show φE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (φE l' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) = _
      rw [hφEflat l _ k, hφEflat l' _ k])

  have hc'C : ∀ j : Fin n, c' j = ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE j (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro j
    rw [← hcoef n (fun j g' => φE j (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g') hφc hφon' c' j]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have := congrFun hUeq (k : AdelicGL2 (𝓞 K) K)
    beta_reduce at this ⊢
    rw [this]

  have hUU : ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∑ j, conj (c' j) * c' j := by
    have h1 : ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (∑ j, c' j * φE j (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      have := congrFun hUeq (k : AdelicGL2 (𝓞 K) K); beta_reduce at this ⊢; rw [← this]
    rw [h1, hpair (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) g') hUc n (fun j g' => φE j (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g') hφc c']
    refine Finset.sum_congr rfl fun j _ => ?_
    beta_reduce; rw [hc'C j]

  have hunit := AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
    K hαm μ ν hμ hν hμic hνic hμc hνc φ₁ hφ₁ hφ₁K hφ₁sm hφ₁jc hφ₁hol hφ₁Ku φ₁ hφ₁ hφ₁K hφ₁sm hφ₁jc hφ₁hol hφ₁Ku
    O₁ E₁ N₁ hE₁ O₁ E₁ N₁ hE₁ t
  simp only [] at hunit

  obtain ⟨hWon, hWprops⟩ :=
    AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
      K N tysK hαm μb νb hμb hνb hμbic hνbic hμbc hνbc n φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon
      OE EE NE hEE (-(t + σ))
  simp only [hc1] at hWon hWprops
  have hWc : ∀ l : Fin n, Continuous (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g') := fun l => (hWprops l).2.1
  have hc4 : -(-((((t + σ : ℝ) : ℂ)) * Complex.I)) - (((σ : ℝ) : ℂ) * Complex.I) = ((t : ℂ) * Complex.I) := by push_cast; ring
  have hWsec : ∀ l : Fin n, IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I))
      (fun g' : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g') := by
    intro l
    have h := (hWprops l).1
    rw [(hPb' _).1, (hPb' _).2, hc4] at h
    exact h

  set C : Fin n → ℂ := fun j => ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE j (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hCdef
  have hc'C' : ∀ j, c' j = C j := fun j => by rw [hCdef]; exact hc'C j
  set S : AdelicGL2 (𝓞 K) K → ℂ := fun x => ∑ l, C l * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x) with hSdef
  have hSc : Continuous S := by
    rw [hSdef]; exact continuous_finset_sum _ fun l _ => continuous_const.mul (hWc l)
  have hSsec : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) S := by
    rw [hSdef]; exact isInducedSection_sum K C _ hWsec
  have hφ₁c : Continuous (φ₁ ((t : ℂ) * Complex.I)) := hcs _ hφ₁jc _
  set Y : ℂ := ∑ j, conj (C j) * C j with hY
  have hYreal : conj Y = Y := by
    rw [hY, map_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [map_mul, Complex.conj_conj, mul_comm]
  have h11 : ∫ k, φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = Y := by
    rw [← hunit, hUU, hY]; simp only [hc'C']
  have h1S : ∫ k, φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (S (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = Y := by
    rw [hSdef, hpair (φ₁ ((t : ℂ) * Complex.I)) hφ₁c n _ hWc C, hY]
    refine Finset.sum_congr rfl fun l _ => ?_
    beta_reduce; rw [hA l]
  have hS1 : ∫ k, S (k : AdelicGL2 (𝓞 K) K) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = Y := by
    rw [integral_mul_conj_symm, h1S, hYreal]
  have hSS : ∫ k, S (k : AdelicGL2 (𝓞 K) K) * conj (S (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = Y := by
    have : ∫ k, S (k : AdelicGL2 (𝓞 K) K) * conj (S (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = ∫ k, S (k : AdelicGL2 (𝓞 K) K) * conj (∑ l, C l * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE l (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) := by
      rw [hSdef]
    rw [this, hpair S hSc n _ hWc C, hY]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hSdef, hcoef n _ hWc hWon C l]

  have hPP : ∫ k, (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = 0 := by
    have e : (fun k : adelicMaximalCompact K => (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) - φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (S (k : AdelicGL2 (𝓞 K) K))) -
          (S (k : AdelicGL2 (𝓞 K) K) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) - S (k : AdelicGL2 (𝓞 K) K) * conj (S (k : AdelicGL2 (𝓞 K) K))) := by
      funext k; rw [map_sub]; ring
    have hI1 := hint _ _ hφ₁c hφ₁c
    have hI2 := hint _ _ hφ₁c hSc
    have hI3 := hint _ _ hSc hφ₁c
    have hI4 := hint _ _ hSc hSc
    have h12 : Integrable (fun k : adelicMaximalCompact K =>
        φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) - φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (S (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) := hI1.sub hI2
    have h34 : Integrable (fun k : adelicMaximalCompact K =>
        S (k : AdelicGL2 (𝓞 K) K) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) - S (k : AdelicGL2 (𝓞 K) K) * conj (S (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) := hI3.sub hI4
    rw [e, integral_sub h12 h34, integral_sub hI1 hI2, integral_sub hI3 hI4, h11, h1S, hS1, hSS]
    ring

  have hPK : ∀ k : adelicMaximalCompact K, φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) = S (k : AdelicGL2 (𝓞 K) K) := by
    have hPc : Continuous fun k : adelicMaximalCompact K => φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K) :=
      (hcK _ hφ₁c).sub (hcK _ hSc)
    have hns : ∫ k, Complex.normSq (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = 0 := by
      have h2 : (fun k : adelicMaximalCompact K => (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) * conj (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K))) =
          fun k : adelicMaximalCompact K => ((Complex.normSq (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) : ℝ) : ℂ) := by
        funext k; rw [Complex.mul_conj]
      have h3 := hPP
      rw [h2, integral_complex_ofReal] at h3
      exact_mod_cast h3
    have hnn : 0 ≤ᵐ[(maximalCompactHaar K)] fun k : adelicMaximalCompact K => Complex.normSq (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) :=
      Filter.Eventually.of_forall fun k => Complex.normSq_nonneg _
    have hnsc : Continuous fun k : adelicMaximalCompact K => Complex.normSq (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K)) :=
      Complex.continuous_normSq.comp hPc
    have hi : Integrable (fun k : adelicMaximalCompact K => Complex.normSq (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) := by
      have := hnsc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ (μ := (maximalCompactHaar K))
      simpa using this
    have hae : (fun k : adelicMaximalCompact K => Complex.normSq (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K))) =ᵐ[(maximalCompactHaar K)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hns
    have hzero : (fun k : adelicMaximalCompact K => Complex.normSq (φ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) - S (k : AdelicGL2 (𝓞 K) K))) = 0 :=
      (Continuous.ae_eq_iff_eq (maximalCompactHaar K) hnsc continuous_const).mp hae
    intro k
    have := congrFun hzero k
    simp only [Pi.zero_apply, Complex.normSq_eq_zero, sub_eq_zero] at this
    exact this

  have hPG : φ₁ ((t : ℂ) * Complex.I) = S :=
    AutomorphicForm.eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq K _ _ _ _ (hφ₁ ((t : ℂ) * Complex.I)) hSsec hPK

  rw [congrFun hPG g, hSdef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hCdef]; ring

end Ws31.CtInversion

end

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (φ₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ₁ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ₁ s))
      (_hφ₁K : ∀ s, IsArchKFinite K (φ₁ s)) (_hφ₁sm : ∀ s, IsKfSmooth K (φ₁ s))
      (_hφ₁jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ₁ p.1 p.2))
      (_hφ₁hol : ∀ g, Differentiable ℂ (fun s => φ₁ s g))
      (_hφ₁Ku : ∀ (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φ₁ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφ₁lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₁ s (g * u) = φ₁ s g)
      (_hφ₁ty : ∀ (s : ℂ), φ₁ s ∈ archCutSubmodule K tysK)
      (O₁ : Set ℂ) (E₁ N₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hE₁ :
      IsOpen O₁ ∧ IsPreconnected O₁ ∧ {s : ℂ | s.re = 0} ⊆ O₁ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O₁ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => E₁ s g) O₁) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => N₁ s g) O₁) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E₁ p.1 p.2) (O₁ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => N₁ p.1 p.2) (O₁ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        E₁ s g = φ₁ s g + ∑' ξ : K, φ₁ s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        N₁ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φ₁ s) g))
      (σ : ℝ) (μb νb : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hsw : μb = ν * NumberField.TateGlobal.normPowChar K σ ∧ νb = μ * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (_hμb : IsUnitaryChar (𝓞 K) K μb) (_hνb : IsUnitaryChar (𝓞 K) K νb)
      (_hμbic : IsIdeleClassChar (𝓞 K) K μb) (_hνbic : IsIdeleClassChar (𝓞 K) K νb)
      (_hμbc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μb z : ℂˣ) : ℂ))
      (_hνbc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((νb z : ℂˣ) : ℂ))
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μb αm hαm s) (etaSnd νb αm hαm s) (φE j s))
      (_hφEK : ∀ j s, IsArchKFinite K (φE j s))
      (_hφEf : ∀ j s, IsKfSmooth K (φE j s))
      (_hφEjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j p.1 p.2))
      (_hφEhol : ∀ j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE j s g))
      (_hφEKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE j s (g * u) = φE j s g)
      (_hφEty : ∀ j (s : ℂ), φE j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μb αm hαm ((t : ℂ) * Complex.I)) (etaSnd νb αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
      (OE : Fin n → Set ℂ) (EE NE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (j : Fin n),
      IsOpen (OE j) ∧ IsPreconnected (OE j) ∧ {s : ℂ | s.re = 0} ⊆ (OE j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE j s g) (OE j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE j s g) (OE j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE j s g = φE j s g + ∑' ξ : K, φE j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE j s) g))
      (t : ℝ) (g : AdelicGL2 (𝓞 K) K),
    ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * ∑ j' : Fin n,
        (∫ k, (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          NE j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g =
      φ₁ ((t : ℂ) * Complex.I) g :=
  Ws31.CtInversion.main K N hN tysK

end S_AutomorphicForm_inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
end P2MW
export P2MW.S_AutomorphicForm_inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar (solution)
