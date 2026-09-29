-- Prove2me | solution 1 for AutomorphicForm.integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1573cfda-e5f1-5268-a1b0-062e3639b2ad

import Theorems.Thm_AutomorphicForm_exists_forall_sum_setIntegral_norm_sq_rightConv_le_of_orthogonal_of_isCuspidalFn_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_injOn_forall_twistedConvOp_mem_isotypicCuspSubmodule_comp_unitsMap_inf_archCutSubmodule_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_rightConv_rightConv_inv_eq_rightConv_rightConv
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_PlaceTransport
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one"

set_option autoImplicit false

noncomputable section

namespace R4TCSigma

section

open scoped InnerProductSpace ComplexConjugate

namespace Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sq_sum_smul_eq_re {J : Type*} [Fintype J] (c : J → ℂ) (v : J → E) :
    ‖∑ j, c j • v j‖ ^ 2 = RCLike.re (∑ j, ∑ j', conj (c j) * c j' * ⟪v j, v j'⟫_ℂ) := by
  rw [@norm_sq_eq_re_inner ℂ, sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [inner_smul_left, inner_smul_right, mul_assoc]

theorem exists_orthonormalBasis_diag {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (s : V → V → ℂ)
    (hadd : ∀ φ φ' ψ, s (φ + φ') ψ = s φ ψ + s φ' ψ) (hsmul : ∀ (c : ℂ) φ ψ, s (c • φ) ψ = conj c * s φ ψ)
    (hconj : ∀ φ ψ, conj (s ψ φ) = s φ ψ) :
    ∃ d : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      (∀ p q, p ≠ q → s (d p) (d q) = 0) ∧ ∀ p, s (d p) (d p) = ((RCLike.re (s (d p) (d p)) : ℝ) : ℂ) := by
  classical

  have hadd' : ∀ φ ψ ψ', s φ (ψ + ψ') = s φ ψ + s φ ψ' := fun φ ψ ψ' => by
    rw [← hconj, hadd, map_add, hconj, hconj]
  have hsmul' : ∀ (c : ℂ) φ ψ, s φ (c • ψ) = c * s φ ψ := fun c φ ψ => by
    rw [← hconj, hsmul, map_mul, Complex.conj_conj, hconj]

  let b₀ := stdOrthonormalBasis ℂ V
  let G : V →ₗ[ℂ] V :=
    { toFun := fun v => ∑ q, s (b₀ q) v • b₀ q
      map_add' := fun v w => by
        simp only [hadd', add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [hsmul', RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have hG : ∀ w v : V, ⟪w, G v⟫_ℂ = s w v := by
    intro w v
    show ⟪w, ∑ q, s (b₀ q) v • b₀ q⟫_ℂ = s w v
    rw [inner_sum]
    conv_rhs => rw [← b₀.sum_repr' w]
    have hexp : s (∑ q, ⟪b₀ q, w⟫_ℂ • b₀ q) v = ∑ q, conj ⟪b₀ q, w⟫_ℂ * s (b₀ q) v := by
      have hzero : ∀ ψ, s 0 ψ = 0 := fun ψ => by
        have := hsmul 0 (0 : V) ψ
        rwa [zero_smul, map_zero, zero_mul] at this
      induction (Finset.univ : Finset (Fin (Module.finrank ℂ V))) using Finset.induction_on with
      | empty => simp [hzero]
      | insert q t hq ih => rw [Finset.sum_insert hq, Finset.sum_insert hq, hadd, hsmul, ih]
    rw [hexp]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_smul_right, inner_conj_symm, mul_comm]
  have hGsym : G.IsSymmetric := by
    intro v w
    rw [hG, ← inner_conj_symm, hG, hconj]
  refine ⟨hGsym.eigenvectorBasis rfl, fun p q hpq => ?_, fun p => ?_⟩
  · rw [← hG, hGsym.apply_eigenvectorBasis, inner_smul_right,
      orthonormal_iff_ite.1 (hGsym.eigenvectorBasis rfl).orthonormal p q, if_neg hpq, mul_zero]
  · have hval : s (hGsym.eigenvectorBasis rfl p) (hGsym.eigenvectorBasis rfl p) =
        ((hGsym.eigenvalues rfl p : ℝ) : ℂ) := by
      rw [← hG, hGsym.apply_eigenvectorBasis, inner_smul_right,
        orthonormal_iff_ite.1 (hGsym.eigenvectorBasis rfl).orthonormal p p, if_pos rfl, mul_one]
      try rfl
    rw [hval, RCLike.re_to_complex, Complex.ofReal_re]

end Abstract

end

section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace Mixed

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem integrable_mul_conj (a b : X → ℂ) (ha : MemLp a 2 ρ) (hb : MemLp b 2 ρ) :
    Integrable (fun x => a x * conj (b x)) ρ := by
  have ha' := (memLp_two_iff_integrable_sq_norm ha.1).1 ha
  have hb' := (memLp_two_iff_integrable_sq_norm hb.1).1 hb
  have hpt : ∀ x, ‖a x * conj (b x)‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have hm : AEStronglyMeasurable (fun x => a x * conj (b x)) ρ :=
    ha.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hb.1)
  exact Integrable.mono' ((ha'.add hb').div_const 2) hm (Filter.Eventually.of_forall hpt)

theorem integrable_and_integral_norm_sq_sum_smul {J : Type*} [Fintype J] [DecidableEq J]
    (φ : J → X → ℂ) (hφ : ∀ j, MemLp (φ j) 2 ρ) (v : J → E) (s : J → ℝ)
    (horth : ∀ j j', ∫ x, φ j x * conj (φ j' x) ∂ρ = if j = j' then ((s j : ℝ) : ℂ) else 0) :
    Integrable (fun x => ‖∑ j, conj (φ j x) • v j‖ ^ 2) ρ ∧
      ∫ x, ‖∑ j, conj (φ j x) • v j‖ ^ 2 ∂ρ = ∑ j, s j * ‖v j‖ ^ 2 := by
  have hint : ∀ j j', Integrable (fun x => φ j x * conj (φ j' x)) ρ := fun j j' => integrable_mul_conj _ _ (hφ j) (hφ j')

  set F : X → ℂ := fun x => ∑ j, ∑ j', φ j x * conj (φ j' x) * ⟪v j, v j'⟫_ℂ with hF
  have hFint : Integrable F ρ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => (hint j j').mul_const _
  have hpt : ∀ x, ‖∑ j, conj (φ j x) • v j‖ ^ 2 = RCLike.re (F x) := by
    intro x
    have h := Abstract.norm_sq_sum_smul_eq_re (fun j => conj (φ j x)) v
    simp only [Complex.conj_conj] at h
    exact h
  have hre : (fun x => ‖∑ j, conj (φ j x) • v j‖ ^ 2) = fun x => RCLike.re (F x) := funext hpt
  refine ⟨?_, ?_⟩
  · rw [hre]
    exact hFint.re
  · rw [hre, integral_re hFint, hF]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => (hint j j').mul_const _]
    have hj : ∀ j, ∫ x, ∑ j', φ j x * conj (φ j' x) * ⟪v j, v j'⟫_ℂ ∂ρ = ((s j * ‖v j‖ ^ 2 : ℝ) : ℂ) := by
      intro j
      rw [integral_finsetSum _ fun j' _ => (hint j j').mul_const _, Finset.sum_eq_single j]
      · have h3 : ⟪v j, v j⟫_ℂ = ((‖v j‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow]
          exact inner_self_eq_norm_sq_to_K (v j)
        rw [integral_mul_const, horth j j, if_pos rfl, h3]
        push_cast
        ring
      · intro j' _ hj'
        rw [integral_mul_const, horth j j', if_neg (Ne.symm hj'), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    simp only [hj]
    rw [← Complex.ofReal_sum, RCLike.re_to_complex, Complex.ofReal_re]

end Mixed

end

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate
open MeasureTheory.Measure
open scoped ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Venue

open AutomorphicForm NumberField.TateGlobal NumberField.AdelicVolume

variable (K : Type) [Field K] [NumberField K]

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

variable {K}

scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

theorem wt_continuous (σ : ℝ) : Continuous (wt K σ) :=
  Complex.continuous_ofReal.comp
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne')

theorem wt_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

theorem wt_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    min (α ^ (-σ)) (β ^ (-σ)) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hα.le h1 hs),
      (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ideleNorm_pos _) h2 hs.le),
      (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)⟩

theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

theorem det_centralScalar' (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z ^ 2 := by
  rw [show centralScalar (𝓞 K) K = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem normDet_central (c : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K c * x)) =
      ideleNorm K c ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, det_centralScalar', pow_two, ideleNorm_mul, pow_two]

theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

theorem exists_ideleNorm_eq (t : ℝ) (ht : 0 < t) : ∃ c : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K c = t := by
  obtain ⟨c, -, hc⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K t ht
  exact ⟨c, hc⟩

theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, normDet_global]
  exact Iff.rfl

scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

theorem smulInvariant_restrict (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict S) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ S = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, hS γ x]
  rw [hset, measure_preimage_mul]

theorem countable_K : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

theorem countable_Γ : Countable (Γ K) := by
  haveI := countable_K (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), x ∈ slab K α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurable α β))

theorem wt_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => by
    simp only [wt, Complex.norm_real, Real.norm_of_nonneg (wt_pos σ x).le]
    exact (wt_bounds α β σ hα x hx).2

def ven (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {φ | Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 ((μ K).restrict Φ₀)}
  zero_mem' := ⟨continuous_zero, ⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero'⟩
  add_mem' := by
    rintro φ ψ ⟨hφc, hφ, hφ₂⟩ ⟨hψc, hψ, hψ₂⟩
    exact ⟨hφc.add hψc,
      ⟨fun γ g => by simp only [Pi.add_apply, hφ.left_invariant, hψ.left_invariant],
        fun z g => by simp only [Pi.add_apply, hφ.central_transform, hψ.central_transform, mul_add]⟩,
      hφ₂.add hψ₂⟩
  smul_mem' := by
    rintro c φ ⟨hφc, hφ, hφ₂⟩
    exact ⟨hφc.const_smul c,
      ⟨fun γ g => by simp only [Pi.smul_apply, hφ.left_invariant],
        fun z g => by simp only [Pi.smul_apply, smul_eq_mul, hφ.central_transform]; ring⟩,
      hφ₂.const_smul c⟩

section Venue

variable (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hαβ : α < β) (hΦ₀ : Φ₀ ⊆ slab K α β)
  (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)

def Ven (_hα : 0 < α) (_hαβ : α < β) (_hΦ₀ : Φ₀ ⊆ slab K α β)
    (_hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) (σ : ℝ)
    (_hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ) : Type :=
  ↥(ven ξ Φ₀)

scoped instance : AddCommGroup (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  inferInstanceAs (AddCommGroup ↥(ven ξ Φ₀))

scoped instance : Module ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  inferInstanceAs (Module ℂ ↥(ven ξ Φ₀))

variable {α β hα hαβ Φ₀ hΦ₀ hFD ξ σ hσ}

def fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : AdelicGL2 (𝓞 K) K → ℂ := (φ : ↥(ven ξ Φ₀)).1

theorem fn_add (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (φ + ψ) = fn φ + fn ψ := rfl

theorem fn_smul (c : ℂ) (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (c • φ) = c • fn φ := rfl

theorem fn_zero : fn (0 : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) = 0 := rfl

theorem fn_sum {J : Type*} (s : Finset J) (φ : J → Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    fn (∑ j ∈ s, φ j) = ∑ j ∈ s, fn (φ j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, fn_add, ih]

theorem continuous_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : Continuous (fn φ) :=
  (φ : ↥(ven ξ Φ₀)).2.1

theorem isLsXiFunction_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : IsLsXiFunction (𝓞 K) K ⊤ ξ (fn φ) :=
  (φ : ↥(ven ξ Φ₀)).2.2.1

theorem memLp_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : MemLp (fn φ) 2 ((μ K).restrict Φ₀) :=
  (φ : ↥(ven ξ Φ₀)).2.2.2

theorem fn_injective : Function.Injective (fn : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ → _) :=
  fun _ _ h => Subtype.ext h

def pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : ℂ :=
  ∫ x in Φ₀, fn ψ x * conj (fn φ x) * wt K σ x ∂(μ K)

theorem integrable_pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    Integrable (fun x => fn ψ x * conj (fn φ x) * wt K σ x) ((μ K).restrict Φ₀) := by
  simpa only [mul_comm] using (Mixed.integrable_mul_conj (fn ψ) (fn φ) (memLp_fn ψ) (memLp_fn φ)).bdd_mul
    (wt_continuous σ).aestronglyMeasurable (wt_ae_bound α β σ hα Φ₀ hΦ₀)

theorem pair_add_left (φ φ' ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair (φ + φ') ψ = pair φ ψ + pair φ' ψ := by
  simp only [pair, fn_add, Pi.add_apply, map_add, mul_add, add_mul]
  exact integral_add (integrable_pair φ ψ) (integrable_pair φ' ψ)

theorem pair_smul_left (c : ℂ) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair (c • φ) ψ = conj c * pair φ ψ := by
  simp only [pair, fn_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

theorem conj_pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : conj (pair ψ φ) = pair φ ψ := by
  simp only [pair, ← integral_conj, map_mul, Complex.conj_conj, wt, Complex.conj_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

theorem pair_self_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair φ φ = ((∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) : ℝ) : ℂ) := by
  rw [pair, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [wt, Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_pow]

theorem re_pair_self_nonneg (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : 0 ≤ RCLike.re (pair φ φ) := by
  rw [pair_self_eq, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (wt_pos σ x).le

theorem forall_eq_zero_of_measure_inter_eq_zero (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (U : Set (AdelicGL2 (𝓞 K) K)) (hU : IsOpen U) (h : (μ K) ({x | f x ≠ 0} ∩ U) = 0) :
    ∀ x ∈ U, f x = 0 := by
  have hopen : IsOpen ({x | f x ≠ 0} ∩ U) := (isOpen_ne_fun hf continuous_const).inter hU
  have hempty := (hopen.measure_eq_zero_iff (μ := μ K)).1 h
  intro x hx
  by_contra hne
  have hmem : x ∈ {x | f x ≠ 0} ∩ U := ⟨hne, hx⟩
  rw [hempty] at hmem
  exact hmem

theorem eq_zero_of_pair_self_eq_zero (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) (h : pair φ φ = 0) :
    φ = 0 := by
  have h0 : ∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) = 0 := by
    have h' := pair_self_eq φ
    rw [h] at h'
    exact_mod_cast h'.symm
  have hint : Integrable (fun x => ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
      ((μ K).restrict Φ₀) := by
    have h2 := (memLp_two_iff_integrable_sq_norm (continuous_fn φ).aestronglyMeasurable).1 (memLp_fn φ)
    have hb : ∀ᵐ x ∂((μ K).restrict Φ₀),
        ‖ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
      (wt_ae_bound α β σ hα Φ₀ hΦ₀).mono fun x hx => by simpa only [wt, Complex.norm_real] using hx
    simpa only [mul_comm] using h2.bdd_mul
      ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne').aestronglyMeasurable hb
  have hae : ∀ᵐ x ∂((μ K).restrict Φ₀), fn φ x = 0 := by
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (sq_nonneg _) (wt_pos σ x).le) hint).1 h0
    filter_upwards [hz] with x hx
    have hx' : ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) = 0 := hx
    rcases mul_eq_zero.1 hx' with h1 | h1
    · exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
    · exact absurd h1 (wt_pos σ x).ne'
  obtain ⟨A, hA⟩ : ∃ A : Set (AdelicGL2 (𝓞 K) K), A = {x | fn φ x ≠ 0} := ⟨_, rfl⟩
  have hAopen : IsOpen A := by
    rw [hA]
    exact isOpen_ne_fun (continuous_fn φ) continuous_const
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  have hAΓ : ∀ γ : Γ K, γ • A = A := fun γ => by
    ext x
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Set.mem_smul_set_iff_inv_smul_mem, hA, Set.mem_setOf_eq, Set.mem_setOf_eq, Γ_smul]
    have hinv : ((γ⁻¹ : Γ K) : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀⁻¹ := by
      rw [Subgroup.coe_inv, hγ₀, map_inv]
    rw [hinv, (isLsXiFunction_fn φ).left_invariant]
  haveI : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) :=
    smulInvariant_restrict _ (slab_Γ_stable α β)
  haveI : Countable (Γ K) := countable_Γ
  have hAslab : (μ K).restrict (slab K α β) A = 0 := by
    refine hFD.measure_zero_of_invariant A hAΓ ?_
    have hμ : (μ K) (A ∩ Φ₀) = 0 := by
      rw [← Measure.restrict_apply hAmeas, hA]
      exact hae
    exact nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 Measure.restrict_le_self _).trans hμ.le)
  obtain ⟨U, hU⟩ : ∃ U : Set (AdelicGL2 (𝓞 K) K),
      U = {x | ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Ioo α β} := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_Ioo.preimage (continuous_ideleNorm_det K)
  have hUslab : U ⊆ slab K α β := by
    rw [hU]
    exact fun x hx => Set.Ioo_subset_Icc_self hx
  have hAU : (μ K) (A ∩ U) = 0 := by
    have hAs : (μ K) (A ∩ slab K α β) = 0 := by rwa [Measure.restrict_apply hAmeas] at hAslab
    exact measure_mono_null (Set.inter_subset_inter_right _ hUslab) hAs
  have hzeroU : ∀ x ∈ U, fn φ x = 0 := by
    refine forall_eq_zero_of_measure_inter_eq_zero (fn φ) (continuous_fn φ) U hUopen ?_
    rw [← hA]
    exact hAU
  have hall : ∀ g, fn φ g = 0 := by
    intro g
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (α + β) / 2 := ⟨_, rfl⟩
    have htα : α < t := by rw [ht]; linarith
    have htβ : t < β := by rw [ht]; linarith
    have ht0 : 0 < t := hα.trans htα
    have hdg : 0 < ideleNorm K (Matrix.GeneralLinearGroup.det g) := ideleNorm_pos _
    obtain ⟨c, hc⟩ := exists_ideleNorm_eq (K := K)
      (Real.sqrt (t / ideleNorm K (Matrix.GeneralLinearGroup.det g))) (Real.sqrt_pos.2 (div_pos ht0 hdg))
    have hmemU : centralScalar (𝓞 K) K c * g ∈ U := by
      rw [hU, Set.mem_setOf_eq, normDet_central, hc, Real.sq_sqrt (div_pos ht0 hdg).le,
        div_mul_cancel₀ _ hdg.ne']
      exact ⟨htα, htβ⟩
    have h1 := hzeroU _ hmemU
    have h2 := (isLsXiFunction_fn φ).central_transform ⟨c, Subgroup.mem_top c⟩ g
    change fn φ (centralScalar (𝓞 K) K c * g) = _ at h2
    rw [h1] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (Units.ne_zero _)
  exact fn_injective (funext hall)

@[reducible] def venCore : InnerProductSpace.Core ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) where
  inner := pair
  conj_inner_symm φ ψ := conj_pair φ ψ
  re_inner_nonneg φ := re_pair_self_nonneg φ
  add_left φ φ' ψ := pair_add_left φ φ' ψ
  smul_left φ ψ c := pair_smul_left c φ ψ
  definite φ h := eq_zero_of_pair_self_eq_zero φ h

scoped instance : NormedAddCommGroup (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ venCore

scoped instance : InnerProductSpace ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  InnerProductSpace.ofCore _

theorem norm_sq_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    ‖φ‖ ^ 2 = ∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) := by
  rw [@norm_sq_eq_re_inner ℂ]
  change RCLike.re (pair φ φ) = _
  rw [pair_self_eq, RCLike.re_to_complex, Complex.ofReal_re]

def uw (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : ℂ :=
  ∫ x in Φ₀, fn ψ x * conj (fn φ x) ∂(μ K)

theorem integrable_uw (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    Integrable (fun x => fn ψ x * conj (fn φ x)) ((μ K).restrict Φ₀) :=
  Mixed.integrable_mul_conj (fn ψ) (fn φ) (memLp_fn ψ) (memLp_fn φ)

theorem uw_add_left (φ φ' ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw (φ + φ') ψ = uw φ ψ + uw φ' ψ := by
  simp only [uw, fn_add, Pi.add_apply, map_add, mul_add]
  exact integral_add (integrable_uw φ ψ) (integrable_uw φ' ψ)

theorem uw_add_right (φ ψ ψ' : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw φ (ψ + ψ') = uw φ ψ + uw φ ψ' := by
  simp only [uw, fn_add, Pi.add_apply, add_mul]
  exact integral_add (integrable_uw φ ψ) (integrable_uw φ ψ')

theorem uw_smul_left (c : ℂ) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw (c • φ) ψ = conj c * uw φ ψ := by
  simp only [uw, fn_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

theorem uw_smul_right (c : ℂ) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw φ (c • ψ) = c * uw φ ψ := by
  simp only [uw, fn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem uw_zero_left (ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw 0 ψ = 0 := by
  simp only [uw, fn_zero, Pi.zero_apply, map_zero, mul_zero, integral_zero]

theorem uw_zero_right (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw φ 0 = 0 := by
  simp only [uw, fn_zero, Pi.zero_apply, zero_mul, integral_zero]

theorem conj_uw (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : conj (uw ψ φ) = uw φ ψ := by
  simp only [uw, ← integral_conj, map_mul, Complex.conj_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

theorem uw_self_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    uw φ φ = ((∫ x in Φ₀, ‖fn φ x‖ ^ 2 ∂(μ K) : ℝ) : ℂ) := by
  rw [uw, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_sq_le_mul_uw (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    ‖φ‖ ^ 2 ≤ max (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖fn φ x‖ ^ 2 ∂(μ K) := by
  have hsq : Integrable (fun x => ‖fn φ x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm (continuous_fn φ).aestronglyMeasurable).1 (memLp_fn φ)
  rw [norm_sq_eq, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hsq.const_mul _) ?_
  · exact mul_nonneg (sq_nonneg _) (wt_pos σ x).le
  filter_upwards [ae_mem_slab α β Φ₀ hΦ₀] with x hx
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (wt_bounds α β σ hα x hx).2 (sq_nonneg _)

theorem mul_uw_le_norm_sq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    min (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖fn φ x‖ ^ 2 ∂(μ K) ≤ ‖φ‖ ^ 2 := by
  have hsq : Integrable (fun x => ‖fn φ x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm (continuous_fn φ).aestronglyMeasurable).1 (memLp_fn φ)
  have hint : Integrable (fun x => ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
      ((μ K).restrict Φ₀) := by
    have hb : ∀ᵐ x ∂((μ K).restrict Φ₀),
        ‖ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
      (wt_ae_bound α β σ hα Φ₀ hΦ₀).mono fun x hx => by simpa only [wt, Complex.norm_real] using hx
    simpa only [mul_comm] using hsq.bdd_mul
      ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne').aestronglyMeasurable hb
  rw [norm_sq_eq, ← integral_const_mul]
  refine integral_mono_ae (hsq.const_mul _) hint ?_
  filter_upwards [ae_mem_slab α β Φ₀ hΦ₀] with x hx
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (wt_bounds α β σ hα x hx).1 (sq_nonneg _)

end Venue

scoped instance secondCountable_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

section Convolution

theorem continuous_rightConv_of_hasCompactSupport (u g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Continuous (rightConv K u g) := by
  have hconv : rightConv K u g = fun x => ∫ y, u (x * y) * g y ∂(μ K) := funext fun x => rightConv_apply K u g x
  rw [hconv, continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hNc.mul (hgc : IsCompact (tsupport g))).exists_bound_of_continuousOn huc.continuousOn
  refine continuousAt_of_dominated (bound := fun y => M * ‖g y‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((huc.comp (continuous_const.mul continuous_id)).mul hg).aestronglyMeasurable
  · refine Filter.eventually_of_mem hN fun x hx => Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport g
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mul_mem_mul hx hy)) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hg.norm.integrable_of_hasCompactSupport hgc.norm).const_mul M
  · exact Filter.Eventually.of_forall fun y =>
      ((huc.comp (continuous_id.mul continuous_const)).mul continuous_const).continuousAt

theorem isLsXiFunction_rightConv (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (u g : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) : IsLsXiFunction (𝓞 K) K ⊤ ξ (rightConv K u g) where
  left_invariant γ x := by simp only [rightConv, mul_assoc, hu.left_invariant]
  central_transform z x := by simp only [rightConv, mul_assoc, hu.central_transform, integral_const_mul]

theorem rightConv_add_left (u v g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hvc : Continuous v)
    (hg : Continuous g) (hgc : HasCompactSupport g) : rightConv K (u + v) g = rightConv K u g + rightConv K v g := by
  funext x
  simp only [rightConv, Pi.add_apply, add_mul]
  exact integral_add
    (((huc.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left)
    (((hvc.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left)

theorem rightConv_smul_left (c : ℂ) (u g : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K (c • u) g = c • rightConv K u g := by
  funext x
  simp only [rightConv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem flat_continuous (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) :
    Continuous (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) :=
  (Complex.continuous_conj.comp (hg.comp continuous_inv)).mul (wt_continuous σ)

theorem flat_hasCompactSupport (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) := by
  have h1 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => g y⁻¹) :=
    hgc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  have h2 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹)) :=
    h1.comp_left (map_zero (starRingEnd ℂ))
  exact h2.mul_right

end Convolution

section Operators

variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ slab K α β}
  {hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}

def convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ where
  toFun φ := show ↥(ven ξ Φ₀) from
    ⟨rightConv K (fn φ) g,
      continuous_rightConv_of_hasCompactSupport (fn φ) g (continuous_fn φ) hg hgc,
      isLsXiFunction_rightConv ξ (fn φ) g (isLsXiFunction_fn φ),
      (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn φ) (fn φ)
        (isLsXiFunction_fn φ) (isLsXiFunction_fn φ) (continuous_fn φ) (continuous_fn φ) (memLp_fn φ) (memLp_fn φ)
        g hg hgc).1⟩
  map_add' φ ψ := fn_injective (by
    change rightConv K (fn φ + fn ψ) g = rightConv K (fn φ) g + rightConv K (fn ψ) g
    exact rightConv_add_left (fn φ) (fn ψ) g (continuous_fn φ) (continuous_fn ψ) hg hgc)
  map_smul' c φ := fn_injective (by
    change rightConv K (c • fn φ) g = c • rightConv K (fn φ) g
    exact rightConv_smul_left c (fn φ) g)

theorem fn_convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (convOp g hg hgc φ) = rightConv K (fn φ) g := rfl

def convOpFlat (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ :=
  convOp (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) * ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))
    (flat_continuous σ g hg) (flat_hasCompactSupport σ g hgc)

theorem inner_convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (w v : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    @inner ℂ _ _ (convOp g hg hgc w) v = @inner ℂ _ _ w (convOpFlat g hg hgc v) := by
  have h : pair v (convOp g hg hgc w) = pair (convOpFlat g hg hgc v) w :=
    (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn w) (fn v)
      (isLsXiFunction_fn w) (isLsXiFunction_fn v) (continuous_fn w) (continuous_fn v) (memLp_fn w) (memLp_fn v)
      g hg hgc).2.2
  change pair (convOp g hg hgc w) v = pair w (convOpFlat g hg hgc v)
  rw [← conj_pair, h, conj_pair]

end Operators

end Venue
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate
open MeasureTheory.Measure
open scoped ENNReal
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ConvolutionAssociativity

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

private abbrev _root_.R4TCSigma.ConvolutionAssociativity.μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

p2m_export "R4TCSigma.ConvolutionAssociativity" "μ"
variable {K}

scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private theorem _root_.R4TCSigma.ConvolutionAssociativity.continuous_rightConv_of_hasCompactSupport (u g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Continuous (rightConv K u g) :=
  Venue.continuous_rightConv_of_hasCompactSupport u g huc hg hgc

p2m_export "R4TCSigma.ConvolutionAssociativity" "continuous_rightConv_of_hasCompactSupport"
theorem hasCompactSupport_rightConv_inv (g h : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h) : HasCompactSupport (rightConv K g fun y => h y⁻¹) := by
  refine HasCompactSupport.intro ((hgc : IsCompact (tsupport g)).mul (hhc : IsCompact (tsupport h))) fun x hx => ?_
  rw [rightConv_apply]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : h y⁻¹ = 0
  · simp [hy]
  have hgx : g (x * y) = 0 := by
    by_contra hgx
    apply hx
    have : x = x * y * y⁻¹ := by group
    rw [this]
    exact Set.mul_mem_mul (subset_tsupport g hgx) (subset_tsupport h hy)
  simp [hgx]

theorem rightConv_sum_right (u : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (F : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hF : ∀ k, Continuous (F k)) (hFc : ∀ k, HasCompactSupport (F k)) :
    rightConv K u (∑ k, F k) = ∑ k, rightConv K u (F k) := by
  funext x
  simp only [rightConv, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun k _ =>
    ((huc.comp (continuous_const.mul continuous_id)).mul (hF k)).integrable_of_hasCompactSupport (hFc k).mul_left

theorem rightConv_eq_sum_of_forall_eq_sum (u f : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (g h : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hg : ∀ k, Continuous (g k)) (hgc : ∀ k, HasCompactSupport (g k))
    (hh : ∀ k, Continuous (h k)) (hhc : ∀ k, HasCompactSupport (h k))
    (hf : ∀ x, f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x) :
    rightConv K u f = ∑ k, rightConv K (rightConv K u (h k)) (g k) := by
  have hf' : f = ∑ k, rightConv K (g k) fun y => h k y⁻¹ := by
    funext x
    rw [hf x, Finset.sum_apply]
  have hinvc : ∀ k, Continuous fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k => (hh k).comp continuous_inv
  have hinvcs : ∀ k, HasCompactSupport fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k =>
    (hhc k).comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  rw [hf', rightConv_sum_right u huc _
    (fun k => continuous_rightConv_of_hasCompactSupport (g k) _ (hg k) (hinvc k) (hinvcs k))
    (fun k => hasCompactSupport_rightConv_inv (g k) (h k) (hgc k) (hhc k))]
  exact Finset.sum_congr rfl fun k _ =>
    rightConv_rightConv_inv_eq_rightConv_rightConv K u (g k) (h k) huc (hg k) (hgc k) (hh k) (hhc k)

end ConvolutionAssociativity
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.ConvolutionAssociativity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.ConvolutionAssociativity"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate ENNReal
open MeasureTheory.Measure

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Transport

open AutomorphicForm NumberField.TateGlobal

variable {E : Type} [Field E] [NumberField E]

variable {F : Type} [Field F] [Algebra F E]

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

theorem sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)
    (τ : E ≃ₐ[F] E) (z : (AdeleRing (𝓞 E) E)ˣ) :
    sigmaAdelicAct F E D τ (centralScalar (𝓞 E) E z) =
      centralScalar (𝓞 E) E
        (Units.map ((D.act τ : RingAut (AdeleRing (𝓞 E) E)).toRingHom :
          AdeleRing (𝓞 E) E →* AdeleRing (𝓞 E) E) z) :=
  map_scalar (D.act τ : RingAut (AdeleRing (𝓞 E) E)).toRingHom z

theorem ideleNorm_unitsMap (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E) (σ : E ≃ₐ[F] E)
    (z : (AdeleRing (𝓞 E) E)ˣ) :
    ideleNorm E (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 E) E)).toRingHom :
        AdeleRing (𝓞 E) E →* AdeleRing (𝓞 E) E) z) = ideleNorm E z := by
  have h := AutomorphicForm.ideleNorm_det_sigmaAdelicAct F E D σ (centralScalar (𝓞 E) E z)
  rw [sigmaAdelicAct_centralScalar, Venue.det_centralScalar', Venue.det_centralScalar', pow_two, pow_two,
    ideleNorm_mul, ideleNorm_mul, ← pow_two, ← pow_two] at h
  exact (pow_left_inj₀ (ideleNorm_pos _).le (ideleNorm_pos _).le two_ne_zero).1 h

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.ConvolutionAssociativity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.ConvolutionAssociativity"
end R4TCSigma
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.ConvolutionAssociativity P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.Venue P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma.ConvolutionAssociativity P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab.R4TCSigma"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate InnerProductSpace ProbabilityTheory NumberField.PlaceTransport
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 9600000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφf : IsFactorizableTestFn L φ)
    (hφU : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (hφt : IsArchBiFinite L tysL φ) :
    (∀ i, IntegrableOn (fun x => twistedConvOp K L D σ φ (b i) x * conj (b i x)) Φ₀
        (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    Summable (fun Ψ : HeckeEigensystem L ℂ =>
      ∫ x in Φ₀, ‖∑ᶠ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖
        ∂adelicGLHaar (Fin 2) (𝓞 L) L) := by
  classical

  set P := productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L) with hP
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ

  set ξσ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ :=
    ξL.comp (Subgroup.topEquiv.symm.toMonoidHom.comp
      ((Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)).comp Subgroup.topEquiv.toMonoidHom)) with hξσ
  have ξσ_apply : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (hz : z ∈ (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)),
      ξσ ⟨z, hz⟩ = ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ := fun _ _ => rfl

  let W : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := fun Ψ =>
    isotypicCuspSubmodule L P ξL N SL Ψ ⊓ archCutSubmodule L tysL
  let W' : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := fun Θ =>
    isotypicCuspSubmodule L P ξσ N SL Θ ⊓ archCutSubmodule L tysL

  have hWin : ∀ (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (Θ : HeckeEigensystem L ℂ),
      ∀ u ∈ isotypicCuspSubmodule L P ξ' N SL Θ ⊓ archCutSubmodule L tysL,
      Continuous u ∧ IsLsXiFunction (𝓞 L) L ⊤ ξ' u ∧ MemLp u 2 (μ.restrict ΦL) ∧
      IsCuspidalFn ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) unipotentGL2 u := by
    intro ξ' Θ u hu
    have hu' := (Submodule.mem_inf.1 hu).1
    by_cases h0 : u = 0
    · subst h0
      exact ⟨continuous_const, isLsXiFunction_zero (𝓞 L) L ⊤ ξ', MemLp.zero, fun g => constantTerm_zero _ _ g⟩
    · have h := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L ΦL
        (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) ξ' N SL Θ u hu' h0
      obtain ⟨hl, h2⟩ := (lsXiMemberAt_iff (𝓞 L) L (adelicGLHaar (Fin 2) (𝓞 L) L) ⊤ ξ' ΦL u).1 h.smoothCusp.1.1
      exact ⟨h.continuous, hl, h2, h.smoothCusp.1.2⟩
  have hWf : ∀ Ψ, ∀ u ∈ W Ψ, Continuous u ∧ IsLsXiFunction (𝓞 L) L ⊤ ξL u ∧ MemLp u 2 (μ.restrict ΦL) ∧
      IsCuspidalFn ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) unipotentGL2 u := hWin ξL
  have hW'f : ∀ Θ, ∀ u ∈ W' Θ, Continuous u ∧ IsLsXiFunction (𝓞 L) L ⊤ ξσ u ∧ MemLp u 2 (μ.restrict ΦL) ∧
      IsCuspidalFn ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) unipotentGL2 u := hWin ξσ

  have hΦ₀' : Φ₀ ⊆ R4TCSigma.Venue.slab L α β := hΦ₀s
  have hFD₀' : IsFundamentalDomain (R4TCSigma.Venue.Γ L) Φ₀ ((R4TCSigma.Venue.μ L).restrict (R4TCSigma.Venue.slab L α β)) := hΦ₀
  have hisoσ := fun (u v : AdelicGL2 (𝓞 L) L → ℂ) hu hv hu₂ =>
    AutomorphicForm.memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab
      K L D σ α β ΦL Φ₀ hΦs hΦ hΦ₀s hΦ₀ u v hu hv hu₂

  have hmemΦ₀ : ∀ (u : AdelicGL2 (𝓞 L) L → ℂ),
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) x, u (globalPoints (𝓞 L) L γ * x) = u x) →
      MemLp u 2 (μ.restrict ΦL) → MemLp u 2 (μ.restrict Φ₀) := fun u hu h => (hisoσ u u hu hu h).1

  have hreal : ∀ (u : AdelicGL2 (𝓞 L) L → ℂ) (S : Set (AdelicGL2 (𝓞 L) L)),
      ∫ x in S, u x * conj (u x) ∂μ = 1 → ∫ x in S, ‖u x‖ ^ 2 ∂μ = 1 := by
    intro u S h
    have h2 : (fun x => u x * conj (u x)) = fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [h2, integral_complex_ofReal] at h
    exact_mod_cast h

  obtain ⟨T, hT, hTinj, hTblock⟩ :=
    AutomorphicForm.exists_injOn_forall_twistedConvOp_mem_isotypicCuspSubmodule_comp_unitsMap_inf_archCutSubmodule_of_isFundamentalDomain_slab
      K L D σ α β ΦL hΦs hΦ ξL SL hSL N hN tysL

  have hRW : ∀ Ψ : HeckeEigensystem L ℂ, Ψ.level = N → ∀ u ∈ W Ψ, twistedConvOp K L D σ φ u ∈ W' (T Ψ) :=
    fun Ψ hΨ u hu => hTblock Ψ hΨ φ hφ hφc hφU hφt u hu

  set c : ι → AdelicGL2 (𝓞 L) L → ℂ := fun i => sigmaSectionActOn K L D σ (b i) with hc
  have c_apply : ∀ i x, c i x = b i (sigmaAdelicAct K L D σ x) := fun i x => rfl
  have hA_eq : ∀ i, twistedConvOp K L D σ φ (b i) = rightConv L (c i) φ := fun i => twistedConvOp_apply K L D σ φ (b i)

  have hbne : ∀ i, b i ≠ 0 := by
    intro i h
    have h0 : (fun g => b i g * conj (b i g)) = fun _ => 0 := funext fun g => by rw [h, Pi.zero_apply, zero_mul]
    have := hb₁ i
    rw [h0, integral_zero] at this
    exact zero_ne_one this
  have hiso : ∀ i, IsIsotypicCuspFormAt L P ξL N SL (cls i) (b i) := fun i =>
    AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L ΦL
      (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w)
      ξL N SL (cls i) (b i) (Submodule.mem_inf.1 (hb i).2).1 (hbne i)
  have hcf : ∀ i, Continuous (c i) ∧ IsLsXiFunction (𝓞 L) L ⊤ ξσ (c i) ∧ MemLp (c i) 2 (μ.restrict ΦL) ∧
      IsCuspidalFn ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) unipotentGL2 (c i) := by
    intro i
    have h := AutomorphicForm.isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
      K L D σ α β ΦL hΦs hΦ ξL SL hSL N (cls i) (b i) (hiso i)
    obtain ⟨hl, h2⟩ := (lsXiMemberAt_iff (𝓞 L) L (adelicGLHaar (Fin 2) (𝓞 L) L) ⊤ _ ΦL _).1 h.smoothCusp.1.1
    exact ⟨h.continuous, hl, h2, h.smoothCusp.1.2⟩

  have hbl : ∀ i (γ : Matrix.GeneralLinearGroup (Fin 2) L) x, b i (globalPoints (𝓞 L) L γ * x) = b i x :=
    fun i => (hWf _ _ (hb i).2).2.1.left_invariant
  have hcl : ∀ i (γ : Matrix.GeneralLinearGroup (Fin 2) L) x, c i (globalPoints (𝓞 L) L γ * x) = c i x :=
    fun i => (hcf i).2.1.left_invariant
  have hbmem : ∀ i, MemLp (b i) 2 (μ.restrict ΦL) := fun i => (hWf _ _ (hb i).2).2.2.1

  have hbb : ∀ i j, ∫ x in Φ₀, b i x * conj (b j x) ∂μ = ∫ x in ΦL, b i x * conj (b j x) ∂μ :=
    fun i j => (hisoσ (b i) (b j) (hbl i) (hbl j) (hbmem i)).2.1
  have hcc : ∀ i j, ∫ x in Φ₀, c i x * conj (c j x) ∂μ = ∫ x in ΦL, b i x * conj (b j x) ∂μ :=
    fun i j => (hisoσ (b i) (b j) (hbl i) (hbl j) (hbmem i)).2.2
  have hcn : ∀ i, ∫ x in Φ₀, ‖c i x‖ ^ 2 ∂μ = 1 := fun i => hreal _ _ ((hcc i i).trans (hb₁ i))

  have hK2 : ∀ i, IntegrableOn (fun x => twistedConvOp K L D σ φ (b i) x * conj (b i x)) Φ₀ μ := by
    intro i
    have hlev : (cls i).level = N := (hb i).1.1
    have hmemW' := hRW (cls i) hlev (b i) (hb i).2
    have h1 : MemLp (twistedConvOp K L D σ φ (b i)) 2 (μ.restrict Φ₀) :=
      hmemΦ₀ _ (hW'f _ _ hmemW').2.1.left_invariant (hW'f _ _ hmemW').2.2.1
    have h2 : MemLp (b i) 2 (μ.restrict Φ₀) := hmemΦ₀ _ (hbl i) (hWf _ _ (hb i).2).2.2.1
    exact R4TCSigma.Mixed.integrable_mul_conj _ _ h1 h2
  refine ⟨hK2, ?_⟩

  have hfin : ∀ Ψ, {i | cls i = Ψ}.Finite := by
    intro Ψ
    by_cases hΨ : Ψ ∈ cuspClasses L P ξL N SL
    · exact (hbs Ψ hΨ).1
    · have he : {i | cls i = Ψ} = ∅ := Set.eq_empty_of_forall_notMem fun i hi => hΨ (hi ▸ (hb i).1)
      rw [he]
      exact Set.finite_empty
  letI instF : ∀ Ψ, Fintype {i // cls i = Ψ} := fun Ψ => (hfin Ψ).fintype

  have hfs : ∀ Ψ x, (∑ᶠ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)) =
      ∑ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x) := fun Ψ x => finsum_eq_sum_of_fintype _
  simp_rw [hfs]

  by_cases hι : IsEmpty ι
  · have hz : (fun Ψ : HeckeEigensystem L ℂ =>
        ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ∂μ) = 0 := by
      funext Ψ
      haveI : IsEmpty {i // cls i = Ψ} := ⟨fun i => hι.elim i.1⟩
      simp
    rw [hz]
    exact summable_zero

  obtain ⟨i₀⟩ := not_isEmpty_iff.1 hι
  have hb₀ne : ∃ g, b i₀ g ≠ 0 := by
    by_contra h
    exact hbne i₀ (funext fun g => by_contra fun hg => h ⟨g, hg⟩)
  obtain ⟨hprin, hcontχ⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous L ξL (b i₀)
      (hWf _ _ (hb i₀).2).2.1 (hWf _ _ (hb i₀).2).1 hb₀ne
  let μξ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp Subgroup.topEquiv.symm.toMonoidHom
  obtain ⟨s, hs'⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow L μξ (fun u => hprin u) hcontχ
  have hσ' : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ),
      ‖((ξσ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm L (z : (AdeleRing (𝓞 L) L)ˣ) ^ s := by
    rintro ⟨z, hz⟩
    rw [ξσ_apply, ← R4TCSigma.Transport.ideleNorm_unitsMap D σ z]
    exact hs' _
  have hN0 : N ≠ ⊥ := (hb i₀).1.1 ▸ (cls i₀).level_ne_bot

  obtain ⟨ι', b', cls', hb', hb'₁, hb'₀, hbs', -⟩ :=
    AutomorphicForm.exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
      L α β hα hαβ ΦL hΦs hΦ ξσ N hN0 SL hN tysL
  have hb'l : ∀ j (γ : Matrix.GeneralLinearGroup (Fin 2) L) x, b' j (globalPoints (𝓞 L) L γ * x) = b' j x :=
    fun j => (hW'f _ _ (hb' j).2).2.1.left_invariant

  let E : Type := R4TCSigma.Venue.Ven α β Φ₀ ξσ hα hαβ hΦ₀' hFD₀' s hσ'
  have hW'v : ∀ Θ, W' Θ ≤ R4TCSigma.Venue.ven ξσ Φ₀ := fun Θ u hu =>
    ⟨(hW'f Θ u hu).1, (hW'f Θ u hu).2.1, hmemΦ₀ u (hW'f Θ u hu).2.1.left_invariant (hW'f Θ u hu).2.2.1⟩

  let Cv : ι → E := fun i => show ↥(R4TCSigma.Venue.ven ξσ Φ₀) from
    ⟨c i, (hcf i).1, (hcf i).2.1, hmemΦ₀ _ (hcl i) (hcf i).2.2.1⟩
  have fn_Cv : ∀ i, R4TCSigma.Venue.fn (Cv i) = c i := fun i => rfl

  let B'v : ι' → E := fun j => show ↥(R4TCSigma.Venue.ven ξσ Φ₀) from ⟨b' j, hW'v _ (hb' j).2⟩
  have fn_B'v : ∀ j, R4TCSigma.Venue.fn (B'v j) = b' j := fun j => rfl

  set mw : ℝ := min (α ^ (-s)) (β ^ (-s)) with hmw
  set Mw : ℝ := max (α ^ (-s)) (β ^ (-s)) with hMw
  have hmw0 : 0 < mw := lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans hαβ) _)
  have hMw0 : 0 ≤ Mw := le_max_of_le_left (Real.rpow_nonneg hα.le _)

  obtain ⟨n, g, h, hg, hh, hfsum⟩ := exists_eq_sum_rightConv_of_isFactorizableTestFn L φ hφf
  have hgc : ∀ k, Continuous (g k) ∧ HasCompactSupport (g k) := fun k =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L (g k) (hg k)
  have hhc : ∀ k, Continuous (h k) ∧ HasCompactSupport (h k) := fun k =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L (h k) (hh k)
  let A : Fin n → E →ₗ[ℂ] E := fun k => R4TCSigma.Venue.convOp (g k) (hgc k).1 (hgc k).2
  let Adag : Fin n → E →ₗ[ℂ] E := fun k => R4TCSigma.Venue.convOpFlat (g k) (hgc k).1 (hgc k).2
  let Bop : Fin n → E →ₗ[ℂ] E := fun k => R4TCSigma.Venue.convOp (h k) (hhc k).1 (hhc k).2
  let TE : E →ₗ[ℂ] E := ∑ k, A k ∘ₗ Bop k
  have fn_TE : ∀ w : E, R4TCSigma.Venue.fn (TE w) = rightConv L (R4TCSigma.Venue.fn w) φ := by
    intro w
    show R4TCSigma.Venue.fn ((∑ k, A k ∘ₗ Bop k) w) = rightConv L (R4TCSigma.Venue.fn w) φ
    rw [LinearMap.sum_apply, R4TCSigma.Venue.fn_sum]
    rw [R4TCSigma.ConvolutionAssociativity.rightConv_eq_sum_of_forall_eq_sum _ φ (R4TCSigma.Venue.continuous_fn w) g h
      (fun k => (hgc k).1) (fun k => (hgc k).2) (fun k => (hhc k).1) (fun k => (hhc k).2) hfsum]
    exact Finset.sum_congr rfl fun k _ => rfl
  have TE_def : ∀ w : E, TE w = ∑ k, A k (Bop k w) := fun w => by
    show (∑ k, A k ∘ₗ Bop k) w = _
    rw [LinearMap.sum_apply]
    rfl
  have hadj : ∀ k (w v : E), ⟪A k w, v⟫_ℂ = ⟪w, Adag k v⟫_ℂ :=
    fun k w v => R4TCSigma.Venue.inner_convOp (g k) (hgc k).1 (hgc k).2 w v

  have hHS :=
    AutomorphicForm.exists_forall_sum_setIntegral_norm_sq_rightConv_le_of_orthogonal_of_isCuspidalFn_of_isFundamentalDomain_slab
      L α β hα hαβ Φ₀ hΦ₀s hΦ₀ ξσ s hσ'
  choose HB hHB using fun k => hHS (h k) (hh k)
  choose HA hHA using fun k => hHS (g k) (hg k)

  let V' : HeckeEigensystem L ℂ → Submodule ℂ E := fun Θ => (W' Θ).comap (R4TCSigma.Venue.ven ξσ Φ₀).subtype
  have mem_V' : ∀ Θ (w : E), w ∈ V' Θ ↔ R4TCSigma.Venue.fn w ∈ W' Θ := fun Θ w => Iff.rfl
  have hB'vV : ∀ j, B'v j ∈ V' (cls' j) := fun j => (hb' j).2
  have hfdW' : ∀ Θ ∈ cuspClasses L P ξσ N SL, FiniteDimensional ℂ (W' Θ) := by
    intro Θ hΘ
    have h := (hbs' Θ hΘ).2
    rw [show W' Θ = Submodule.span ℂ (b' '' {j | cls' j = Θ}) from h.symm]
    exact FiniteDimensional.span_of_finite ℂ ((hbs' Θ hΘ).1.image b')
  have hfdV' : ∀ Θ ∈ cuspClasses L P ξσ N SL, FiniteDimensional ℂ (V' Θ) := by
    intro Θ hΘ
    haveI := hfdW' Θ hΘ
    exact LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (hW'v Θ)).symm
  have hdiag : ∀ Θ (hΘ : Θ ∈ cuspClasses L P ξσ N SL),
      ∃ d : OrthonormalBasis (Fin (Module.finrank ℂ (V' Θ))) ℂ (V' Θ),
        (∀ p q, p ≠ q → R4TCSigma.Venue.uw ((d p : V' Θ) : E) ((d q : V' Θ) : E) = 0) ∧
        ∀ p, R4TCSigma.Venue.uw ((d p : V' Θ) : E) ((d p : V' Θ) : E) =
          ((RCLike.re (R4TCSigma.Venue.uw ((d p : V' Θ) : E) ((d p : V' Θ) : E)) : ℝ) : ℂ) := by
    intro Θ hΘ
    haveI := hfdV' Θ hΘ
    exact R4TCSigma.Abstract.exists_orthonormalBasis_diag (V := V' Θ)
      (fun v w => R4TCSigma.Venue.uw (v : E) (w : E))
      (fun φ φ' ψ => by beta_reduce; rw [Submodule.coe_add]; exact R4TCSigma.Venue.uw_add_left _ _ _)
      (fun c φ ψ => by beta_reduce; rw [Submodule.coe_smul]; exact R4TCSigma.Venue.uw_smul_left _ _ _)
      (fun φ ψ => R4TCSigma.Venue.conj_uw _ _)

  have key : ∀ (Ψ : HeckeEigensystem L ℂ) (hΨ : Ψ ∈ cuspClasses L P ξL N SL)
      (hΘ : T Ψ ∈ cuspClasses L P ξσ N SL)
      (d : OrthonormalBasis (Fin (Module.finrank ℂ (V' (T Ψ)))) ℂ (V' (T Ψ)))
      (hd0 : ∀ p q, p ≠ q → R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d q : V' (T Ψ)) : E) = 0)
      (hd1 : ∀ p, R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d p : V' (T Ψ)) : E) =
          ((RCLike.re (R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d p : V' (T Ψ)) : E)) : ℝ) : ℂ)),
      ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ∂μ ≤
        ∑ k, (mw⁻¹ * ∑ p, ‖Adag k ((d p : V' (T Ψ)) : E)‖ ^ 2 + ∑ i : {i // cls i = Ψ}, ‖Bop k (Cv i)‖ ^ 2) / 2 := by
    intro Ψ hΨ hΘ d hd0 hd1
    haveI := hfdV' (T Ψ) hΘ

    let ex : AdelicGL2 (𝓞 L) L → E := fun x => ∑ i : {i // cls i = Ψ}, conj (b i x) • Cv i
    let rx : AdelicGL2 (𝓞 L) L → E := fun x => ∑ p, conj (R4TCSigma.Venue.fn ((d p : V' (T Ψ)) : E) x) • ((d p : V' (T Ψ)) : E)
    have ex_def : ∀ x, ex x = ∑ i : {i // cls i = Ψ}, conj (b i x) • Cv i := fun x => rfl
    have rx_def : ∀ x, rx x = ∑ p, conj (R4TCSigma.Venue.fn ((d p : V' (T Ψ)) : E) x) • ((d p : V' (T Ψ)) : E) :=
      fun x => rfl

    have hexW : ∀ x, (∑ i : {i // cls i = Ψ}, conj (b i x) • b (i : ι)) ∈ W Ψ := fun x => by
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have h := (hb i.1).2
      rw [i.2] at h
      exact h
    have hfnex : ∀ x, R4TCSigma.Venue.fn (ex x) =
        sigmaSectionActOn K L D σ (∑ i : {i // cls i = Ψ}, conj (b i x) • b (i : ι)) := by
      intro x
      rw [ex_def, R4TCSigma.Venue.fn_sum]
      funext y
      show (∑ i : {i // cls i = Ψ}, R4TCSigma.Venue.fn (conj (b i x) • Cv i)) y =
        (∑ i : {i // cls i = Ψ}, conj (b i x) • b (i : ι)) (sigmaAdelicAct K L D σ y)
      rw [Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [R4TCSigma.Venue.fn_smul, Pi.smul_apply, Pi.smul_apply, fn_Cv, c_apply]
    have hTexV : ∀ x, TE (ex x) ∈ V' (T Ψ) := fun x => by
      rw [mem_V', fn_TE, hfnex, ← twistedConvOp_apply]
      exact hRW Ψ hΨ.1 _ (hexW x)

    have hrep : ∀ (w : E), w ∈ V' (T Ψ) → ∀ x, R4TCSigma.Venue.fn w x = ⟪rx x, w⟫_ℂ := by
      intro w hw x
      rw [rx_def, sum_inner]
      have hsum : (∑ p, ⟪d p, (⟨w, hw⟩ : V' (T Ψ))⟫_ℂ • d p) = (⟨w, hw⟩ : V' (T Ψ)) := d.sum_repr' _
      have hsum' : (∑ p, ⟪((d p : V' (T Ψ)) : E), w⟫_ℂ • ((d p : V' (T Ψ)) : E)) = w := by
        have := congrArg (fun v : V' (T Ψ) => (v : E)) hsum
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, Submodule.coe_mk] using this
      conv_lhs => rw [← hsum']
      rw [R4TCSigma.Venue.fn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [R4TCSigma.Venue.fn_smul, Pi.smul_apply, smul_eq_mul, inner_smul_left, Complex.conj_conj, mul_comm]

    have hker : ∀ x, (∑ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)) =
        R4TCSigma.Venue.fn (TE (ex x)) x := by
      intro x
      rw [ex_def, map_sum, R4TCSigma.Venue.fn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, R4TCSigma.Venue.fn_smul, Pi.smul_apply, smul_eq_mul, fn_TE, fn_Cv, hA_eq, mul_comm]

    have hpt : ∀ x, ‖∑ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ≤
        ∑ k, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex x)‖ ^ 2) / 2 := by
      intro x
      rw [hker x, hrep _ (hTexV x) x, TE_def, inner_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [← inner_conj_symm, hadj, inner_conj_symm]
      calc ‖⟪Adag k (rx x), Bop k (ex x)⟫_ℂ‖ ≤ ‖Adag k (rx x)‖ * ‖Bop k (ex x)‖ := norm_inner_le_norm _ _
        _ ≤ (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex x)‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖Adag k (rx x)‖ - ‖Bop k (ex x)‖), norm_nonneg (Adag k (rx x)),
              norm_nonneg (Bop k (ex x))]

    have hB : ∀ k, Integrable (fun x => ‖Bop k (ex x)‖ ^ 2) (μ.restrict Φ₀) ∧
        ∫ x in Φ₀, ‖Bop k (ex x)‖ ^ 2 ∂μ = ∑ i : {i // cls i = Ψ}, ‖Bop k (Cv i)‖ ^ 2 := by
      intro k
      have hmap : ∀ x, Bop k (ex x) = ∑ i : {i // cls i = Ψ}, conj (b i x) • Bop k (Cv i) := fun x => by
        rw [ex_def, map_sum]
        exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
      simp_rw [hmap]
      have h := R4TCSigma.Mixed.integrable_and_integral_norm_sq_sum_smul (ρ := μ.restrict Φ₀)
        (fun i : {i // cls i = Ψ} => b i) (fun i => hmemΦ₀ _ (hbl i) (hWf _ _ (hb i).2).2.2.1)
        (fun i => Bop k (Cv i)) (fun _ => 1)
        (fun i j => by
          by_cases hij : i = j
          · subst hij
            rw [if_pos rfl, hbb, hb₁]
            simp
          · rw [if_neg hij, hbb, hb₀ _ _ fun h' => hij (Subtype.ext h')])
      simpa only [one_mul] using h

    have hA : ∀ k, Integrable (fun x => ‖Adag k (rx x)‖ ^ 2) (μ.restrict Φ₀) ∧
        ∫ x in Φ₀, ‖Adag k (rx x)‖ ^ 2 ∂μ ≤ mw⁻¹ * ∑ p, ‖Adag k ((d p : V' (T Ψ)) : E)‖ ^ 2 := by
      intro k
      have hmap : ∀ x, Adag k (rx x) =
          ∑ p, conj (R4TCSigma.Venue.fn ((d p : V' (T Ψ)) : E) x) • Adag k ((d p : V' (T Ψ)) : E) := fun x => by
        rw [rx_def, map_sum]
        exact Finset.sum_congr rfl fun p _ => map_smul _ _ _
      simp_rw [hmap]
      have h := R4TCSigma.Mixed.integrable_and_integral_norm_sq_sum_smul (ρ := μ.restrict Φ₀)
        (fun p => R4TCSigma.Venue.fn ((d p : V' (T Ψ)) : E)) (fun p => R4TCSigma.Venue.memLp_fn _)
        (fun p => Adag k ((d p : V' (T Ψ)) : E))
        (fun p => RCLike.re (R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d p : V' (T Ψ)) : E)))
        (fun p q => by
          by_cases hpq : p = q
          · subst hpq
            rw [if_pos rfl]
            exact hd1 p
          · rw [if_neg hpq]
            exact hd0 q p (Ne.symm hpq))
      refine ⟨h.1, ?_⟩
      rw [h.2, Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      beta_reduce
      have h1 : RCLike.re (R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d p : V' (T Ψ)) : E)) =
          ∫ x in Φ₀, ‖R4TCSigma.Venue.fn ((d p : V' (T Ψ)) : E) x‖ ^ 2 ∂μ := by
        rw [R4TCSigma.Venue.uw_self_eq, RCLike.re_to_complex, Complex.ofReal_re]
      have h2 : mw * ∫ x in Φ₀, ‖R4TCSigma.Venue.fn ((d p : V' (T Ψ)) : E) x‖ ^ 2 ∂μ ≤ ‖((d p : V' (T Ψ)) : E)‖ ^ 2 :=
        R4TCSigma.Venue.mul_uw_le_norm_sq _
      have h3 : ‖((d p : V' (T Ψ)) : E)‖ = 1 := d.orthonormal.1 p
      rw [h3, one_pow] at h2
      rw [h1]
      have hX : (∫ x in Φ₀, ‖R4TCSigma.Venue.fn ((d p : V' (T Ψ)) : E) x‖ ^ 2 ∂μ) ≤ mw⁻¹ := by
        have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hmw0.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hmw0.ne', one_mul, mul_one] at this
      exact mul_le_mul_of_nonneg_right hX (sq_nonneg _)

    have hLint : Integrable (fun x => ‖∑ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖)
        (μ.restrict Φ₀) :=
      (integrable_finsetSum (Finset.univ : Finset {i // cls i = Ψ}) fun i _ => hK2 i).norm
    have hRint : Integrable (fun x => ∑ k, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex x)‖ ^ 2) / 2) (μ.restrict Φ₀) := by
      refine integrable_finsetSum _ fun k _ => Integrable.div_const ?_ 2
      exact (hA k).1.add (hB k).1
    calc ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ∂μ
        ≤ ∫ x in Φ₀, ∑ k, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex x)‖ ^ 2) / 2 ∂μ := by
          refine integral_mono hLint hRint fun x => ?_
          exact hpt x
      _ = ∑ k, ∫ x in Φ₀, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex x)‖ ^ 2) / 2 ∂μ :=
          integral_finsetSum _ fun k _ => Integrable.div_const ((hA k).1.add (hB k).1) 2
      _ = ∑ k, (∫ x in Φ₀, ‖Adag k (rx x)‖ ^ 2 ∂μ + ∫ x in Φ₀, ‖Bop k (ex x)‖ ^ 2 ∂μ) / 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_div, integral_add (hA k).1 (hB k).1]
      _ ≤ ∑ k, (mw⁻¹ * ∑ p, ‖Adag k ((d p : V' (T Ψ)) : E)‖ ^ 2 + ∑ i : {i // cls i = Ψ}, ‖Bop k (Cv i)‖ ^ 2) / 2 := by
          refine Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right ?_ two_pos.le
          rw [(hB k).2]
          exact add_le_add (hA k).2 le_rfl

  set S₁ : Set (HeckeEigensystem L ℂ) := {Ψ | Ψ ∈ cuspClasses L P ξL N SL ∧ T Ψ ∈ cuspClasses L P ξσ N SL}
    with hS₁

  have hdiag' : ∀ Ψ : ↥S₁,
      ∃ d : OrthonormalBasis (Fin (Module.finrank ℂ (V' (T Ψ)))) ℂ (V' (T Ψ)),
        (∀ p q, p ≠ q → R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d q : V' (T Ψ)) : E) = 0) ∧
        ∀ p, R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d p : V' (T Ψ)) : E) =
          ((RCLike.re (R4TCSigma.Venue.uw ((d p : V' (T Ψ)) : E) ((d p : V' (T Ψ)) : E)) : ℝ) : ℂ) :=
    fun Ψ => hdiag (T Ψ.1) Ψ.2.2
  choose d hd0 hd1 using hdiag'

  have hV'span : ∀ Θ ∈ cuspClasses L P ξσ N SL,
      V' Θ ≤ Submodule.span ℂ (Set.range fun j : {j // cls' j = Θ} => B'v j) := by
    intro Θ hΘ w hw
    have hfnw : R4TCSigma.Venue.fn w ∈ Submodule.span ℂ (b' '' {j | cls' j = Θ}) := by
      rw [(hbs' Θ hΘ).2]
      exact hw
    have himg : b' '' {j | cls' j = Θ} = (R4TCSigma.Venue.ven ξσ Φ₀).subtype '' (Set.range fun j : {j // cls' j = Θ} => B'v j) := by
      ext u
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨B'v j, ⟨⟨j, hj⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        exact ⟨j.1, j.2, rfl⟩
    rw [himg, ← Submodule.map_span] at hfnw
    obtain ⟨w', hw', hww⟩ := hfnw
    have : w' = w := R4TCSigma.Venue.fn_injective hww
    exact this ▸ hw'
  have huwB'v : ∀ j j', cls' j ≠ cls' j' → R4TCSigma.Venue.uw (B'v j) (B'v j') = 0 := by
    intro j j' hjj
    show ∫ x in Φ₀, b' j' x * conj (b' j x) ∂(R4TCSigma.Venue.μ L) = 0
    rw [(hisoσ (b' j') (b' j) (hb'l j') (hb'l j) (hW'f _ _ (hb' j').2).2.2.1).2.1]
    exact hb'₀ j' j fun h => hjj (h ▸ rfl)
  have hcross : ∀ (Θ Θ' : HeckeEigensystem L ℂ), Θ ∈ cuspClasses L P ξσ N SL → Θ' ∈ cuspClasses L P ξσ N SL →
      Θ ≠ Θ' → ∀ w ∈ V' Θ, ∀ w' ∈ V' Θ', R4TCSigma.Venue.uw w w' = 0 := by
    intro Θ Θ' hΘ hΘ' hne w hw w' hw'
    have hw1 := hV'span Θ hΘ hw
    have hw2 := hV'span Θ' hΘ' hw'
    refine Submodule.span_induction (p := fun w' _ => R4TCSigma.Venue.uw w w' = 0) ?_ ?_ ?_ ?_ hw2
    · rintro _ ⟨j, rfl⟩
      refine Submodule.span_induction (p := fun w _ => R4TCSigma.Venue.uw w (B'v j) = 0) ?_ ?_ ?_ ?_ hw1
      · rintro _ ⟨i, rfl⟩
        exact huwB'v i j (by rw [i.2, j.2]; exact hne)
      · exact R4TCSigma.Venue.uw_zero_left _
      · intro u u' _ _ hu hu'
        exact (R4TCSigma.Venue.uw_add_left _ _ _).trans (by rw [hu, hu', add_zero])
      · intro c u _ hu
        exact (R4TCSigma.Venue.uw_smul_left _ _ _).trans (by rw [hu, mul_zero])
    · exact R4TCSigma.Venue.uw_zero_right _
    · intro u u' _ _ hu hu'
      exact (R4TCSigma.Venue.uw_add_right _ _ _).trans (by rw [hu, hu', add_zero])
    · intro c u _ hu
      exact (R4TCSigma.Venue.uw_smul_right _ _ _).trans (by rw [hu, mul_zero])

  have hnorm_conv : ∀ (u : AdelicGL2 (𝓞 L) L → ℂ) (hu : Continuous u) (huc : HasCompactSupport u) (w : E),
      ‖R4TCSigma.Venue.convOp u hu huc w‖ ^ 2 ≤
        Mw * ∫ x in Φ₀, ‖rightConv L (R4TCSigma.Venue.fn w) u x‖ ^ 2 ∂μ := fun u hu huc w =>
    R4TCSigma.Venue.norm_sq_le_mul_uw _

  set Bound : ℝ := ∑ k : Fin n, (mw⁻¹ * (Mw * (mw⁻¹ * HA k)) + Mw * HB k) / 2 with hBound
  have hpartial : ∀ t : Finset ↥S₁,
      ∑ Ψ ∈ t, ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ∂μ ≤ Bound := by
    intro t

    let JB : Type := Σ Ψ : ↥t, {i // cls i = Ψ.1.1}
    let JA : Type := Σ Ψ : ↥t, Fin (Module.finrank ℂ (V' (T Ψ.1.1)))

    let eB : JB → AdelicGL2 (𝓞 L) L → ℂ := fun j => c j.2.1

    let cA : ℂ := ((Real.sqrt mw : ℝ) : ℂ)
    let eA : JA → AdelicGL2 (𝓞 L) L → ℂ := fun j => cA • R4TCSigma.Venue.fn ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)
    have eB_def : ∀ j, eB j = c j.2.1 := fun j => rfl
    have eA_def : ∀ j, eA j = cA • R4TCSigma.Venue.fn ((d j.1.1 j.2 : V' (T j.1.1.1)) : E) := fun j => rfl

    let σB := (Fintype.equivFin JB).symm
    let σA := (Fintype.equivFin JA).symm

    have hinjB : ∀ j j' : JB, j.2.1 = j'.2.1 → j = j' := by
      rintro ⟨⟨Ψ, hΨ⟩, ⟨i, hi⟩⟩ ⟨⟨Ψ', hΨ'⟩, ⟨i', hi'⟩⟩ (hii : i = i')
      subst hii
      have : Ψ = Ψ' := Subtype.ext (hi.symm.trans hi')
      subst this
      rfl
    have huwA : ∀ j j' : JA, j ≠ j' →
        R4TCSigma.Venue.uw ((d j'.1.1 j'.2 : V' (T j'.1.1.1)) : E) ((d j.1.1 j.2 : V' (T j.1.1.1)) : E) = 0 := by
      rintro ⟨Ψ, p⟩ ⟨Ψ', p'⟩ hne
      by_cases hΨ : Ψ = Ψ'
      · subst hΨ
        have hpp : p' ≠ p := fun h => hne (by rw [h])
        exact hd0 Ψ.1 p' p hpp
      ·
        have hTne : T Ψ'.1.1 ≠ T Ψ.1.1 := fun h =>
          hΨ (Subtype.ext (Subtype.ext (hTinj Ψ'.1.2.1 Ψ.1.2.1 h).symm))
        exact hcross (T Ψ'.1.1) (T Ψ.1.1) Ψ'.1.2.2 Ψ.1.2.2 hTne _ (d Ψ'.1 p').2 _ (d Ψ.1 p).2

    have hBsum : ∀ k, ∑ j : JB, ‖Bop k (Cv j.2.1)‖ ^ 2 ≤ Mw * HB k := by
      intro k
      have h1 : ∀ j : JB, ‖Bop k (Cv j.2.1)‖ ^ 2 ≤ Mw * ∫ x in Φ₀, ‖rightConv L (eB j) (h k) x‖ ^ 2 ∂μ :=
        fun j => hnorm_conv (h k) (hhc k).1 (hhc k).2 (Cv j.2.1)
      have h2 : ∑ m : Fin (Fintype.card JB), ∫ x in Φ₀, ‖rightConv L (eB (σB m)) (h k) x‖ ^ 2 ∂μ ≤ HB k := by
        refine (hHB k _ (fun m => eB (σB m)) (fun m => (hcf _).1) (fun m => (hcf _).2.1)
          (fun m => (hcf _).2.2.2) (fun m => hmemΦ₀ _ (hcl _) (hcf _).2.2.1) (fun m m' hmm => ?_) (fun m => ?_)).1
        · show ∫ x in Φ₀, c (σB m).2.1 x * conj (c (σB m').2.1 x) ∂μ = 0
          rw [hcc]
          exact hb₀ _ _ fun heq => hmm (σB.injective (hinjB _ _ heq))
        · exact (hcn (σB m).2.1).le
      calc ∑ j : JB, ‖Bop k (Cv j.2.1)‖ ^ 2
          ≤ ∑ j : JB, Mw * ∫ x in Φ₀, ‖rightConv L (eB j) (h k) x‖ ^ 2 ∂μ := Finset.sum_le_sum fun j _ => h1 j
        _ = Mw * ∑ j : JB, ∫ x in Φ₀, ‖rightConv L (eB j) (h k) x‖ ^ 2 ∂μ := (Finset.mul_sum _ _ _).symm
        _ = Mw * ∑ m : Fin (Fintype.card JB), ∫ x in Φ₀, ‖rightConv L (eB (σB m)) (h k) x‖ ^ 2 ∂μ := by
            rw [← Equiv.sum_comp σB]
        _ ≤ Mw * HB k := mul_le_mul_of_nonneg_left h2 hMw0

    have hAsum : ∀ k, ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)‖ ^ 2 ≤ Mw * (mw⁻¹ * HA k) := by
      intro k
      have hcA : cA * conj cA = ((mw : ℝ) : ℂ) := by
        show ((Real.sqrt mw : ℝ) : ℂ) * conj ((Real.sqrt mw : ℝ) : ℂ) = _
        rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hmw0.le]
      have hcA2 : ‖cA‖ ^ 2 = mw := by
        show ‖((Real.sqrt mw : ℝ) : ℂ)‖ ^ 2 = mw
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hmw0.le]
      have h1 : ∀ j : JA, ‖Adag k ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)‖ ^ 2 ≤
          Mw * (mw⁻¹ * ∫ x in Φ₀, ‖rightConv L (eA j) (fun y => conj (g k y⁻¹) *
            ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) := by
        intro j
        have h := hnorm_conv _ (R4TCSigma.Venue.flat_continuous s (g k) (hgc k).1)
          (R4TCSigma.Venue.flat_hasCompactSupport s (g k) (hgc k).2) ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)
        refine h.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hMw0)
        have hsm : rightConv L (eA j) (fun y => conj (g k y⁻¹) *
            ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) =
            cA • rightConv L (R4TCSigma.Venue.fn ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) :=
          R4TCSigma.Venue.rightConv_smul_left cA _ _
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hcA2]
        rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hmw0.ne', one_mul]
      have h2 : ∑ m : Fin (Fintype.card JA), ∫ x in Φ₀, ‖rightConv L (eA (σA m)) (fun y => conj (g k y⁻¹) *
            ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ ≤ HA k := by
        have hmemA : ∀ j : JA, R4TCSigma.Venue.fn ((d j.1.1 j.2 : V' (T j.1.1.1)) : E) ∈ W' (T j.1.1.1) :=
          fun j => (mem_V' _ _).1 (d j.1.1 j.2).2
        refine (hHA k _ (fun m => eA (σA m))
          (fun m => by beta_reduce; rw [eA_def]; exact (hW'f _ _ (hmemA (σA m))).1.const_smul cA)
          (fun m => ?_) (fun m => ?_)
          (fun m => by beta_reduce; rw [eA_def]; exact (R4TCSigma.Venue.memLp_fn _).const_smul cA)
          (fun m m' hmm => ?_) (fun m => ?_)).2
        ·
          have hl := (hW'f _ _ (hmemA (σA m))).2.1
          exact ⟨fun γ x => by beta_reduce; rw [eA_def]; simp only [Pi.smul_apply, hl.left_invariant],
            fun z x => by
              beta_reduce; rw [eA_def]; simp only [Pi.smul_apply, smul_eq_mul, hl.central_transform]; ring⟩
        ·
          beta_reduce
          have hz := (hW'f _ _ (hmemA (σA m))).2.2.2
          intro x
          have h1 := hz x
          have hsplit : constantTermIntegrand unipotentGL2 (eA (σA m)) x =
              fun q => cA * constantTermIntegrand unipotentGL2
                (R4TCSigma.Venue.fn ((d (σA m).1.1 (σA m).2 : V' (T (σA m).1.1.1)) : E)) x q :=
            rfl
          unfold constantTerm at h1 ⊢
          rw [hsplit, integral_const_mul, h1, mul_zero]
        ·
          have huw : R4TCSigma.Venue.uw ((d (σA m').1.1 (σA m').2 : V' (T (σA m').1.1.1)) : E)
              ((d (σA m).1.1 (σA m).2 : V' (T (σA m).1.1.1)) : E) = 0 :=
            huwA (σA m) (σA m') fun heq => hmm (σA.injective heq)
          show ∫ x in Φ₀, eA (σA m) x * conj (eA (σA m') x) ∂μ = 0
          have : (fun x => eA (σA m) x * conj (eA (σA m') x)) = fun x => (cA * conj cA) *
              (R4TCSigma.Venue.fn ((d (σA m).1.1 (σA m).2 : V' (T (σA m).1.1.1)) : E) x *
                conj (R4TCSigma.Venue.fn ((d (σA m').1.1 (σA m').2 : V' (T (σA m').1.1.1)) : E) x)) := by
            funext x
            simp only [eA_def, Pi.smul_apply, smul_eq_mul, map_mul]
            ring
          rw [this, integral_const_mul]
          change cA * conj cA * R4TCSigma.Venue.uw _ _ = 0
          rw [huw, mul_zero]
        ·
          beta_reduce
          have hint2 : ∫ x in Φ₀, ‖eA (σA m) x‖ ^ 2 ∂μ =
              mw * ∫ x in Φ₀, ‖R4TCSigma.Venue.fn ((d (σA m).1.1 (σA m).2 : V' (T (σA m).1.1.1)) : E) x‖ ^ 2 ∂μ := by
            simp only [eA_def, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hcA2]
            exact integral_const_mul _ _
          rw [hint2]
          have h2 := R4TCSigma.Venue.mul_uw_le_norm_sq ((d (σA m).1.1 (σA m).2 : V' (T (σA m).1.1.1)) : E)
          have h3 : ‖((d (σA m).1.1 (σA m).2 : V' (T (σA m).1.1.1)) : E)‖ = 1 := (d (σA m).1.1).orthonormal.1 _
          rw [h3, one_pow] at h2
          exact h2
      calc ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)‖ ^ 2
          ≤ ∑ j : JA, Mw * (mw⁻¹ * ∫ x in Φ₀, ‖rightConv L (eA j) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) :=
            Finset.sum_le_sum fun j _ => h1 j
        _ = Mw * (mw⁻¹ * ∑ j : JA, ∫ x in Φ₀, ‖rightConv L (eA j) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ = Mw * (mw⁻¹ * ∑ m : Fin (Fintype.card JA), ∫ x in Φ₀, ‖rightConv L (eA (σA m)) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) := by
            rw [← Equiv.sum_comp σA]
        _ ≤ Mw * (mw⁻¹ * HA k) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hmw0.le)) hMw0

    calc ∑ Ψ ∈ t, ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ∂μ
        ≤ ∑ Ψ ∈ t, ∑ k, (mw⁻¹ * ∑ p, ‖Adag k ((d Ψ p : V' (T Ψ.1)) : E)‖ ^ 2 +
            ∑ i : {i // cls i = Ψ.1}, ‖Bop k (Cv i)‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun Ψ _ => key Ψ.1 Ψ.2.1 Ψ.2.2 (d Ψ) (hd0 Ψ) (hd1 Ψ)
      _ = ∑ k, (mw⁻¹ * ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)‖ ^ 2 +
            ∑ j : JB, ‖Bop k (Cv j.2.1)‖ ^ 2) / 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hSA : ∑ Ψ ∈ t, ∑ p, ‖Adag k ((d Ψ p : V' (T Ψ.1)) : E)‖ ^ 2 =
              ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)‖ ^ 2 := by
            rw [← Finset.sum_coe_sort t]
            exact (Fintype.sum_sigma (fun j : JA => ‖Adag k ((d j.1.1 j.2 : V' (T j.1.1.1)) : E)‖ ^ 2)).symm
          have hSB : ∑ Ψ ∈ t, ∑ i : {i // cls i = Ψ.1}, ‖Bop k (Cv i)‖ ^ 2 = ∑ j : JB, ‖Bop k (Cv j.2.1)‖ ^ 2 := by
            rw [← Finset.sum_coe_sort t]
            exact (Fintype.sum_sigma (fun j : JB => ‖Bop k (Cv j.2.1)‖ ^ 2)).symm
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hSA, hSB]
      _ ≤ Bound := Finset.sum_le_sum fun k _ =>
          div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left (hAsum k) (inv_nonneg.2 hmw0.le))
            (hBsum k)) two_pos.le

  refine (summable_subtype_and_compl (s := S₁)).1 ⟨?_, ?_⟩
  · have hnn : 0 ≤ fun Ψ : ↥S₁ =>
        ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ∂μ :=
      fun Ψ => integral_nonneg fun _ => norm_nonneg _
    exact summable_of_sum_le hnn hpartial
  · have hz : (fun Ψ : ↥(S₁ᶜ) =>
        ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i x)‖ ∂μ) = 0 := by
      funext Ψ
      have hΨ : Ψ.1 ∉ S₁ := Ψ.2
      by_cases hcl : Ψ.1 ∈ cuspClasses L P ξL N SL
      ·
        have hT' : T Ψ.1 ∉ cuspClasses L P ξσ N SL := fun h => hΨ ⟨hcl, h⟩
        have hbot : isotypicCuspSubmodule L P ξσ N SL (T Ψ.1) = ⊥ := by
          by_contra hne
          exact hT' ⟨((hT Ψ.1).1).trans hcl.1, (hT Ψ.1).2.1, hne⟩
        have hzero : ∀ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) = 0 := by
          intro i
          have hlev : (cls i.1).level = N := (hb i.1).1.1
          have h := (Submodule.mem_inf.1 (hRW (cls i.1) hlev (b i.1) (hb i.1).2)).1
          rw [i.2, hbot, Submodule.mem_bot] at h
          exact h
        simp [hzero]
      · haveI : IsEmpty {i // cls i = Ψ.1} := ⟨fun i => hcl (i.2 ▸ (hb i.1).1)⟩
        simp
    rw [hz]
    exact summable_zero

end S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab (solution)
