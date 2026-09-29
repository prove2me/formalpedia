-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/132542da-8b74-5dc6-8b1f-748d9298a4e8

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
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
import Theorems.Thm_AutomorphicForm_exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat
import Theorems.Thm_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
import Theorems.Thm_AutomorphicForm_exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
import Theorems.Thm_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField.TateGlobal AutomorphicForm

noncomputable section

open Complex

namespace Ws31
namespace C3Glue

theorem L1_conj_symm (L L' : ℂ → ℂ) (hL : Differentiable ℂ L) (hL' : Differentiable ℂ L')
    (h : ∀ w : ℂ, 1 < w.re → L' w = (starRingEnd ℂ) (L ((starRingEnd ℂ) w))) :
    ∀ w : ℂ, L' w = (starRingEnd ℂ) (L ((starRingEnd ℂ) w)) := by

  have hR : Differentiable ℂ (fun w => (starRingEnd ℂ) (L ((starRingEnd ℂ) w))) := by
    intro w
    have := (hL ((starRingEnd ℂ) w)).conj_conj
    simpa [Function.comp_def] using this
  have hA : AnalyticOnNhd ℂ L' Set.univ := (hL'.differentiableOn.analyticOnNhd isOpen_univ)
  have hB : AnalyticOnNhd ℂ (fun w => (starRingEnd ℂ) (L ((starRingEnd ℂ) w))) Set.univ :=
    (hR.differentiableOn.analyticOnNhd isOpen_univ)
  have hev : L' =ᶠ[nhds (2 : ℂ)] (fun w => (starRingEnd ℂ) (L ((starRingEnd ℂ) w))) := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {w : ℂ | 1 < w.re} := by simp
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact h w hw
  have := hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (Set.mem_univ (2 : ℂ)) hev
  intro w
  exact this (Set.mem_univ w)

end Ws31.C3Glue

open Complex

namespace Ws31
namespace C3Glue

theorem norm_real_cpow (Nf : ℝ) (hNf : 0 < Nf) (z : ℂ) : ‖((Nf : ℂ) ^ z)‖ = Nf ^ z.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hNf]

theorem L2_norm_axis (Λ Λd : ℂ → ℂ) (ε : ℂ) (Nf : ℝ) (hNf : 0 < Nf) (hε : ‖ε‖ = 1)
    (hFE : ∀ s : ℂ, Λd (1 - s) = ε * ((Nf : ℂ) ^ (s - 1 / 2)) * Λ s)
    (hconj : ∀ w : ℂ, Λd w = (starRingEnd ℂ) (Λ ((starRingEnd ℂ) w))) (t : ℝ) :
    ‖Λ (2 * ((t : ℂ) * I))‖ = Real.sqrt Nf * ‖Λ (1 + 2 * ((t : ℂ) * I))‖ := by
  have h1 := hFE (2 * ((t : ℂ) * I))
  have h2 : ‖Λd (1 - 2 * ((t : ℂ) * I))‖ = ‖Λ (1 + 2 * ((t : ℂ) * I))‖ := by
    rw [hconj, Complex.norm_conj]
    congr 1
    congr 1
    simp only [map_sub, map_one, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have h3 : ‖ε * ((Nf : ℂ) ^ (2 * ((t : ℂ) * I) - 1 / 2)) * Λ (2 * ((t : ℂ) * I))‖
      = Nf ^ (-(1 / 2 : ℝ)) * ‖Λ (2 * ((t : ℂ) * I))‖ := by
    rw [norm_mul, norm_mul, hε, one_mul, norm_real_cpow Nf hNf]
    congr 1
    congr 1
    simp [Complex.sub_re, Complex.mul_re]
  rw [← h1] at h3
  rw [h2] at h3

  have hpos : 0 < Nf ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hNf _
  have hsq : Real.sqrt Nf * Nf ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNf]; norm_num
  calc ‖Λ (2 * ((t : ℂ) * I))‖ = (Real.sqrt Nf * Nf ^ (-(1 / 2 : ℝ))) * ‖Λ (2 * ((t : ℂ) * I))‖ := by rw [hsq, one_mul]
    _ = Real.sqrt Nf * (Nf ^ (-(1 / 2 : ℝ)) * ‖Λ (2 * ((t : ℂ) * I))‖) := by ring
    _ = Real.sqrt Nf * ‖Λ (1 + 2 * ((t : ℂ) * I))‖ := by rw [← h3]

theorem L4_logDeriv_via_FE (Λ Λd : ℂ → ℂ) (ε : ℂ) (Nf : ℝ) (hNf : 0 < Nf) (hε : ‖ε‖ = 1)
    (hΛ : Differentiable ℂ Λ) (hΛd : Differentiable ℂ Λd)
    (hFE : ∀ s : ℂ, Λd (1 - s) = ε * ((Nf : ℂ) ^ (s - 1 / 2)) * Λ s) (w : ℂ) (hw : Λ w ≠ 0) :
    logDeriv Λ w = -logDeriv Λd (1 - w) - Real.log Nf := by
  have hε0 : ε ≠ 0 := fun h => by rw [h, norm_zero] at hε; exact zero_ne_one hε
  have hNf0 : (Nf : ℂ) ≠ 0 := by exact_mod_cast hNf.ne'

  have hcomp : ∀ s, HasDerivAt (fun s => Λd (1 - s)) (-(deriv Λd (1 - s))) s := by
    intro s
    have h := (hΛd (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
    first | simpa using h | (have h_1 := h; simp at h_1; exact h_1) | (have h_1 := h; simp at h_1 ⊢; exact h_1) | exact (h)

  have hpow : ∀ s, HasDerivAt (fun s : ℂ => (Nf : ℂ) ^ (s - 1 / 2)) ((Nf : ℂ) ^ (s - 1 / 2) * Complex.log Nf) s := by
    intro s
    have h := ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_cpow (c := (Nf : ℂ)) (Or.inl hNf0)
    simpa using h
  have hR : ∀ s, HasDerivAt (fun s => ε * ((Nf : ℂ) ^ (s - 1 / 2)) * Λ s)
      (ε * ((Nf : ℂ) ^ (s - 1 / 2) * Complex.log Nf) * Λ s + ε * ((Nf : ℂ) ^ (s - 1 / 2)) * deriv Λ s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℂ => ε * ((Nf : ℂ) ^ (s - 1 / 2))) (ε * ((Nf : ℂ) ^ (s - 1 / 2) * Complex.log Nf)) s :=
      (hpow s).const_mul ε
    exact h1.mul (hΛ s).hasDerivAt
  have hfun : (fun s => Λd (1 - s)) = fun s => ε * ((Nf : ℂ) ^ (s - 1 / 2)) * Λ s := funext hFE
  have hderiv : -(deriv Λd (1 - w)) = ε * ((Nf : ℂ) ^ (w - 1 / 2) * Complex.log Nf) * Λ w + ε * ((Nf : ℂ) ^ (w - 1 / 2)) * deriv Λ w := by
    have h1 := (hcomp w).deriv
    have h2 := (hR w).deriv
    rw [hfun] at h1
    rw [← h1, h2]
  have hΛdw : Λd (1 - w) ≠ 0 := by
    rw [hFE]; exact mul_ne_zero (mul_ne_zero hε0 (by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hNf0 h.1)) hw
  have hc : (Nf : ℂ) ^ (w - 1 / 2) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hNf0 h.1
  rw [logDeriv_apply, logDeriv_apply, hFE w]
  have : deriv Λd (1 - w) = -(ε * ((Nf : ℂ) ^ (w - 1 / 2) * Complex.log Nf) * Λ w + ε * ((Nf : ℂ) ^ (w - 1 / 2)) * deriv Λ w) := by
    rw [← hderiv, neg_neg]
  rw [this, Complex.ofReal_log hNf.le, neg_div, neg_neg]
  have hA : ε * ((Nf : ℂ) ^ (w - 1 / 2) * Complex.log Nf) * Λ w = (ε * (Nf : ℂ) ^ (w - 1 / 2) * Λ w) * Complex.log Nf := by ring
  have hB : ε * ((Nf : ℂ) ^ (w - 1 / 2)) * deriv Λ w = (ε * (Nf : ℂ) ^ (w - 1 / 2)) * deriv Λ w := by ring
  have hD : ε * (Nf : ℂ) ^ (w - 1 / 2) * Λ w ≠ 0 := mul_ne_zero (mul_ne_zero hε0 hc) hw
  rw [hA, hB, add_div, mul_div_cancel_left₀ _ hD, mul_div_mul_left _ _ (mul_ne_zero hε0 hc)]
  ring

end Ws31.C3Glue

namespace Ws31
namespace C3Glue

open Complex Filter Topology
open scoped ComplexConjugate

theorem logDeriv_congr_of_eventuallyEq (F G : ℂ → ℂ) (w : ℂ) (h : F =ᶠ[𝓝 w] G) :
    logDeriv F w = logDeriv G w := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

theorem L3_logDeriv_re_one (Λ γ L : ℂ → ℂ) (w : ℂ) (hw : w.re = 1) (hΛ : ∀ z : ℂ, 0 < z.re → Λ z = γ z * L z)
    (hγ : γ w ≠ 0) (hL : L w ≠ 0) (hγd : DifferentiableAt ℂ γ w) (hLd : DifferentiableAt ℂ L w) :
    logDeriv Λ w = logDeriv γ w + logDeriv L w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hwmem : w ∈ {z : ℂ | 0 < z.re} := by show 0 < w.re; rw [hw]; exact one_pos
  have hev : Λ =ᶠ[𝓝 w] (fun z => γ z * L z) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hopen.mem_nhds hwmem, fun z hz => hΛ z hz⟩
  rw [logDeriv_congr_of_eventuallyEq _ _ w hev]
  exact logDeriv_mul w hγ hL hγd hLd

theorem L3_logDeriv_of_pos_re (Λ γ L : ℂ → ℂ) (w : ℂ) (hw : 0 < w.re) (hΛ : ∀ z : ℂ, 0 < z.re → Λ z = γ z * L z)
    (hγ : γ w ≠ 0) (hL : L w ≠ 0) (hγd : DifferentiableAt ℂ γ w) (hLd : DifferentiableAt ℂ L w) :
    logDeriv Λ w = logDeriv γ w + logDeriv L w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Λ =ᶠ[𝓝 w] (fun z => γ z * L z) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hopen.mem_nhds hw, fun z hz => hΛ z hz⟩
  rw [logDeriv_congr_of_eventuallyEq _ _ w hev]
  exact logDeriv_mul w hγ hL hγd hLd

theorem L3_logDeriv_prod_shift {ι : Type*} [Fintype ι] (G : ℂ → ℂ) (c : ι → ℂ) (w : ℂ)
    (hG : ∀ i, G (w + c i) ≠ 0) (hGd : ∀ i, DifferentiableAt ℂ G (w + c i)) :
    (∏ i, G (w + c i)) ≠ 0 ∧
    DifferentiableAt ℂ (fun z => ∏ i, G (z + c i)) w ∧
    logDeriv (fun z => ∏ i, G (z + c i)) w = ∑ i, logDeriv G (w + c i) := by
  have hdi : ∀ i, DifferentiableAt ℂ (fun z => G (z + c i)) w := fun i =>
    (hGd i).comp w (differentiableAt_id.add_const (c i))
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => hG i, ?_, ?_⟩
  · have h := DifferentiableAt.finsetProd (u := Finset.univ) (f := fun i z => G (z + c i)) (x := w) fun i _ => hdi i
    rwa [Finset.prod_fn] at h
  · rw [logDeriv_prod (s := Finset.univ) (f := fun i z => G (z + c i)) (x := w) (fun i _ => hG i) (fun i _ => hdi i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]

theorem L3_norm_logDeriv_prod_shift_le {ι : Type*} [Fintype ι] (G : ℂ → ℂ) (c : ι → ℂ) (w : ℂ) (M : ι → ℝ)
    (hG : ∀ i, G (w + c i) ≠ 0) (hGd : ∀ i, DifferentiableAt ℂ G (w + c i))
    (hM : ∀ i, ‖logDeriv G (w + c i)‖ ≤ M i) :
    ‖logDeriv (fun z => ∏ i, G (z + c i)) w‖ ≤ ∑ i, M i := by
  rw [(L3_logDeriv_prod_shift G c w hG hGd).2.2]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hM i)

theorem log_two_add_abs_im_add_le {ι : Type*} [Fintype ι] (c : ι → ℂ) (w : ℂ) (i : ι) :
    Real.log (2 + |(w + c i).im|) ≤ Real.log (2 + |w.im| + ∑ j, |(c j).im|) := by
  have h1 : |(w + c i).im| ≤ |w.im| + |(c i).im| := by rw [Complex.add_im]; exact abs_add_le _ _
  have h2 : |(c i).im| ≤ ∑ j, |(c j).im| :=
    Finset.single_le_sum (f := fun j => |(c j).im|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  apply Real.log_le_log (by positivity)
  linarith

theorem conj_GammaReal_conj (w : ℂ) : conj (Complex.Gammaℝ (conj w)) = Complex.Gammaℝ w := by
  have hpi : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have h1 : -(conj w) / 2 = conj (-w / 2) := by
    rw [map_div₀, map_neg, map_ofNat]
  have h2 : conj w / 2 = conj (w / 2) := by rw [map_div₀, map_ofNat]
  unfold Complex.Gammaℝ
  rw [h1, h2, Complex.cpow_conj _ _ hpi, Complex.conj_ofReal, Complex.Gamma_conj, map_mul, Complex.conj_conj,
    Complex.conj_conj]

theorem conj_GammaComplex_conj (w : ℂ) : conj (Complex.Gammaℂ (conj w)) = Complex.Gammaℂ w := by
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
  have harg : ((2 : ℂ) * (Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [h2pi, Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm
  have h1 : -(conj w) = conj (-w) := by rw [map_neg]
  unfold Complex.Gammaℂ
  rw [h1, Complex.cpow_conj _ _ harg, map_mul, map_mul, Complex.conj_conj, Complex.Gamma_conj, Complex.conj_conj,
    map_ofNat]
  congr 2
  rw [map_mul, map_ofNat, Complex.conj_ofReal]

end Ws31.C3Glue

namespace Ws31
namespace C3Glue

open Complex Filter Topology MeasureTheory

theorem L5_norm_sq_add_mul_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (a b : ℂ) (x y : E) :
    ‖a • x + b • y‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 * ‖x‖ ^ 2 + ‖b‖ ^ 2 * ‖y‖ ^ 2) := by
  have h1 : ‖a • x + b • y‖ ≤ ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_smul_le a x) (norm_smul_le b y))
  have h0 : 0 ≤ ‖a • x + b • y‖ := norm_nonneg _
  have hp : 0 ≤ ‖a‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hq : 0 ≤ ‖b‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖a • x + b • y‖ ^ 2 ≤ (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ 2 * (‖a‖ ^ 2 * ‖x‖ ^ 2 + ‖b‖ ^ 2 * ‖y‖ ^ 2) := by
        nlinarith [sq_nonneg (‖a‖ * ‖x‖ - ‖b‖ * ‖y‖)]

theorem L5_norm_sq_add_mul_le' (a b x y : ℂ) :
    ‖a * x + b * y‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 * ‖x‖ ^ 2 + ‖b‖ ^ 2 * ‖y‖ ^ 2) := by
  simpa only [smul_eq_mul] using L5_norm_sq_add_mul_le (E := ℂ) a b x y

theorem L5_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g h : X → ℝ) (A B : ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg : Integrable g μ) (hh : Integrable h μ)
    (hle : ∀ x, f x ≤ 2 * (A * g x + B * h x)) :
    ∫ x, f x ∂μ ≤ 2 * (A * ∫ x, g x ∂μ + B * ∫ x, h x ∂μ) := by
  have hI : Integrable (fun x => 2 * (A * g x + B * h x)) μ := ((hg.const_mul A).add (hh.const_mul B)).const_mul 2
  calc ∫ x, f x ∂μ ≤ ∫ x, 2 * (A * g x + B * h x) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall hf0) hI (Eventually.of_forall hle)
    _ = 2 * (A * ∫ x, g x ∂μ + B * ∫ x, h x ∂μ) := by
        rw [integral_const_mul, integral_add (hg.const_mul A) (hh.const_mul B), integral_const_mul, integral_const_mul]

theorem L5_deriv_congr (F G : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (s₀ : ℂ) (hs₀ : s₀ ∈ U)
    (h : ∀ s ∈ U, F s = G s) : deriv F s₀ = deriv G s₀ :=
  (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hs₀, h⟩ : F =ᶠ[𝓝 s₀] G).deriv_eq

theorem L5_hasDerivAt_comp_two_mul_add_one_mul (Λ M : ℂ → ℂ) (s₀ : ℂ)
    (hΛ : DifferentiableAt ℂ Λ (2 * s₀ + 1)) (hM : DifferentiableAt ℂ M s₀) :
    HasDerivAt (fun s => Λ (2 * s + 1) * M s) (2 * deriv Λ (2 * s₀ + 1) * M s₀ + Λ (2 * s₀ + 1) * deriv M s₀) s₀ := by
  have h1 : HasDerivAt (fun s : ℂ => 2 * s + 1) 2 s₀ := by
    simpa using ((hasDerivAt_id s₀).const_mul (2 : ℂ)).add_const (1 : ℂ)
  have h2 : HasDerivAt (fun s => Λ (2 * s + 1)) (deriv Λ (2 * s₀ + 1) * 2) s₀ :=
    hΛ.hasDerivAt.comp s₀ h1
  have h3 := h2.mul hM.hasDerivAt
  convert h3 using 1 <;> first | rfl | ring

theorem L5_hasDerivAt_comp_two_mul_mul (Λ M : ℂ → ℂ) (s₀ : ℂ)
    (hΛ : DifferentiableAt ℂ Λ (2 * s₀)) (hM : DifferentiableAt ℂ M s₀) :
    HasDerivAt (fun s => Λ (2 * s) * M s) (2 * deriv Λ (2 * s₀) * M s₀ + Λ (2 * s₀) * deriv M s₀) s₀ := by
  have h1 : HasDerivAt (fun s : ℂ => 2 * s) 2 s₀ := by
    simpa using (hasDerivAt_id s₀).const_mul (2 : ℂ)
  have h2 : HasDerivAt (fun s => Λ (2 * s)) (deriv Λ (2 * s₀) * 2) s₀ := hΛ.hasDerivAt.comp s₀ h1
  have h3 := h2.mul hM.hasDerivAt
  convert h3 using 1 <;> first | rfl | ring

end Ws31.C3Glue

namespace Ws31
namespace C3Glue

open Complex Filter Topology

theorem L6_zero_branch {X : Type*} (N : ℂ → X → ℂ) (O : Set ℂ) (hO : IsOpen O) (hOc : IsPreconnected O)
    (h0 : {s : ℂ | s.re = 0} ⊆ O) (h12 : {s : ℂ | 1 / 2 < s.re} ⊆ O)
    (hN : ∀ x, AnalyticOnNhd ℂ (fun s => N s x) O)
    (hz : ∀ s : ℂ, 1 / 2 < s.re → ∀ x, N s x = 0) (t : ℝ) (x : X) :
    N ((t : ℂ) * I) x = 0 ∧ deriv (fun s => N s x) ((t : ℂ) * I) = 0 := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1mem : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by simp; norm_num
  have hev : (fun s => N s x) =ᶠ[𝓝 (1 : ℂ)] 0 :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨{s : ℂ | 1 / 2 < s.re}, hopen.mem_nhds h1mem, fun s hs => hz s hs x⟩
  have hEq : Set.EqOn (fun s => N s x) 0 O :=
    (hN x).eqOn_zero_of_preconnected_of_eventuallyEq_zero hOc (h12 h1mem) hev
  have hit : ((t : ℂ) * I) ∈ O := h0 (by simp)
  refine ⟨hEq hit, ?_⟩
  have hev' : (fun s => N s x) =ᶠ[𝓝 ((t : ℂ) * I)] (fun _ => (0 : ℂ)) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨O, hO.mem_nhds hit, fun s hs => hEq hs⟩
  rw [hev'.deriv_eq, deriv_const]

end Ws31.C3Glue

namespace Ws31
namespace C3Glue

open Complex Filter Topology NumberField
open scoped ComplexConjugate Classical

theorem differentiableAt_Gamma_of_re_pos (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ Gamma s := by
  refine Complex.differentiableAt_Gamma s fun m heq => ?_
  have := congrArg Complex.re heq; simp at this; have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith

theorem differentiableAt_GammaReal_of_re_pos (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hE : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) ^ (-x / 2)) ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s :=
    ((hasDerivAt_id s).neg.div_const 2).const_cpow (Or.inl hc)
  have hG : DifferentiableAt ℂ (fun x : ℂ => Gamma (x / 2)) s :=
    (differentiableAt_Gamma_of_re_pos (s / 2) (by simp; linarith)).comp s ((hasDerivAt_id s).div_const 2).differentiableAt
  rw [show Complex.Gammaℝ = fun x => (Real.pi : ℂ) ^ (-x / 2) * Gamma (x / 2) from rfl]
  exact hE.differentiableAt.mul hG

theorem differentiableAt_GammaComplex_of_re_pos (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gammaℂ s := by
  have hc : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hE : HasDerivAt (fun x : ℂ => (2 * (Real.pi : ℂ)) ^ (-x)) ((2 * (Real.pi : ℂ)) ^ (-s) * Complex.log (2 * (Real.pi : ℂ)) * (-1)) s :=
    (hasDerivAt_id s).neg.const_cpow (Or.inl hc)
  rw [show Complex.Gammaℂ = fun x => (2 * (2 * (Real.pi : ℂ)) ^ (-x)) * Gamma x from rfl]
  exact (hE.differentiableAt.const_mul 2).mul (differentiableAt_Gamma_of_re_pos s hs)

theorem GammaComplex_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) : Complex.Gammaℂ s ≠ 0 := by
  have hc : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hEne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hc h.1
  show 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Gamma s ≠ 0
  exact mul_ne_zero (mul_ne_zero two_ne_zero hEne) (Complex.Gamma_ne_zero_of_re_pos hs)

theorem conj_GammaReal_conj' (w : ℂ) : conj (Complex.Gammaℝ (conj w)) = Complex.Gammaℝ w := by
  have hpi : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have h1 : -(conj w) / 2 = conj (-w / 2) := by rw [map_div₀, map_neg, map_ofNat]
  have h2 : conj w / 2 = conj (w / 2) := by rw [map_div₀, map_ofNat]
  unfold Complex.Gammaℝ
  rw [h1, h2, Complex.cpow_conj _ _ hpi, Complex.conj_ofReal, Complex.Gamma_conj, map_mul, Complex.conj_conj,
    Complex.conj_conj]

theorem conj_GammaComplex_conj' (w : ℂ) : conj (Complex.Gammaℂ (conj w)) = Complex.Gammaℂ w := by
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
  have harg : ((2 : ℂ) * (Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [h2pi, Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm
  have h1 : -(conj w) = conj (-w) := by rw [map_neg]
  unfold Complex.Gammaℂ
  rw [h1, Complex.cpow_conj _ _ harg, map_mul, map_mul, Complex.conj_conj, Complex.Gamma_conj, Complex.conj_conj,
    map_ofNat]
  congr 2
  rw [map_mul, map_ofNat, Complex.conj_ofReal]

section K
variable (K : Type) [Field K] [NumberField K]

noncomputable def archGamma (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) : ℂ → ℂ := fun s =>
  ∏ v : InfinitePlace K,
    (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
      else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))

noncomputable def archShift (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (v : InfinitePlace K) : ℂ :=
  if v.IsReal then ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ)
  else ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2

noncomputable def archFactor (v : InfinitePlace K) : ℂ → ℂ :=
  if v.IsReal then Complex.Gammaℝ else Complex.Gammaℂ

theorem archGamma_eq (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    archGamma K τ m = fun s => ∏ v : InfinitePlace K, archFactor K v (s + archShift K τ m v) := by
  funext s
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v.IsReal
  · simp only [archFactor, archShift, if_pos hv, add_assoc]
  · simp only [archFactor, archShift, if_neg hv, add_assoc]

theorem archShift_re_nonneg (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (v : InfinitePlace K) :
    0 ≤ (archShift K τ m v).re := by
  by_cases hv : v.IsReal
  · simp [archShift, if_pos hv]
  · simp [archShift, if_neg hv]; positivity

theorem norm_archShift_le (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (v : InfinitePlace K) :
    ‖archShift K τ m v‖ ≤ |τ v| + |(m v : ℝ)| := by
  have hm : ((m v).natAbs : ℝ) = |(m v : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  by_cases hv : v.IsReal
  · simp only [archShift, if_pos hv]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    · rw [Complex.norm_natCast, ← hm]
      exact_mod_cast Nat.mod_le _ _
  · simp only [archShift, if_neg hv]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    · rw [norm_div, Complex.norm_natCast, Complex.norm_two, ← hm]
      have : (0 : ℝ) ≤ (m v).natAbs := Nat.cast_nonneg _
      linarith

theorem archFactor_ne_zero (v : InfinitePlace K) (z : ℂ) (hz : 0 < z.re) : archFactor K v z ≠ 0 := by
  by_cases hv : v.IsReal
  · simp only [archFactor, if_pos hv]; exact Complex.Gammaℝ_ne_zero_of_re_pos hz
  · simp only [archFactor, if_neg hv]; exact GammaComplex_ne_zero_of_re_pos z hz

theorem differentiableAt_archFactor (v : InfinitePlace K) (z : ℂ) (hz : 0 < z.re) : DifferentiableAt ℂ (archFactor K v) z := by
  by_cases hv : v.IsReal
  · simp only [archFactor, if_pos hv]; exact differentiableAt_GammaReal_of_re_pos z hz
  · simp only [archFactor, if_neg hv]; exact differentiableAt_GammaComplex_of_re_pos z hz

theorem L8_archGamma_ne_zero_differentiableAt_logDeriv (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (w : ℂ) (hw : 0 < w.re) :
    archGamma K τ m w ≠ 0 ∧ DifferentiableAt ℂ (archGamma K τ m) w ∧
    logDeriv (archGamma K τ m) w = ∑ v : InfinitePlace K, logDeriv (archFactor K v) (w + archShift K τ m v) := by
  have hre : ∀ v, 0 < (w + archShift K τ m v).re := fun v => by
    rw [Complex.add_re]; linarith [archShift_re_nonneg K τ m v]
  have hne : ∀ v, archFactor K v (w + archShift K τ m v) ≠ 0 := fun v => archFactor_ne_zero K v _ (hre v)
  have hd : ∀ v, DifferentiableAt ℂ (archFactor K v) (w + archShift K τ m v) := fun v =>
    differentiableAt_archFactor K v _ (hre v)
  have hdi : ∀ v, DifferentiableAt ℂ (fun z => archFactor K v (z + archShift K τ m v)) w := fun v =>
    (hd v).comp w (differentiableAt_id.add_const _)
  rw [archGamma_eq]
  refine ⟨Finset.prod_ne_zero_iff.mpr fun v _ => hne v, ?_, ?_⟩
  · have h := DifferentiableAt.finsetProd (u := Finset.univ) (f := fun v z => archFactor K v (z + archShift K τ m v))
      (x := w) fun v _ => hdi v
    rwa [Finset.prod_fn] at h
  · rw [logDeriv_prod (s := Finset.univ) (f := fun v z => archFactor K v (z + archShift K τ m v)) (x := w)
      (fun v _ => hne v) (fun v _ => hdi v)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]

theorem L8_norm_logDeriv_archGamma_le (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (δ C : ℝ) (hC : 0 ≤ C)
    (hdig : ∀ s : ℂ, δ ≤ s.re →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + ‖s‖) ∧ ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + ‖s‖))
    (w : ℂ) (hw : 0 < w.re) (hwδ : δ ≤ w.re) :
    ‖logDeriv (archGamma K τ m) w‖ ≤
      (Fintype.card (InfinitePlace K)) * C * Real.log (2 + ‖w‖ + ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|)) := by
  rw [(L8_archGamma_ne_zero_differentiableAt_logDeriv K τ m w hw).2.2]
  set Lg := Real.log (2 + ‖w‖ + ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|)) with hLg
  have hS0 : 0 ≤ ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|) := Finset.sum_nonneg fun v _ => by positivity
  have hterm : ∀ v, ‖logDeriv (archFactor K v) (w + archShift K τ m v)‖ ≤ C * Lg := by
    intro v
    have hreδ : δ ≤ (w + archShift K τ m v).re := by
      rw [Complex.add_re]; linarith [archShift_re_nonneg K τ m v]
    have hlog : Real.log (2 + ‖w + archShift K τ m v‖) ≤ Lg := by
      apply Real.log_le_log (by positivity)
      have h1 := norm_add_le w (archShift K τ m v)
      have h2 := norm_archShift_le K τ m v
      have h3 : |τ v| + |(m v : ℝ)| ≤ ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|) :=
        Finset.single_le_sum (f := fun v => |τ v| + |(m v : ℝ)|) (fun v _ => by positivity) (Finset.mem_univ v)
      linarith
    by_cases hv : v.IsReal
    · have := (hdig _ hreδ).1; simp only [archFactor, if_pos hv] at this ⊢
      exact this.trans (mul_le_mul_of_nonneg_left hlog hC)
    · have := (hdig _ hreδ).2; simp only [archFactor, if_neg hv] at this ⊢
      exact this.trans (mul_le_mul_of_nonneg_left hlog hC)
  calc ‖∑ v : InfinitePlace K, logDeriv (archFactor K v) (w + archShift K τ m v)‖
      ≤ ∑ v : InfinitePlace K, ‖logDeriv (archFactor K v) (w + archShift K τ m v)‖ := norm_sum_le _ _
    _ ≤ ∑ v : InfinitePlace K, C * Lg := Finset.sum_le_sum fun v _ => hterm v
    _ = (Fintype.card (InfinitePlace K)) * C * Lg := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem L8_archGamma_neg_eq_conj (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (w : ℂ) :
    archGamma K (fun v => -τ v) m w = conj (archGamma K τ m (conj w)) := by
  simp only [archGamma, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v.IsReal
  · simp only [if_pos hv]
    rw [← conj_GammaReal_conj' (w + (((-τ v : ℝ)) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))]
    congr 2
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    push_cast; ring
  · simp only [if_neg hv]
    rw [← conj_GammaComplex_conj' (w + (((-τ v : ℝ)) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)]
    congr 2
    simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
    push_cast; ring

end K

section Kdual
variable (K : Type) [Field K] [NumberField K]

theorem archGamma_neg_eq_sub (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    archGamma K (fun v => -τ v) m = fun s => ∏ v : InfinitePlace K,
      (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)) := by
  funext s
  simp only [archGamma]
  refine Finset.prod_congr rfl fun v _ => ?_
  have : s + (((-τ v : ℝ)) : ℂ) * Complex.I = s - ((τ v : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]

theorem L8_archGammaDual_eq_conj (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (w : ℂ) :
    (∏ v : InfinitePlace K,
      (if v.IsReal then Complex.Gammaℝ (w - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (w - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))) =
    conj (archGamma K τ m (conj w)) := by
  have h := congrFun (archGamma_neg_eq_sub K τ m) w
  rw [← h]
  exact L8_archGamma_neg_eq_conj K τ m w

end Kdual

end Ws31.C3Glue

namespace Ws31
namespace C3Glue

open Complex Filter Topology MeasureTheory Metric

theorem continuous_slice_of_continuousOn_prod {X : Type*} [TopologicalSpace X] (R : ℂ → X → ℂ) (U : Set ℂ)
    (hcont : ContinuousOn (fun p : ℂ × X => R p.1 p.2) (U ×ˢ Set.univ)) (s : ℂ) (hs : s ∈ U) :
    Continuous (fun x => R s x) := by
  have h1 : Continuous (fun x : X => ((s, x) : ℂ × X)) := continuous_const.prodMk continuous_id
  have h2 : ∀ x : X, ((s, x) : ℂ × X) ∈ U ×ˢ (Set.univ : Set X) := fun x => ⟨hs, Set.mem_univ x⟩
  exact hcont.comp_continuous h1 h2

theorem L9_integrable_norm_sq_deriv {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (R : ℂ → X → ℂ) (U : Set ℂ) (hU : IsOpen U) (s₀ : ℂ) (hs₀ : s₀ ∈ U)
    (han : ∀ x, DifferentiableOn ℂ (fun s => R s x) U)
    (hcont : ContinuousOn (fun p : ℂ × X => R p.1 p.2) (U ×ˢ Set.univ)) :
    Integrable (fun x => ‖deriv (fun s => R s x) s₀‖ ^ 2) μ ∧ Integrable (fun x => ‖R s₀ x‖ ^ 2) μ := by

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU s₀ hs₀
  set ρ : ℝ := ε / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hcb : closedBall s₀ ρ ⊆ U := fun z hz => hball (by
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz; linarith)

  have hK : IsCompact (closedBall s₀ ρ ×ˢ (Set.univ : Set X)) := (isCompact_closedBall s₀ ρ).prod isCompact_univ
  have hcK : ContinuousOn (fun p : ℂ × X => R p.1 p.2) (closedBall s₀ ρ ×ˢ (Set.univ : Set X)) :=
    hcont.mono (Set.prod_mono hcb le_rfl)
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hcK
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ z ∈ closedBall s₀ ρ, ∀ x : X, ‖R z x‖ ≤ M := fun z hz x =>
    (hM₀ (z, x) ⟨hz, Set.mem_univ x⟩).trans (le_max_left _ _)

  have hderiv : ∀ x : X, ‖deriv (fun s => R s x) s₀‖ ≤ M / ρ := by
    intro x
    have hdc : DiffContOnCl ℂ (fun s => R s x) (ball s₀ ρ) :=
      ((han x).mono ((closure_ball_subset_closedBall).trans hcb)).diffContOnCl
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos hdc
      (fun z hz => hM z (sphere_subset_closedBall hz) x)

  have hmeas : Measurable (fun x => deriv (fun s => R s x) s₀) := by
    let h : ℕ → ℂ := fun n => ((ρ / ((n : ℝ) + 2) : ℝ) : ℂ)
    have hh0 : ∀ n, h n ≠ 0 := fun n => by
      simp only [h, ne_eq, Complex.ofReal_eq_zero]; positivity
    have hhmem : ∀ n, s₀ + h n ∈ U := fun n => hcb (by
      rw [Metric.mem_closedBall, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 2 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
      exact div_le_self hρpos.le this)
    have htend : Tendsto h atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ρ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have := tendsto_const_div_atTop_nhds_zero_nat ρ

        have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
          tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        exact tendsto_const_nhds.div_atTop h2
      have h2 := Complex.continuous_ofReal.continuousAt.tendsto.comp h1
      first | simpa using h2 | (have h_1 := h2; simp at h_1; exact h_1) | (have h_1 := h2; simp at h_1 ⊢; exact h_1) | exact (h2)
    let F : ℕ → X → ℂ := fun n x => (h n)⁻¹ * (R (s₀ + h n) x - R s₀ x)
    have hFm : ∀ n, Measurable (F n) := fun n =>
      (continuous_const.mul ((continuous_slice_of_continuousOn_prod R U hcont _ (hhmem n)).sub
        (continuous_slice_of_continuousOn_prod R U hcont _ hs₀))).measurable
    refine measurable_of_tendsto_metrizable hFm ?_
    rw [tendsto_pi_nhds]
    intro x
    have hd : HasDerivAt (fun s => R s x) (deriv (fun s => R s x) s₀) s₀ :=
      ((han x).differentiableAt (hU.mem_nhds hs₀)).hasDerivAt

    have hs : Tendsto (fun n => s₀ + h n) atTop (𝓝[≠] s₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · simpa using tendsto_const_nhds.add htend
      · simp [hh0 n]
    have := (hasDerivAt_iff_tendsto_slope.mp hd).comp hs
    refine this.congr' (Eventually.of_forall fun n => ?_)
    show slope (fun s => R s x) s₀ (s₀ + h n) = F n x
    rw [slope_def_field]
    simp only [F, add_sub_cancel_left]
    rw [div_eq_inv_mul]
  have hmeas2 : Measurable (fun x => R s₀ x) := (continuous_slice_of_continuousOn_prod R U hcont _ hs₀).measurable
  constructor
  · refine Integrable.mono' (integrable_const ((M / ρ) ^ 2)) (hmeas.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hderiv x) 2
  · refine Integrable.mono' (integrable_const (M ^ 2)) (hmeas2.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM s₀ (mem_closedBall_self hρpos.le) x) 2

end Ws31.C3Glue

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

namespace Ws31
namespace C3Glue
open Complex
open scoped ComplexConjugate

theorem conj_tprod {ι : Type*} (f : ι → ℂ) : conj (∏' i, f i) = ∏' i, conj (f i) := by
  have hmap : ∀ g : ι → ℂ, Multipliable g → HasProd (fun i => conj (g i)) (conj (∏' i, g i)) := fun g hg =>
    hg.hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  by_cases h : Multipliable f
  · exact ((hmap f h).tprod_eq).symm
  · have h' : ¬ Multipliable (fun i => conj (f i)) := by
      intro h'
      apply h
      have := (hmap _ h').multipliable
      simpa using this
    rw [tprod_eq_one_of_not_multipliable h, tprod_eq_one_of_not_multipliable h', map_one]

theorem conj_natCast_cpow_neg_conj (N : ℕ) (w : ℂ) : conj (((N : ℕ) : ℂ) ^ (-(conj w))) = ((N : ℕ) : ℂ) ^ (-w) := by
  have harg : ((N : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [show ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg N)]
    exact Real.pi_ne_zero.symm
  have h1 : -(conj w) = conj (-w) := by rw [map_neg]
  rw [h1, Complex.cpow_conj _ _ harg, Complex.conj_conj, map_natCast]

theorem eulerProduct_conj {K : Type} [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (w : ℂ) :
    conj (∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(conj w))))⁻¹)
      = ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((((χ (uniformizerIdele K v))⁻¹ : ℂˣ)) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
  rw [conj_tprod]
  refine tprod_congr fun v => ?_
  rw [map_inv₀, map_sub, map_one, map_mul, conj_natCast_cpow_neg_conj]
  congr 2
  split_ifs with h
  · rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hχu _)]
  · rw [map_zero]

end Ws31.C3Glue

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel
open NumberField.TateGlobal
open scoped Classical

namespace Ws31
namespace C3Glue
open Complex

variable {K : Type} [Field K] [NumberField K]

theorem coe_mul_normPowChar_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (((χ * normPowChar K θ) z : ℂˣ) : ℂ) = ((χ z : ℂˣ) : ℂ) * ((ideleNorm K z : ℝ) : ℂ) ^ (I * θ) := by
  rw [MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply]

theorem isUnitaryChar_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsUnitaryChar (𝓞 K) K χ) (θ : ℝ) :
    IsUnitaryChar (𝓞 K) K (χ * normPowChar K θ) := by
  intro z
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ z, norm_coe_normPowChar_apply, one_mul]

theorem ideleNorm_unitsMap_algebraMap (q : Kˣ) :
    ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q) = 1 := by
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := K) (diagOne q)
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K (diagOne q)) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q := by
    ext
    simp [globalPoints, diagOne, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]
  rwa [hdet] at h

theorem isIdeleClassChar_normPowChar (θ : ℝ) : IsIdeleClassChar (𝓞 K) K (normPowChar K θ) := fun q =>
  normPowChar_eq_one_of_ideleNorm_eq_one θ (ideleNorm_unitsMap_algebraMap q)

theorem isIdeleClassChar_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ)
    (θ : ℝ) : IsIdeleClassChar (𝓞 K) K (χ * normPowChar K θ) := fun q => by
  rw [MonoidHom.mul_apply, hχ q, isIdeleClassChar_normPowChar θ q, one_mul]

theorem continuous_coe_normPowChar (θ : ℝ) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((normPowChar K θ z : ℂˣ) : ℂ) := by
  simp only [coe_normPowChar_apply]
  refine Continuous.cpow (Complex.continuous_ofReal.comp (continuous_ideleNorm K)) continuous_const fun z => ?_
  exact Or.inl (by simpa using ideleNorm_pos z)

theorem continuous_coe_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) (θ : ℝ) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ * normPowChar K θ) z : ℂˣ) : ℂ) := by
  simp only [MonoidHom.mul_apply, Units.val_mul]
  exact hχc.mul (continuous_coe_normPowChar θ)

theorem ideleNorm_finIncl_localUnit (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (hu' : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ideleNorm K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u)) = 1 := by
  refine NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K _ rfl ⟨?_, ?_⟩
  · intro w
    show (((localUnit (𝓞 K) K v u) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w ∈ _
    by_cases hw : w = v
    · subst hw; rw [localUnit_apply_self]; exact hu
    · rw [localUnit_apply_of_ne (𝓞 K) K v u hw]; exact one_mem _
  · intro w
    show ((((localUnit (𝓞 K) K v u)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ)) : FiniteAdeleRing (𝓞 K) K) w ∈ _
    rw [← map_inv]
    by_cases hw : w = v
    · subst hw; rw [localUnit_apply_self]; exact hu'
    · rw [localUnit_apply_of_ne (𝓞 K) K v _ hw]; exact one_mem _

theorem localChar_mul_normPowChar_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) (hu : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (hu' : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    localChar (χ * normPowChar K θ) v u = localChar χ v u := by
  rw [localChar_apply, localChar_apply, MonoidHom.mul_apply,
    normPowChar_eq_one_of_ideleNorm_eq_one θ (ideleNorm_finIncl_localUnit v u hu hu'), mul_one]

theorem isUnramifiedCharAt_mul_normPowChar_iff (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) : IsUnramifiedCharAt (χ * normPowChar K θ) v ↔ IsUnramifiedCharAt χ v := by
  constructor
  · intro h u hu hu'; rw [← localChar_mul_normPowChar_apply χ θ v u hu hu']; exact h u hu hu'
  · intro h u hu hu'; rw [localChar_mul_normPowChar_apply χ θ v u hu hu']; exact h u hu hu'

theorem coe_archLocalChar_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (w : InfinitePlace K)
    (x : (w.Completion)ˣ) :
    ((archLocalChar (χ * normPowChar K θ) w x : ℂˣ) : ℂ) =
      ((archLocalChar χ w x : ℂˣ) : ℂ) * ((ideleNorm K (archUnitHom w x) : ℝ) : ℂ) ^ (I * θ) := by
  show (((χ * normPowChar K θ) (archUnitHom w x) : ℂˣ) : ℂ) = ((χ (archUnitHom w x) : ℂˣ) : ℂ) * _
  exact coe_mul_normPowChar_apply χ θ _

theorem norm_ext' (w : InfinitePlace K) (x : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem ideleNorm_archUnitHom' (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  have h1 : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)).erase w,
      ‖((archUnitHom w x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = 1 := by
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) v‖ ^ v.mult = 1
    rw [Function.update_of_ne hvw]
    change ‖(1 : v.Completion)‖ ^ v.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one h1, one_mul]
  show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) w‖ ^ w.mult = _
  rw [Function.update_self]

theorem archParam_pin_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (τ : InfinitePlace K → ℝ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (χ * normPowChar K θ) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ ((((τ v + θ : ℝ)) : ℂ) * Complex.I) := by
  intro v x h1 h2
  have hn0 : (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ideleNorm_pos _).ne'
  rw [coe_archLocalChar_mul_normPowChar, hτ v x h1 h2, ← Complex.cpow_add _ _ hn0]
  congr 1; push_cast; ring

theorem weight_pin_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (m : InfinitePlace K → ℤ)
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (χ * normPowChar K θ) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v) := by
  intro v x h1
  have hx1 : ‖(x : v.Completion)‖ = 1 := by rw [← norm_ext']; exact h1
  rw [coe_archLocalChar_mul_normPowChar, hm v x h1, ideleNorm_archUnitHom', hx1, one_pow, Complex.ofReal_one,
    Complex.one_cpow, mul_one]

theorem coe_normPowChar_uniformizerIdele (θ : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ((normPowChar K θ (uniformizerIdele K v) : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(I * θ)) := by
  have harg : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [show ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
    exact Real.pi_ne_zero.symm
  rw [coe_normPowChar_apply, NumberField.TateGlobal.ideleNorm_uniformizerIdele K v, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

theorem eulerFactor_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (v : HeightOneSpectrum (𝓞 K)) (w : ℂ) :
    (1 - (if IsUnramifiedCharAt (χ * normPowChar K θ) v then
        (((χ * normPowChar K θ) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
      = (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(w + θ * I))))⁻¹ := by
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast this
  rw [isUnramifiedCharAt_mul_normPowChar_iff]
  congr 2
  split_ifs with h
  · rw [MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_uniformizerIdele, mul_assoc, ← Complex.cpow_add _ _ hN]
    congr 2
    ring
  · rw [zero_mul, zero_mul]

theorem eulerProduct_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (w : ℂ) :
    (∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt (χ * normPowChar K θ) v then
          (((χ * normPowChar K θ) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹)
      = ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(w + θ * I))))⁻¹ :=
  tprod_congr fun v => eulerFactor_mul_normPowChar χ θ v w

end Ws31.C3Glue

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel
open NumberField.TateGlobal
open scoped Classical

namespace Ws31
namespace C3Glue
p2m_open "Complex NumberField.InfinitePlace.Completion"

variable {K : Type} [Field K] [NumberField K]

theorem norm_ext'' (w : InfinitePlace K) (x : w.Completion) : ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem ideleNorm_archUnitHom'' (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  have h1 : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)).erase w,
      ‖((archUnitHom w x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = 1 := by
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) v‖ ^ v.mult = 1
    rw [Function.update_of_ne hvw]
    change ‖(1 : v.Completion)‖ ^ v.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one h1, one_mul]
  show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) w‖ ^ w.mult = _
  rw [Function.update_self]

theorem exists_extensionEmbedding_eq_ofReal (v : InfinitePlace K) (r : ℝ) :
    ∃ y : v.Completion, extensionEmbedding v y = (r : ℂ) := by
  by_cases hv : v.IsReal
  · obtain ⟨y, hy⟩ := (bijective_extensionEmbeddingOfIsReal hv).2 r
    exact ⟨y, by rw [← extensionEmbeddingOfIsReal_apply hv, hy]⟩
  · exact (surjective_extensionEmbedding_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.mp hv)) _

theorem tau_eq_of_normPowChar (τ₀ : ℝ) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : χ = normPowChar K τ₀)
    (v : InfinitePlace K) (a : ℝ)
    (hτ : ∀ x : (v.Completion)ˣ, 0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((a : ℝ) : ℂ) * Complex.I)) :
    a = τ₀ := by
  by_contra hne
  set d : ℝ := a - τ₀ with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
  have hmult : (v.mult : ℝ) ≠ 0 := by exact_mod_cast (InfinitePlace.mult_pos (w := v)).ne'
  set r : ℝ := Real.exp (Real.pi / (d * v.mult)) with hr
  have hrpos : 0 < r := Real.exp_pos _
  obtain ⟨y, hy⟩ := exists_extensionEmbedding_eq_ofReal v r
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, map_zero] at hy; exact hrpos.ne' (by exact_mod_cast hy.symm)
  let x : (v.Completion)ˣ := Units.mk0 y hy0
  have hxe : extensionEmbedding v (x : v.Completion) = (r : ℂ) := hy
  have h := hτ x (by rw [hxe, Complex.ofReal_re]; exact hrpos) (by rw [hxe, Complex.ofReal_im])

  have hn : ideleNorm K (archUnitHom v x) = Real.exp (Real.pi / d) := by
    rw [ideleNorm_archUnitHom'', ← norm_ext'', hxe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hr,
      ← Real.exp_nat_mul]
    congr 1; field_simp
  have hnpos : 0 < Real.exp (Real.pi / d) := Real.exp_pos _
  have hn0 : ((Real.exp (Real.pi / d) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [hχ, show archLocalChar (normPowChar K τ₀) v x = normPowChar K τ₀ (archUnitHom v x) from rfl,
    coe_normPowChar_apply, hn] at h

  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_log hnpos.le,
    Real.log_exp] at h
  have h2 : Complex.exp (((Real.pi / d : ℝ) : ℂ) * (((a : ℝ) : ℂ) * I) - ((Real.pi / d : ℝ) : ℂ) * (I * τ₀)) = 1 := by
    rw [Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  have hd0' : (((a : ℝ) : ℂ) - ((τ₀ : ℝ) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast (sub_ne_zero.mpr hne)
  have h3 : ((Real.pi / d : ℝ) : ℂ) * (((a : ℝ) : ℂ) * I) - ((Real.pi / d : ℝ) : ℂ) * (I * τ₀) = Real.pi * I := by
    rw [hd]; push_cast
    rw [show (Real.pi : ℂ) / ((a : ℂ) - (τ₀ : ℂ)) * ((a : ℂ) * I) - (Real.pi : ℂ) / ((a : ℂ) - (τ₀ : ℂ)) * (I * (τ₀ : ℂ))
        = ((Real.pi : ℂ) * I) * (((a : ℂ) - (τ₀ : ℂ)) / ((a : ℂ) - (τ₀ : ℂ))) by ring,
      div_self hd0', mul_one]
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

end Ws31.C3Glue

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

namespace Ws31
namespace C3Glue
open Complex

theorem normPowChar_inv_eq {K : Type} [Field K] [NumberField K] (t : ℝ) :
    (normPowChar K t)⁻¹ = normPowChar K (-t) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_normPowChar_apply, coe_normPowChar_apply,
    ← Complex.cpow_neg]
  congr 1
  push_cast
  ring

theorem not_normPow_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (h : ∀ τ₀ : ℝ, μ * ν⁻¹ ≠ normPowChar K τ₀) : ∀ τ₀ : ℝ, ν * μ⁻¹ ≠ normPowChar K τ₀ := by
  intro τ₀ heq
  apply h (-τ₀)
  have : μ * ν⁻¹ = (ν * μ⁻¹)⁻¹ := by ext z; simp [mul_comm]
  rw [this, heq, normPowChar_inv_eq]

theorem isUnramifiedCharAt_swap_iff {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) : IsUnramifiedCharAt (ν * μ⁻¹) v ↔ IsUnramifiedCharAt (μ * ν⁻¹) v := by
  have key : ∀ u : (v.adicCompletion K)ˣ, localChar (ν * μ⁻¹) v u = (localChar (μ * ν⁻¹) v u)⁻¹ := by
    intro u
    show ν _ * (μ _)⁻¹ = (μ _ * (ν _)⁻¹)⁻¹
    rw [mul_inv_rev, inv_inv]
  constructor
  · intro h u hu hu'; have := h u hu hu'; rw [key] at this; exact inv_eq_one.mp this
  · intro h u hu hu'; rw [key, h u hu hu', inv_one]

theorem eulerProduct_swap_eq {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℂ) :
    (∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt (ν * μ⁻¹) v then (((ν * μ⁻¹) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹)
      = ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt (μ * ν⁻¹) v then ((((μ * ν⁻¹) (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
  congr 1; funext v
  have h1 : ((ν * μ⁻¹) (uniformizerIdele K v) : ℂˣ) = ((μ * ν⁻¹) (uniformizerIdele K v))⁻¹ := by
    show ν _ * (μ _)⁻¹ = (μ _ * (ν _)⁻¹)⁻¹
    rw [mul_inv_rev, inv_inv]
  rw [h1]
  simp only [isUnramifiedCharAt_swap_iff]

theorem solve_case_two (A B A' B' N N' R R' u : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hum : u - 1 ≠ 0)
    (hFG : 2 * A' * ((u - 1) * N) + A * (2 * N + (u - 1) * N') = 2 * B' * ((u + 1) * R) + B * (2 * R + (u + 1) * R'))
    (hC : A * ((u - 1) * N) = B * ((u + 1) * R)) :
    N' = (B / A) / (u - 1) * (((2 * (B' / B) - 2 * (A' / A)) * (u + 1) + 2 - 2 * (u + 1) / (u - 1)) * R + (u + 1) * R') := by
  field_simp
  linear_combination (u - 1) * A * hFG - (2 * A' * (u - 1) + 2 * A) * hC

theorem normPowChar_add' {K : Type} [Field K] [NumberField K] (a b : ℝ) :
    normPowChar K a * normPowChar K b = normPowChar K (a + b) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply, coe_normPowChar_apply, coe_normPowChar_apply,
    ← Complex.cpow_add _ _ (by exact_mod_cast (ideleNorm_pos x).ne')]
  congr 1; push_cast; ring

theorem not_normPow_twist {K : Type} [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ)
    (h : ∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀) : ∀ τ₀ : ℝ, χ * normPowChar K θ ≠ normPowChar K τ₀ := by
  intro τ₀ heq
  apply h (τ₀ + -θ)
  have : χ = χ * normPowChar K θ * normPowChar K (-θ) := by
    refine MonoidHom.ext fun z => ?_
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_assoc, ← MonoidHom.mul_apply (normPowChar K θ), normPowChar_add',
      add_neg_cancel, normPowChar_zero, MonoidHom.one_apply, mul_one]
  rw [this, heq, normPowChar_add']

theorem gammaFactor_swap_eq {K : Type} [Field K] [NumberField K] (τμ τν : InfinitePlace K → ℝ) (mμ mν : InfinitePlace K → ℤ) (s : ℂ) :
    (∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s + (((fun v => τν v - τμ v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mν v - mμ v) v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s + (((fun v => τν v - τμ v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mν v - mμ v) v).natAbs : ℕ) : ℂ) / 2)))
      = ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s - (((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mμ v - mν v) v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s - (((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mμ v - mν v) v).natAbs : ℕ) : ℂ) / 2)) := by
  refine Finset.prod_congr rfl fun v _ => ?_
  have hn : (mν v - mμ v).natAbs = (mμ v - mν v).natAbs := by rw [← Int.natAbs_neg, neg_sub]
  have hτ : (((τν v - τμ v : ℝ)) : ℂ) * Complex.I = -((((τμ v - τν v : ℝ)) : ℂ) * Complex.I) := by push_cast; ring
  simp only [hn, hτ, ← sub_eq_add_neg]

end Ws31.C3Glue

namespace Ws31
namespace C3Glue

theorem localChar_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    localChar (μ * ν⁻¹) v u = localChar μ v u * (localChar ν v u)⁻¹ := rfl

theorem archLocalChar_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : InfinitePlace K) (x : (v.Completion)ˣ) :
    archLocalChar (μ * ν⁻¹) v x = archLocalChar μ v x * (archLocalChar ν v x)⁻¹ := rfl

theorem pin_tau_quot (r τμ τν : ℝ) (hr : 0 < r) :
    ((r : ℂ) ^ (((τμ : ℝ) : ℂ) * Complex.I)) * (((r : ℂ) ^ (((τν : ℝ) : ℂ) * Complex.I)))⁻¹
      = (r : ℂ) ^ ((((τμ - τν : ℝ)) : ℂ) * Complex.I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hr0]
  congr 1
  push_cast
  ring

theorem pin_m_quot (z : ℂ) (hz : z ≠ 0) (mμ mν : ℤ) :
    z ^ mμ * (z ^ mν)⁻¹ = z ^ (mμ - mν) := by
  rw [zpow_sub₀ hz, div_eq_mul_inv]

theorem hτ_quot {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (τμ τν : InfinitePlace K → ℝ)
    (hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τμ v : ℝ) : ℂ) * Complex.I))
    (hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τν v : ℝ) : ℂ) * Complex.I)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ ((((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I) := by
  intro v x h1 h2
  rw [archLocalChar_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, hτμ v x h1 h2, hτν v x h1 h2]
  exact pin_tau_quot _ _ _ (ideleNorm_pos _)

theorem hm_quot {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (mμ mν : InfinitePlace K → ℤ)
    (hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) = (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
    (hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) = (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ ((fun v => mμ v - mν v) v) := by
  intro v x h
  rw [archLocalChar_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, hmμ v x h, hmν v x h]
  have hz : InfinitePlace.Completion.extensionEmbedding v (x : v.Completion) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
  exact pin_m_quot _ hz _ _

theorem hram_quot {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ρ ρ' : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (h : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar μ v u = ρ v u)
    (h' : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar ν v u = ρ' v u) :
    ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        localChar (μ * ν⁻¹) v u = (fun v => ρ v * (ρ' v)⁻¹) v u := by
  intro v hv u hu hu'
  rw [localChar_mul_inv, h v hv u hu hu', h' v hv u hu hu']
  rfl

theorem isUnramifiedCharAt_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hμ : IsUnramifiedCharAt μ v) (hν : IsUnramifiedCharAt ν v) :
    IsUnramifiedCharAt (μ * ν⁻¹) v := by
  intro t ht ht'
  rw [localChar_mul_inv, hμ t ht ht', hν t ht ht', inv_one, mul_one]

theorem isUnitaryChar_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsUnitaryChar (𝓞 K) K μ) (hν : AutomorphicForm.IsUnitaryChar (𝓞 K) K ν) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (μ * ν⁻¹) := by
  intro x
  show ‖(((μ x * (ν x)⁻¹ : ℂˣ)) : ℂ)‖ = 1
  rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hμ x, hν x, inv_one, mul_one]

theorem isIdeleClassChar_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ) (hν : AutomorphicForm.IsIdeleClassChar (𝓞 K) K ν) :
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K (μ * ν⁻¹) := by
  intro u
  show μ _ * (ν _)⁻¹ = 1
  rw [hμ u, hν u, inv_one, mul_one]

theorem continuous_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
    (hν : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * ν⁻¹) z : ℂˣ) : ℂ) := by
  have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * ν⁻¹) z : ℂˣ) : ℂ)) = fun z => ((μ z : ℂˣ) : ℂ) * (((ν z : ℂˣ) : ℂ))⁻¹ := by
    funext z; simp [Units.val_inv_eq_inv_val]
  rw [this]
  exact hμ.mul (hν.inv₀ fun z => Units.ne_zero _)

theorem mul_inv_inv_eq {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    (μ * ν⁻¹)⁻¹ = ν * μ⁻¹ := by
  ext z; simp [mul_comm]

end Ws31.C3Glue

namespace Ws31
namespace C3Glue
open Complex MeasureTheory

theorem exists_ge_forall_le {ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ) : ∃ M : ℝ, a ≤ M ∧ ∀ i, f i ≤ M := by
  classical
  refine ⟨max a (if h : (Finset.univ : Finset ι).Nonempty then Finset.univ.sup' h f else a), le_max_left _ _, fun i => ?_⟩
  have h : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
  rw [dif_pos h]
  exact (Finset.le_sup' f (Finset.mem_univ i)).trans (le_max_right _ _)

theorem exists_nat_ge_forall_le {ι : Type} [Fintype ι] (f : ι → ℕ) : ∃ M : ℕ, ∀ i, f i ≤ M := by
  classical
  refine ⟨if h : (Finset.univ : Finset ι).Nonempty then Finset.univ.sup' h f else 0, fun i => ?_⟩
  have h : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
  rw [dif_pos h]; exact Finset.le_sup' f (Finset.mem_univ i)

end Ws31.C3Glue

set_option maxHeartbeats 16000000 in
open Ws31.C3Glue in
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
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧
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
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g))
      (t : ℝ),
    (∫ k, ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
        deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) ((t : ℂ) * Complex.I)‖ ^ 2 ∂(maximalCompactHaar K))
      ≤ (C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A) ^ 2 := by
  intro αm
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  classical

  obtain ⟨n, ρs, hFR⟩ :=
    AutomorphicForm.exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
      K SK N hN

  let ρq : Fin n × Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ :=
    fun p v => ρs p.1 v * (ρs p.2 v)⁻¹
  have hF1 := fun p : Fin n × Fin n =>
    NumberField.TateGlobal.exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq K SK (ρq p)
  have hC3b := fun p : Fin n × Fin n =>
    NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq K SK (ρq p)
  choose Nf hNf0 hF1' using hF1
  choose c₀ Cz Az hc₀ hCz hC3b' using hC3b

  obtain ⟨CR, AR, hCR, hF2⟩ :=
    AutomorphicForm.exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat
      K SK ξK hξc hξt N hN tysK w hξw

  obtain ⟨Cdg, hCdg, hdg⟩ :=
    Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re (1 / 2) (by norm_num)
  have hdig : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ Cdg * Real.log (2 + ‖s‖) ∧ ‖logDeriv Complex.Gammaℂ s‖ ≤ Cdg * Real.log (2 + ‖s‖) :=
    fun s hs => ⟨(hdg s hs).2.1, (hdg s hs).2.2⟩

  obtain ⟨Nfmax, hNfmax1, hNfmax⟩ := exists_ge_forall_le Nf 1
  obtain ⟨Czmax, hCzmax1, hCzmax⟩ := exists_ge_forall_le Cz 1
  obtain ⟨Azmax, hAzmax⟩ := exists_nat_ge_forall_le Az
  obtain ⟨Lmax, hLmax0, hLmax⟩ := exists_ge_forall_le (fun p => |Real.log (Nf p)|) 0

  set ncard : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hncard
  set E : ℝ := 3 * ncard * Cdg + Czmax * 3 ^ Azmax with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  set Cfin : ℝ := Real.sqrt (2 * Nfmax * ((4 * E + 2 * Lmax + 8) ^ 2 + 1)) * CR with hCfin
  have hCfin0 : 0 < Cfin := by rw [hCfin]; exact mul_pos (Real.sqrt_pos.mpr (by positivity)) hCR
  refine ⟨Cfin, AR + Azmax + 1, hCfin0, ?main⟩
  case main =>
    intro hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν τμ τν _hτμ _hτν mμ mν _hmμ _hmν ψf _hψf _hψfK _hψff _hψfjc _hψfhol
      _hψfKu _hψfflat _hψflev _hψfty _hψfn Oψ Eψ Nψ _hEψ t
    obtain ⟨hOopen, hOconn, hOaxis, hOhalf, _hEan, hNan, _hEcont, hNcont, _hEeq, hNeq⟩ := _hEψ

    set D : ℝ := ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) with hD
    have hDnn : 0 ≤ D := Finset.sum_nonneg fun v _ => by positivity
    have hit : ((t : ℂ) * Complex.I) ∈ Oψ := hOaxis (by simp)
    by_cases hzero : ∀ s : ℂ, ψf s = 0
    ·
      have hN0 : ∀ k : adelicMaximalCompact K, ∀ s ∈ Oψ, Nψ s (k : AdelicGL2 (𝓞 K) K) = 0 := by
        intro k
        have h2 : (2 : ℂ) ∈ Oψ := hOhalf (by simp; norm_num)

        have hev : (fun s => Nψ s (k : AdelicGL2 (𝓞 K) K)) =ᶠ[nhds (2 : ℂ)] 0 := by
          have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
          filter_upwards [hopen.mem_nhds (show (2:ℂ) ∈ {s : ℂ | 1 / 2 < s.re} by simp; norm_num)] with s hs
          rw [hNeq s hs, hzero s]
          show weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) 0 (k : AdelicGL2 (𝓞 K) K) = 0
          unfold weylIntertwiningIntegral
          simp
        have := (hNan (k : AdelicGL2 (𝓞 K) K)).eqOn_zero_of_preconnected_of_eventuallyEq_zero hOconn h2 hev
        exact fun s hs => this hs
      have hderiv0 : ∀ k : adelicMaximalCompact K, deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) ((t : ℂ) * Complex.I) = 0 := by
        intro k
        have hev : (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) =ᶠ[nhds ((t : ℂ) * Complex.I)] (fun _ => (0 : ℂ)) := by
          filter_upwards [hOopen.mem_nhds hit] with s hs
          exact hN0 k s hs
        rw [hev.deriv_eq, deriv_const]
      have hint : (∫ k, ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
          deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) ((t : ℂ) * Complex.I)‖ ^ 2 ∂(maximalCompactHaar K)) = 0 := by
        simp_rw [hderiv0, mul_zero, norm_zero]
        simp
      rw [hint]
      positivity
    ·
      push Not at hzero
      obtain ⟨s₀, hs₀⟩ := hzero
      obtain ⟨hunr, r, r', hρ⟩ := hFR hαm μ ν s₀ (ψf s₀) (_hψf s₀) hs₀ (_hψflev s₀)

      set χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ * ν⁻¹ with hχ
      have hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ) := continuous_mul_inv μ ν _hμc _hνc
      have hχu : IsUnitaryChar (𝓞 K) K χ := isUnitaryChar_mul_inv μ ν _hμ _hν
      have hχF : IsIdeleClassChar (𝓞 K) K χ := isIdeleClassChar_mul_inv μ ν _hμic _hνic
      have hχunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → IsUnramifiedCharAt χ v :=
        fun v hv => isUnramifiedCharAt_mul_inv μ ν v (hunr v hv).1 (hunr v hv).2
      have hχram : ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar χ v u = ρq (r, r') v u :=
        hram_quot μ ν SK (ρs r) (ρs r') (fun v hv u hu hu' => (hρ v hv u hu hu').1) (fun v hv u hu hu' => (hρ v hv u hu hu').2)
      have hχτ := hτ_quot μ ν τμ τν _hτμ _hτν
      have hχm := hm_quot μ ν mμ mν _hmμ _hmν

      have hF1χ := hF1' (r, r') χ hχc hχu hχF hχunr hχram (fun v => τμ v - τν v) (fun v => mμ v - mν v) hχτ hχm
      have hC3bχ := hC3b' (r, r') χ hχc hχu hχF hχunr hχram

      obtain ⟨δ, R, hδ, hRan, hRcont, hF2i, hF2ii, hRbd⟩ := hF2 hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν τμ τν _hτμ _hτν mμ mν _hmμ _hmν
        ψf _hψf _hψfK _hψff _hψfjc _hψfhol _hψfKu _hψfflat _hψflev _hψfty _hψfn Oψ Eψ Nψ
        ⟨hOopen, hOconn, hOaxis, hOhalf, _hEan, hNan, _hEcont, hNcont, _hEeq, hNeq⟩

      have hLEX := NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq K χ hχc hχu hχF
          (fun v => τμ v - τν v) (fun v => mμ v - mν v) hχτ hχm

      set χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ν * μ⁻¹ with hχ'
      have hχ'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ' z : ℂˣ) : ℂ) := continuous_mul_inv ν μ _hνc _hμc
      have hχ'u : IsUnitaryChar (𝓞 K) K χ' := isUnitaryChar_mul_inv ν μ _hν _hμ
      have hχ'F : IsIdeleClassChar (𝓞 K) K χ' := isIdeleClassChar_mul_inv ν μ _hνic _hμic
      have hχ'unr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → IsUnramifiedCharAt χ' v :=
        fun v hv => isUnramifiedCharAt_mul_inv ν μ v (hunr v hv).2 (hunr v hv).1
      have hχ'ram : ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar χ' v u = ρq (r', r) v u :=
        hram_quot ν μ SK (ρs r') (ρs r) (fun v hv u hu hu' => (hρ v hv u hu hu').2) (fun v hv u hu hu' => (hρ v hv u hu hu').1)
      have hχ'τ := hτ_quot ν μ τν τμ _hτν _hτμ
      have hχ'm := hm_quot ν μ mν mμ _hmν _hmμ
      have hLEX' := NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq K χ' hχ'c hχ'u hχ'F
          (fun v => τν v - τμ v) (fun v => mν v - mμ v) hχ'τ hχ'm
      have hC3bχ' := hC3b' (r', r) χ' hχ'c hχ'u hχ'F hχ'unr hχ'ram

      set s₀ : ℂ := (t : ℂ) * Complex.I with hs₀

      set U : Set ℂ := Oψ ∩ {s : ℂ | -δ < s.re} with hU
      have hUopen : IsOpen U := hOopen.inter (isOpen_lt continuous_const Complex.continuous_re)
      have hs₀re : s₀.re = 0 := by simp [hs₀]
      have hs₀U : s₀ ∈ U := ⟨hit, by show -δ < s₀.re; rw [hs₀re]; linarith⟩

      set cK : ℂ := ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ with hcK
      set w₁ : ℂ := 2 * s₀ + 1 with hw₁
      set w₀ : ℂ := 2 * s₀ with hw₀
      have hw₀re : w₀.re = 0 := by rw [hw₀, hs₀]; simp
      have hw₁re : w₁.re = 1 := by rw [hw₁, Complex.add_re, hw₀re]; simp
      have h1w₀ : 1 - w₀ = (starRingEnd ℂ) w₁ := by
        rw [hw₁, hw₀, hs₀]; apply Complex.ext <;> simp

      set X : ℝ := 1 + D with hX
      have hX1 : 1 ≤ X := by rw [hX]; linarith
      have hX0 : 0 < X := by linarith
      have hDv : ∀ v : InfinitePlace K, |t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ) ≤ D := fun v => by
        rw [hD]; exact Finset.single_le_sum (f := fun v => |t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))
          (fun v _ => by positivity) (Finset.mem_univ v)

      have htwist : ∀ (ξ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (p : Fin n × Fin n) (θ : ℝ) (τ' : InfinitePlace K → ℝ) (m' : InfinitePlace K → ℤ)
          (Lξ : ℂ → ℂ),
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ z : ℂˣ) : ℂ)) → IsUnitaryChar (𝓞 K) K ξ → IsIdeleClassChar (𝓞 K) K ξ →
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → IsUnramifiedCharAt ξ v) →
          (∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar ξ v u = ρq p v u) →
          (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
            0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
            (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
            ((archLocalChar ξ v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ' v : ℝ) : ℂ) * Complex.I)) →
          (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
            ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
            ((archLocalChar ξ v x : ℂˣ) : ℂ) = (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m' v)) →
          (∀ τ₀ : ℝ, ξ ≠ normPowChar K τ₀) → Differentiable ℂ Lξ →
          (∀ w : ℂ, 1 < w.re → Lξ w = ∏' v : HeightOneSpectrum (𝓞 K),
            (1 - (if IsUnramifiedCharAt ξ v then ((ξ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
          (∑ v : InfinitePlace K, (|τ' v + θ| + (|m' v| : ℝ)) ≤ D) →
          Lξ (1 + (θ : ℂ) * Complex.I) ≠ 0 ∧
            ‖logDeriv Lξ (1 + (θ : ℂ) * Complex.I)‖ ≤ Cz p * (3 * X) ^ Az p := by
        intro ξ p θ τ' m' Lξ hξc hξu hξF hξunr hξram hξτ hξm hξnp hLξd hLξP hsum

        have h := hC3b' p (ξ * normPowChar K θ) (continuous_coe_mul_normPowChar ξ hξc θ)
          (isUnitaryChar_mul_normPowChar ξ hξu θ) (isIdeleClassChar_mul_normPowChar ξ hξF θ)
          (fun v hv => (isUnramifiedCharAt_mul_normPowChar_iff ξ θ v).mpr (hξunr v hv))
          (fun v hv u hu hu' => by rw [localChar_mul_normPowChar_apply ξ θ v u hu hu']; exact hξram v hv u hu hu')
        have h1 := h.1 (fun v => τ' v + θ) m' (archParam_pin_mul_normPowChar ξ θ τ' hξτ) (weight_pin_mul_normPowChar ξ θ m' hξm)
          (not_normPow_twist ξ θ hξnp) (fun w => Lξ (w + (θ : ℂ) * Complex.I))
          (hLξd.comp (differentiable_id.add_const _))
          (fun w hw => by
            beta_reduce
            rw [hLξP (w + (θ : ℂ) * Complex.I) (by simpa using hw)]
            exact (eulerProduct_mul_normPowChar ξ θ w).symm)
          0 1
        have hTle : 2 + |(0 : ℝ)| + ∑ v : InfinitePlace K, (|(fun v => τ' v + θ) v| + (|m' v| : ℝ)) ≤ 3 * X := by
          rw [hX, abs_zero, add_zero]; linarith
        have hT1 : (1 : ℝ) ≤ 2 + |(0 : ℝ)| + ∑ v : InfinitePlace K, (|(fun v => τ' v + θ) v| + (|m' v| : ℝ)) := by
          have : 0 ≤ ∑ v : InfinitePlace K, (|(fun v => τ' v + θ) v| + (|m' v| : ℝ)) := Finset.sum_nonneg fun v _ => by positivity
          rw [abs_zero]; linarith
        obtain ⟨hne, hder, -⟩ := h1 (by
          show 1 - c₀ p / Real.log (2 + |(0 : ℝ)| + ∑ v : InfinitePlace K, (|(fun v => τ' v + θ) v| + (|m' v| : ℝ))) ≤ 1
          have : 0 ≤ c₀ p / Real.log (2 + |(0 : ℝ)| + ∑ v : InfinitePlace K, (|(fun v => τ' v + θ) v| + (|m' v| : ℝ))) :=
            div_nonneg (hc₀ p).le (Real.log_nonneg hT1)
          linarith) (by norm_num)
        have hpt : (((1 : ℝ)) : ℂ) + (((0 : ℝ)) : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 1 + (θ : ℂ) * Complex.I := by push_cast; ring
        beta_reduce at hne hder
        rw [hpt] at hne hder
        refine ⟨hne, ?_⟩
        have hderiv : deriv (fun w => Lξ (w + (θ : ℂ) * Complex.I)) ((((1 : ℝ)) : ℂ) + (((0 : ℝ)) : ℂ) * Complex.I)
            = deriv Lξ (1 + (θ : ℂ) * Complex.I) := by
          rw [deriv_comp_add_const, hpt]
        rw [hderiv] at hder
        rw [logDeriv_apply, norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)]
        refine hder.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ (hCz p).le
        exact pow_le_pow_left₀ (by linarith) hTle _
      have hsumχ : ∑ v : InfinitePlace K, (|(fun v => τμ v - τν v) v + 2 * t| + (|(fun v => mμ v - mν v) v| : ℝ)) ≤ D := by
        rw [hD]; refine Finset.sum_le_sum fun v _ => ?_
        beta_reduce
        have h1 : |τμ v - τν v + 2 * t| ≤ |t + τμ v| + |t - τν v| := by
          calc |τμ v - τν v + 2 * t| = |(t + τμ v) + (t - τν v)| := by ring_nf
            _ ≤ |t + τμ v| + |t - τν v| := abs_add_le _ _
        have h2 : (|(mμ v - mν v : ℤ)| : ℝ) ≤ (|mμ v| : ℝ) + (|mν v| : ℝ) := by push_cast; exact abs_sub _ _
        linarith
      have hsumχ' : ∑ v : InfinitePlace K, (|(fun v => τν v - τμ v) v + -(2 * t)| + (|(fun v => mν v - mμ v) v| : ℝ)) ≤ D := by
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun v _ => ?_)) hsumχ
        beta_reduce
        rw [show τν v - τμ v + -(2 * t) = -(τμ v - τν v + 2 * t) by ring, abs_neg, show mν v - mμ v = -(mμ v - mν v) by ring]
        push_cast
        rw [abs_neg]
      have hw₁eq : (1 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I = w₁ := by rw [hw₁, hw₀, hs₀]; push_cast; ring
      have hw₀eq : (1 : ℂ) + ((-(2 * t) : ℝ) : ℂ) * Complex.I = 1 - w₀ := by rw [hw₀, hs₀]; push_cast; ring
      by_cases hnp : ∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀
      ·
        have hnp' : ∀ τ₀ : ℝ, χ' ≠ normPowChar K τ₀ := by
          have := not_normPow_inv μ ν (by rwa [← hχ]); rwa [← hχ'] at this
        obtain ⟨L, Λ, hLd, hΛd, hLP, hΛγ⟩ := hLEX.1 hnp
        obtain ⟨L', Λd, hL'd, hΛdd, hL'P, hΛdγ⟩ := hLEX'.1 hnp'

        have hL'P' : ∀ w : ℂ, 1 < w.re → L' w = ∏' v : HeightOneSpectrum (𝓞 K),
            (1 - (if IsUnramifiedCharAt χ v then ((((χ (uniformizerIdele K v))⁻¹ : ℂˣ)) : ℂ) else 0) *
              (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
          intro w hw
          rw [hL'P w hw, hχ', hχ]
          exact eulerProduct_swap_eq μ ν w
        have hΛdγ' : ∀ s : ℂ, 0 < s.re → Λd s = (∏ v : InfinitePlace K,
            (if v.IsReal then Complex.Gammaℝ (s - (((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mμ v - mν v) v).natAbs % 2 : ℕ) : ℂ))
              else Complex.Gammaℂ (s - (((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mμ v - mν v) v).natAbs : ℕ) : ℂ) / 2))) * L' s := by
          intro s hs
          rw [hΛdγ s hs]
          beta_reduce
          rw [gammaFactor_swap_eq τμ τν mμ mν s]
        obtain ⟨ε, hε, hFE⟩ := hF1χ.1 hnp L hLd hLP L' hL'd hL'P' Λ Λd hΛd hΛdd hΛγ hΛdγ'

        have hid := hF2i hnp Λ hΛd (fun w' hw' => by rw [hΛγ w' (by linarith), hLP w' hw'])

        have hconj : ∀ w : ℂ, Λd w = (starRingEnd ℂ) (Λ ((starRingEnd ℂ) w)) := by

          have hLL' : ∀ w : ℂ, L' w = (starRingEnd ℂ) (L ((starRingEnd ℂ) w)) := by
            refine L1_conj_symm L L' hLd hL'd fun w hw => ?_
            have hw' : 1 < ((starRingEnd ℂ) w).re := by simpa using hw
            rw [hL'P' w hw, hLP _ hw']
            beta_reduce
            exact (eulerProduct_conj χ hχu w).symm

          refine L1_conj_symm Λ Λd hΛd hΛdd fun w hw => ?_
          have hw0 : 0 < w.re := by linarith
          have hw0' : 0 < ((starRingEnd ℂ) w).re := by simpa using hw0
          rw [hΛdγ' w hw0, hΛγ _ hw0', map_mul, ← hLL' w]
          congr 1
          beta_reduce
          exact L8_archGammaDual_eq_conj K (fun v => τμ v - τν v) (fun v => mμ v - mν v) w

        have hγ₁ := L8_archGamma_ne_zero_differentiableAt_logDeriv K (fun v => τμ v - τν v) (fun v => mμ v - mν v) w₁ (by rw [hw₁re]; norm_num)
        obtain ⟨hL₁ne, hL₁bd⟩ := by
          have := htwist χ (r, r') (2 * t) (fun v => τμ v - τν v) (fun v => mμ v - mν v) L hχc hχu hχF hχunr hχram hχτ hχm hnp hLd hLP hsumχ
          rwa [hw₁eq] at this
        obtain ⟨hL₁ne', hL₁'bd⟩ := by
          have := htwist χ' (r', r) (-(2 * t)) (fun v => τν v - τμ v) (fun v => mν v - mμ v) L' hχ'c hχ'u hχ'F hχ'unr hχ'ram hχ'τ hχ'm hnp' hL'd hL'P hsumχ'
          rwa [hw₀eq] at this

        have hΛw₁ : Λ w₁ = archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v) w₁ * L w₁ :=
          hΛγ w₁ (by rw [hw₁re]; norm_num)
        have hΛ₁ne : Λ w₁ ≠ 0 := by rw [hΛw₁]; exact mul_ne_zero hγ₁.1 hL₁ne
        have hnormΛ₀ : ‖Λ w₀‖ = Real.sqrt (Nf (r, r')) * ‖Λ w₁‖ := by
          have h := L2_norm_axis Λ Λd ε (Nf (r, r')) (hNf0 _) hε hFE hconj t
          have e0 : (2 : ℂ) * ((t : ℂ) * Complex.I) = w₀ := by rw [hw₀, hs₀]
          have e1 : (1 : ℂ) + 2 * ((t : ℂ) * Complex.I) = w₁ := by rw [hw₁, hw₀, hs₀]; ring
          rwa [e0, e1] at h
        have hΛ₀ne : Λ w₀ ≠ 0 := by
          intro h0
          have : ‖Λ w₀‖ = 0 := by rw [h0, norm_zero]
          rw [hnormΛ₀] at this
          rcases mul_eq_zero.mp this with h | h
          · exact (Real.sqrt_pos.mpr (hNf0 _)).ne' h
          · exact hΛ₁ne (norm_eq_zero.mp h)

        have hsolve : ∀ k : adelicMaximalCompact K,
            cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀
              = (Λ w₀ / Λ w₁) * ((2 * logDeriv Λ w₀ - 2 * logDeriv Λ w₁) * R s₀ k + deriv (fun s => R s k) s₀) := by
          intro k
          have hNdiff : DifferentiableAt ℂ (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀ :=
            ((hNan (k : AdelicGL2 (𝓞 K) K)) s₀ hit).differentiableAt
          have hRdiff : DifferentiableAt ℂ (fun s : ℂ => R s k) s₀ :=
            ((hRan k) s₀ (by show -δ < s₀.re; rw [hs₀re]; linarith)).differentiableAt
          have hF := L5_hasDerivAt_comp_two_mul_add_one_mul Λ (fun s => cK * Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀
            (hΛd _) (hNdiff.const_mul cK)
          have hG := L5_hasDerivAt_comp_two_mul_mul Λ (fun s => R s k) s₀ (hΛd _) hRdiff
          have hFG : deriv (fun s => Λ (2 * s + 1) * (cK * Nψ s (k : AdelicGL2 (𝓞 K) K))) s₀ = deriv (fun s => Λ (2 * s) * R s k) s₀ :=
            L5_deriv_congr _ _ U hUopen s₀ hs₀U (fun s hs => hid s hs.1 hs.2 k)
          rw [hF.deriv, hG.deriv, deriv_const_mul cK hNdiff] at hFG
          have hC : Λ w₁ * (cK * Nψ s₀ (k : AdelicGL2 (𝓞 K) K)) = Λ w₀ * R s₀ k := hid s₀ hit (by rw [hs₀re]; linarith) k

          beta_reduce at hFG
          rw [logDeriv_apply, logDeriv_apply]
          field_simp
          linear_combination (Λ w₁) * hFG - 2 * deriv Λ w₁ * hC

        have hw₁pos : 0 < w₁.re := by rw [hw₁re]; norm_num
        have h1w₀re : (1 - w₀).re = 1 := by rw [Complex.sub_re, hw₀re]; simp
        have h1w₀pos : 0 < (1 - w₀).re := by rw [h1w₀re]; norm_num
        have hγ₁' := L8_archGamma_ne_zero_differentiableAt_logDeriv K (fun v => τν v - τμ v) (fun v => mν v - mμ v) (1 - w₀) h1w₀pos
        have hncard0 : 0 ≤ ncard := by rw [hncard]; positivity
        have hfac : ∀ (τ' : InfinitePlace K → ℝ) (m' : InfinitePlace K → ℤ) (z : ℂ) (v : InfinitePlace K),
            (1 / 2 : ℝ) ≤ (z + archShift K τ' m' v).re → ‖z + archShift K τ' m' v‖ ≤ 2 + D →
            ‖logDeriv (archFactor K v) (z + archShift K τ' m' v)‖ ≤ Cdg * (3 * X) := by
          intro τ' m' z v hre hn
          have hb : ‖logDeriv (archFactor K v) (z + archShift K τ' m' v)‖ ≤ Cdg * Real.log (2 + ‖z + archShift K τ' m' v‖) := by
            by_cases hv : v.IsReal
            · simp only [archFactor, if_pos hv]; exact (hdig _ hre).1
            · simp only [archFactor, if_neg hv]; exact (hdig _ hre).2
          refine hb.trans (mul_le_mul_of_nonneg_left ?_ hCdg.le)
          have hpos : 0 < 2 + ‖z + archShift K τ' m' v‖ := by positivity
          have := Real.log_le_sub_one_of_pos hpos
          rw [hX]; linarith

        have hshift₁ : ∀ v : InfinitePlace K,
            (1 / 2 : ℝ) ≤ (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re ∧
            ‖w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v‖ ≤ 2 + D := by
          intro v
          have hre : (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re
              = 1 + (archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re := by rw [Complex.add_re, hw₁re]
          have hsnn := archShift_re_nonneg K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v
          refine ⟨by rw [hre]; linarith, ?_⟩
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          have him : (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).im = (t + τμ v) + (t - τν v) := by
            rw [Complex.add_im, hw₁, hw₀, hs₀]
            by_cases hv : v.IsReal <;> simp [archShift, hv] <;> ring
          have hre' : |(w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re| ≤ 1 + ((|mμ v| : ℝ) + (|mν v| : ℝ)) := by
            rw [hre, abs_of_nonneg (by linarith)]
            have : (archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re ≤ |(((mμ v - mν v : ℤ)) : ℝ)| := by
              have hm : (((mμ v - mν v).natAbs : ℕ) : ℝ) = |(((mμ v - mν v : ℤ)) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
              by_cases hv : v.IsReal
              · simp only [archShift, if_pos hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.natCast_re, zero_add]
                rw [← hm]; exact_mod_cast Nat.mod_le _ _
              · simp only [archShift, if_neg hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, Complex.div_ofNat_re, Complex.natCast_re]
                rw [← hm]; linarith [show (0:ℝ) ≤ ((mμ v - mν v).natAbs : ℕ) from by positivity]
            have h2 : |(((mμ v - mν v : ℤ)) : ℝ)| ≤ (|mμ v| : ℝ) + (|mν v| : ℝ) := by push_cast; exact abs_sub _ _
            linarith
          rw [him]
          have := hDv v
          have h3 := abs_add_le (t + τμ v) (t - τν v)
          linarith
        have hshift₀ : ∀ v : InfinitePlace K,
            (1 / 2 : ℝ) ≤ ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re ∧
            ‖(1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v‖ ≤ 2 + D := by
          intro v
          have hre : ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re
              = 1 + (archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re := by rw [Complex.add_re, h1w₀re]
          have hsnn := archShift_re_nonneg K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v
          refine ⟨by rw [hre]; linarith, ?_⟩
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          have him : ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).im = -((t + τμ v) + (t - τν v)) := by
            rw [Complex.add_im, Complex.sub_im, hw₀, hs₀]
            by_cases hv : v.IsReal <;> simp [archShift, hv] <;> ring
          have hre' : |((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re| ≤ 1 + ((|mμ v| : ℝ) + (|mν v| : ℝ)) := by
            rw [hre, abs_of_nonneg (by linarith)]
            have : (archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re ≤ |(((mν v - mμ v : ℤ)) : ℝ)| := by
              have hm : (((mν v - mμ v).natAbs : ℕ) : ℝ) = |(((mν v - mμ v : ℤ)) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
              by_cases hv : v.IsReal
              · simp only [archShift, if_pos hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.natCast_re, zero_add]
                rw [← hm]; exact_mod_cast Nat.mod_le _ _
              · simp only [archShift, if_neg hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, Complex.div_ofNat_re, Complex.natCast_re]
                rw [← hm]; linarith [show (0:ℝ) ≤ ((mν v - mμ v).natAbs : ℕ) from by positivity]
            have h2 : |(((mν v - mμ v : ℤ)) : ℝ)| ≤ (|mμ v| : ℝ) + (|mν v| : ℝ) := by push_cast; rw [abs_sub_comm]; exact abs_sub _ _
            linarith
          rw [him, abs_neg]
          have := hDv v
          have h3 := abs_add_le (t + τμ v) (t - τν v)
          linarith
        have hγ₁bd : ‖logDeriv (archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v)) w₁‖ ≤ ncard * Cdg * (3 * X) := by
          rw [hγ₁.2.2]
          refine (norm_sum_le _ _).trans ?_
          calc ∑ v : InfinitePlace K, ‖logDeriv (archFactor K v) (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v)‖
              ≤ ∑ v : InfinitePlace K, Cdg * (3 * X) := Finset.sum_le_sum fun v _ => hfac _ _ _ v (hshift₁ v).1 (hshift₁ v).2
            _ = ncard * Cdg * (3 * X) := by rw [Finset.sum_const, Finset.card_univ, hncard, nsmul_eq_mul]; ring
        have hγ₁'bd : ‖logDeriv (archGamma K (fun v => τν v - τμ v) (fun v => mν v - mμ v)) (1 - w₀)‖ ≤ ncard * Cdg * (3 * X) := by
          rw [hγ₁'.2.2]
          refine (norm_sum_le _ _).trans ?_
          calc ∑ v : InfinitePlace K, ‖logDeriv (archFactor K v) ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v)‖
              ≤ ∑ v : InfinitePlace K, Cdg * (3 * X) := Finset.sum_le_sum fun v _ => hfac _ _ _ v (hshift₀ v).1 (hshift₀ v).2
            _ = ncard * Cdg * (3 * X) := by rw [Finset.sum_const, Finset.card_univ, hncard, nsmul_eq_mul]; ring
        have hXpow : X ≤ X ^ (Azmax + 1) := le_self_pow₀ hX1 (Nat.succ_ne_zero _)
        have hXpow' : X ^ Azmax ≤ X ^ (Azmax + 1) := pow_le_pow_right₀ hX1 (Nat.le_succ _)
        have hTA : ∀ p : Fin n × Fin n, Cz p * (3 * X) ^ Az p ≤ Czmax * (3 : ℝ) ^ Azmax * X ^ (Azmax + 1) := by
          intro p
          have h3X : 1 ≤ 3 * X := by linarith
          have h1 : (3 * X) ^ Az p ≤ (3 : ℝ) ^ Azmax * X ^ Azmax := by
            rw [← mul_pow]; exact pow_le_pow_right₀ h3X (hAzmax p)
          have hCz0 := (hCz p).le
          have hCzmax0 : 0 ≤ Czmax := by linarith [hCzmax p]
          calc Cz p * (3 * X) ^ Az p ≤ Czmax * ((3 : ℝ) ^ Azmax * X ^ Azmax) := mul_le_mul (hCzmax p) h1 (by positivity) hCzmax0
            _ ≤ Czmax * ((3 : ℝ) ^ Azmax * X ^ (Azmax + 1)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXpow' (by positivity)) hCzmax0
            _ = _ := by ring
        have hEbd : ∀ p : Fin n × Fin n, ncard * Cdg * (3 * X) + Cz p * (3 * X) ^ Az p ≤ E * X ^ (Azmax + 1) := by
          intro p
          have h2 := hTA p
          have h3 : 3 * ncard * Cdg * X ≤ 3 * ncard * Cdg * X ^ (Azmax + 1) := mul_le_mul_of_nonneg_left hXpow (by positivity)
          rw [hE]; nlinarith
        have hℓ₁ : ‖logDeriv Λ w₁‖ ≤ E * X ^ (Azmax + 1) := by
          rw [L3_logDeriv_of_pos_re Λ (archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v)) L w₁ hw₁pos hΛγ hγ₁.1 hL₁ne hγ₁.2.1 (hLd w₁)]
          exact ((norm_add_le _ _).trans (add_le_add hγ₁bd hL₁bd)).trans (hEbd (r, r'))
        have hℓd : ‖logDeriv Λd (1 - w₀)‖ ≤ E * X ^ (Azmax + 1) := by
          rw [L3_logDeriv_of_pos_re Λd (archGamma K (fun v => τν v - τμ v) (fun v => mν v - mμ v)) L' (1 - w₀) h1w₀pos hΛdγ hγ₁'.1 hL₁ne' hγ₁'.2.1 (hL'd _)]
          exact ((norm_add_le _ _).trans (add_le_add hγ₁'bd hL₁'bd)).trans (hEbd (r', r))
        have hℓ₀ : ‖logDeriv Λ w₀‖ ≤ E * X ^ (Azmax + 1) + Lmax := by
          rw [L4_logDeriv_via_FE Λ Λd ε (Nf (r, r')) (hNf0 _) hε hΛd hΛdd hFE w₀ hΛ₀ne]
          calc ‖-logDeriv Λd (1 - w₀) - (Real.log (Nf (r, r')) : ℂ)‖
              ≤ ‖-logDeriv Λd (1 - w₀)‖ + ‖(Real.log (Nf (r, r')) : ℂ)‖ := norm_sub_le _ _
            _ = ‖logDeriv Λd (1 - w₀)‖ + |Real.log (Nf (r, r'))| := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
            _ ≤ E * X ^ (Azmax + 1) + Lmax := add_le_add hℓd (hLmax (r, r'))
        set ℓ : ℂ := 2 * logDeriv Λ w₀ - 2 * logDeriv Λ w₁ with hℓ
        have hℓbd : ‖ℓ‖ ≤ (4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1) := by
          rw [hℓ]
          have hXp1 : 1 ≤ X ^ (Azmax + 1) := le_trans hX1 hXpow
          calc ‖2 * logDeriv Λ w₀ - 2 * logDeriv Λ w₁‖ ≤ ‖2 * logDeriv Λ w₀‖ + ‖2 * logDeriv Λ w₁‖ := norm_sub_le _ _
            _ = 2 * ‖logDeriv Λ w₀‖ + 2 * ‖logDeriv Λ w₁‖ := by simp
            _ ≤ 2 * (E * X ^ (Azmax + 1) + Lmax) + 2 * (E * X ^ (Azmax + 1)) := by linarith
            _ ≤ (4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1) := by nlinarith

        have hb : ‖Λ w₀ / Λ w₁‖ = Real.sqrt (Nf (r, r')) := by
          rw [norm_div, hnormΛ₀, mul_div_assoc, div_self (norm_ne_zero_iff.mpr hΛ₁ne), mul_one]
        have hb2 : ‖Λ w₀ / Λ w₁‖ ^ 2 ≤ Nfmax := by
          rw [hb, Real.sq_sqrt (hNf0 _).le]; exact hNfmax _

        haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := ⟨rfl⟩
        obtain ⟨hIh, hIg⟩ := L9_integrable_norm_sq_deriv (maximalCompactHaar K) R U hUopen s₀ hs₀U
          (fun k => (hRan k).differentiableOn.mono Set.inter_subset_right)
          (hRcont.mono (Set.prod_mono Set.inter_subset_right le_rfl))
        obtain ⟨hIR, hIR'⟩ := hRbd t
        set M : ℝ := (CR * (1 + D) ^ AR) ^ 2 with hM
        have hpt : ∀ k : adelicMaximalCompact K,
            ‖cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀‖ ^ 2
              ≤ 2 * ((‖Λ w₀ / Λ w₁‖ ^ 2 * ‖ℓ‖ ^ 2) * ‖R s₀ k‖ ^ 2 + ‖Λ w₀ / Λ w₁‖ ^ 2 * ‖deriv (fun s => R s k) s₀‖ ^ 2) := by
          intro k
          rw [hsolve k, norm_mul, mul_pow]
          have h := L5_norm_sq_add_mul_le' ℓ 1 (R s₀ k) (deriv (fun s => R s k) s₀)
          rw [norm_one, one_pow, one_mul, one_mul] at h
          have hb0 : 0 ≤ ‖Λ w₀ / Λ w₁‖ ^ 2 := by positivity
          nlinarith
        have hint := L5_integral_le (maximalCompactHaar K)
          (fun k => ‖cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀‖ ^ 2)
          (fun k => ‖R s₀ k‖ ^ 2) (fun k => ‖deriv (fun s => R s k) s₀‖ ^ 2)
          (‖Λ w₀ / Λ w₁‖ ^ 2 * ‖ℓ‖ ^ 2) (‖Λ w₀ / Λ w₁‖ ^ 2)
          (fun k => by positivity) hIg hIh hpt
        refine hint.trans ?_
        have hIg' : (∫ k, ‖R s₀ k‖ ^ 2 ∂(maximalCompactHaar K)) ≤ M := by rw [hM, hs₀]; exact hIR
        have hIh' : (∫ k, ‖deriv (fun s => R s k) s₀‖ ^ 2 ∂(maximalCompactHaar K)) ≤ M := by rw [hM, hs₀]; exact hIR'
        have hM0 : 0 ≤ M := by rw [hM]; positivity
        have hXp1 : 1 ≤ (X ^ (Azmax + 1)) ^ 2 := one_le_pow₀ (le_trans hX1 hXpow)
        have hℓ2 : ‖ℓ‖ ^ 2 ≤ ((4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hℓbd 2
        have key : ‖Λ w₀ / Λ w₁‖ ^ 2 * ‖ℓ‖ ^ 2 * M + ‖Λ w₀ / Λ w₁‖ ^ 2 * M
            ≤ Nfmax * (((4 * E + 2 * Lmax + 8) ^ 2 + 1) * (X ^ (Azmax + 1)) ^ 2) * M := by
          have h1 : ‖Λ w₀ / Λ w₁‖ ^ 2 * ‖ℓ‖ ^ 2 ≤ Nfmax * (((4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1)) ^ 2) :=
            mul_le_mul hb2 hℓ2 (by positivity) (by linarith [hNfmax (r, r'), (hNf0 (r, r')).le])
          have h2 : ‖Λ w₀ / Λ w₁‖ ^ 2 ≤ Nfmax * (X ^ (Azmax + 1)) ^ 2 := by
            calc ‖Λ w₀ / Λ w₁‖ ^ 2 ≤ Nfmax := hb2
              _ = Nfmax * 1 := (mul_one _).symm
              _ ≤ Nfmax * (X ^ (Azmax + 1)) ^ 2 := mul_le_mul_of_nonneg_left hXp1 (by linarith [hNfmax (r, r'), (hNf0 (r, r')).le])
          calc ‖Λ w₀ / Λ w₁‖ ^ 2 * ‖ℓ‖ ^ 2 * M + ‖Λ w₀ / Λ w₁‖ ^ 2 * M = (‖Λ w₀ / Λ w₁‖ ^ 2 * ‖ℓ‖ ^ 2 + ‖Λ w₀ / Λ w₁‖ ^ 2) * M := by ring
            _ ≤ (Nfmax * ((4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1)) ^ 2 + Nfmax * (X ^ (Azmax + 1)) ^ 2) * M :=
                mul_le_mul_of_nonneg_right (add_le_add h1 h2) hM0
            _ = _ := by ring
        have hCfin2 : (Cfin * (1 + D) ^ (AR + Azmax + 1)) ^ 2 = 2 * (Nfmax * (((4 * E + 2 * Lmax + 8) ^ 2 + 1) * (X ^ (Azmax + 1)) ^ 2) * M) := by
          rw [hCfin, hM, ← hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          ring
        rw [hCfin2]
        have hA1 := mul_le_mul_of_nonneg_left hIg' (show 0 ≤ ‖Λ w₀ / Λ w₁‖ ^ 2 * ‖ℓ‖ ^ 2 by positivity)
        have hA2 := mul_le_mul_of_nonneg_left hIh' (show 0 ≤ ‖Λ w₀ / Λ w₁‖ ^ 2 by positivity)
        linarith [hA1, hA2, key]
      ·
        push Not at hnp
        obtain ⟨τ₀, hτ₀⟩ := hnp
        have hτ₀' : χ' = normPowChar K (-τ₀) := by
          rw [hχ', ← mul_inv_inv_eq μ ν, ← hχ, hτ₀, normPowChar_inv_eq]
        obtain ⟨Q, ΛQ, hQd, hΛQd, hQP, hΛQγ⟩ := hLEX.2 τ₀ hτ₀
        obtain ⟨Q', ΛQd, hQ'd, hΛQdd, hQ'P, hΛQdγ⟩ := hLEX'.2 (-τ₀) hτ₀'

        have hQ'P' : ∀ w : ℂ, 1 < w.re → Q' w = (w - ((1 : ℂ) + ((τ₀ : ℝ) : ℂ) * Complex.I)) * ∏' v : HeightOneSpectrum (𝓞 K),
            (1 - (if IsUnramifiedCharAt χ v then ((((χ (uniformizerIdele K v))⁻¹ : ℂˣ)) : ℂ) else 0) *
              (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
          intro w hw
          rw [hQ'P w hw]
          beta_reduce
          rw [hχ', hχ, eulerProduct_swap_eq μ ν w]
          congr 1
          push_cast; ring
        have hΛQdγ' : ∀ s : ℂ, 0 < s.re → ΛQd s = (s - ((τ₀ : ℝ) : ℂ) * Complex.I) * ((∏ v : InfinitePlace K,
            (if v.IsReal then Complex.Gammaℝ (s - (((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mμ v - mν v) v).natAbs % 2 : ℕ) : ℂ))
              else Complex.Gammaℂ (s - (((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I + ((((fun v => mμ v - mν v) v).natAbs : ℕ) : ℂ) / 2))) * Q' s) := by
          intro s hs
          rw [hΛQdγ s hs]
          beta_reduce
          rw [gammaFactor_swap_eq τμ τν mμ mν s]
          push_cast; ring
        obtain ⟨ε, hε, hFE⟩ := hF1χ.2 τ₀ hτ₀ Q hQd hQP Q' hQ'd hQ'P' ΛQ ΛQd hΛQd hΛQdd hΛQγ hΛQdγ'

        have hid := hF2ii τ₀ (by rw [← hχ]; exact hτ₀) ΛQ hΛQd (fun w' hw' => by
          rw [hΛQγ w' (by linarith), hQP w' hw']
          beta_reduce
          ring)

        have hQQ' : ∀ w : ℂ, Q' w = (starRingEnd ℂ) (Q ((starRingEnd ℂ) w)) := by
          refine L1_conj_symm Q Q' hQd hQ'd fun w hw => ?_
          have hw' : 1 < ((starRingEnd ℂ) w).re := by simpa using hw
          rw [hQ'P' w hw, hQP _ hw']
          beta_reduce
          rw [map_mul, ← eulerProduct_conj χ hχu w]
          congr 1
          simp only [map_sub, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I, starRingEnd_self_apply]
          ring
        have hconj : ∀ w : ℂ, ΛQd w = (starRingEnd ℂ) (ΛQ ((starRingEnd ℂ) w)) := by
          refine L1_conj_symm ΛQ ΛQd hΛQd hΛQdd fun w hw => ?_
          have hw0 : 0 < w.re := by linarith
          have hw0' : 0 < ((starRingEnd ℂ) w).re := by simpa using hw0
          rw [hΛQdγ' w hw0, hΛQγ _ hw0', map_mul, map_mul, ← hQQ' w]
          congr 1
          · simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, starRingEnd_self_apply]; ring
          · congr 1
            beta_reduce
            exact L8_archGammaDual_eq_conj K (fun v => τμ v - τν v) (fun v => mμ v - mν v) w

        obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
        have hτ₀v : τμ v₀ - τν v₀ = τ₀ := tau_eq_of_normPowChar τ₀ χ hτ₀ v₀ (τμ v₀ - τν v₀) (hχτ v₀)
        have h2tτ₀ : |2 * t + τ₀| ≤ D := by
          have := hDv v₀
          have h1 : |2 * t + τ₀| ≤ |t + τμ v₀| + |t - τν v₀| := by
            calc |2 * t + τ₀| = |(t + τμ v₀) + (t - τν v₀)| := by rw [← hτ₀v]; ring_nf
              _ ≤ |t + τμ v₀| + |t - τν v₀| := abs_add_le _ _
          have hm : (0 : ℝ) ≤ |(mμ v₀ : ℝ)| := abs_nonneg _
          have hm' : (0 : ℝ) ≤ |(mν v₀ : ℝ)| := abs_nonneg _
          push_cast at this
          linarith

        have hQbd : ∀ (Qx : ℂ → ℂ) (p : Fin n × Fin n) (tt τx : ℝ),
            (let T : ℝ := 2 + |tt + τx|
             1 - c₀ p / Real.log T ≤ (1 : ℝ) → (1 : ℝ) ≤ 2 →
              Qx (((1 : ℝ) : ℂ) + (tt : ℂ) * Complex.I) ≠ 0 ∧
              ‖deriv Qx (((1 : ℝ) : ℂ) + (tt : ℂ) * Complex.I)‖ ≤ Cz p * T ^ Az p * ‖Qx (((1 : ℝ) : ℂ) + (tt : ℂ) * Complex.I)‖ ∧
              1 ≤ Cz p * T ^ Az p * ‖Qx (((1 : ℝ) : ℂ) + (tt : ℂ) * Complex.I)‖) →
            |tt + τx| ≤ D →
            Qx (1 + (tt : ℂ) * Complex.I) ≠ 0 ∧ ‖logDeriv Qx (1 + (tt : ℂ) * Complex.I)‖ ≤ Cz p * (3 * X) ^ Az p := by
          intro Qx p tt τx h hle
          have hT2 : (2 : ℝ) ≤ 2 + |tt + τx| := by linarith [abs_nonneg (tt + τx)]
          have hTle : 2 + |tt + τx| ≤ 3 * X := by rw [hX]; linarith
          obtain ⟨hne, hder, -⟩ := h (by
            show 1 - c₀ p / Real.log (2 + |tt + τx|) ≤ 1
            have : 0 ≤ c₀ p / Real.log (2 + |tt + τx|) := div_nonneg (hc₀ p).le (Real.log_nonneg (by linarith))
            linarith) (by norm_num)
          have hpt : (((1 : ℝ)) : ℂ) + (tt : ℂ) * Complex.I = 1 + (tt : ℂ) * Complex.I := by push_cast; ring
          rw [hpt] at hne hder
          refine ⟨hne, ?_⟩
          rw [logDeriv_apply, norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)]
          refine hder.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hTle _) (hCz p).le) (norm_nonneg _))
        obtain ⟨hQ₁ne, hQ₁bd⟩ := by
          have := hQbd Q (r, r') (2 * t) τ₀ (hC3bχ.2 τ₀ hτ₀ Q hQd hQP (2 * t) 1) h2tτ₀
          rwa [hw₁eq] at this
        obtain ⟨hQ₁ne', hQ₁'bd⟩ := by
          have h' : |-(2 * t) + -τ₀| ≤ D := by rw [← neg_add, abs_neg]; exact h2tτ₀
          have := hQbd Q' (r', r) (-(2 * t)) (-τ₀) (hC3bχ'.2 (-τ₀) hτ₀' Q' hQ'd hQ'P (-(2 * t)) 1) h'
          rwa [hw₀eq] at this

        set u₀ : ℂ := w₀ + ((τ₀ : ℝ) : ℂ) * Complex.I with hu₀
        have hu₀re : u₀.re = 0 := by rw [hu₀, Complex.add_re, hw₀re]; simp
        have hum : ‖u₀ - 1‖ = ‖u₀ + 1‖ := by
          have hcu : (starRingEnd ℂ) u₀ = -u₀ := Complex.ext (by simp [hu₀re]) (by simp)
          have : u₀ + 1 = -((starRingEnd ℂ) (u₀ - 1)) := by rw [map_sub, map_one, hcu]; ring
          rw [this, norm_neg, Complex.norm_conj]
        have hu1 : 1 ≤ ‖u₀ - 1‖ := by
          calc (1 : ℝ) = |(u₀ - 1).re| := by rw [Complex.sub_re, hu₀re]; simp
            _ ≤ ‖u₀ - 1‖ := Complex.abs_re_le_norm _
        have hum0 : u₀ - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hu1; linarith
        have hup0 : u₀ + 1 ≠ 0 := fun h => by rw [hum, h, norm_zero] at hu1; linarith
        have hw₁τ : 1 ≤ ‖w₁ + ((τ₀ : ℝ) : ℂ) * Complex.I‖ := by
          calc (1 : ℝ) = |(w₁ + ((τ₀ : ℝ) : ℂ) * Complex.I).re| := by rw [Complex.add_re, hw₁re]; simp
            _ ≤ _ := Complex.abs_re_le_norm _
        have hw₁τ0 : w₁ + ((τ₀ : ℝ) : ℂ) * Complex.I ≠ 0 := fun h => by rw [h, norm_zero] at hw₁τ; linarith
        have h1w₀τ : 1 ≤ ‖(1 - w₀) + (((-τ₀) : ℝ) : ℂ) * Complex.I‖ := by
          calc (1 : ℝ) = |((1 - w₀) + (((-τ₀) : ℝ) : ℂ) * Complex.I).re| := by rw [Complex.add_re, Complex.sub_re, hw₀re]; simp
            _ ≤ _ := Complex.abs_re_le_norm _
        have h1w₀τ0 : (1 - w₀) + (((-τ₀) : ℝ) : ℂ) * Complex.I ≠ 0 := fun h => by rw [h, norm_zero] at h1w₀τ; linarith

        have hw₁pos : 0 < w₁.re := by rw [hw₁re]; norm_num
        have h1w₀re : (1 - w₀).re = 1 := by rw [Complex.sub_re, hw₀re]; simp
        have h1w₀pos : 0 < (1 - w₀).re := by rw [h1w₀re]; norm_num
        have hγ₁ := L8_archGamma_ne_zero_differentiableAt_logDeriv K (fun v => τμ v - τν v) (fun v => mμ v - mν v) w₁ hw₁pos
        have hγ₁' := L8_archGamma_ne_zero_differentiableAt_logDeriv K (fun v => τν v - τμ v) (fun v => mν v - mμ v) (1 - w₀) h1w₀pos

        have hΛ₁ne : ΛQ w₁ ≠ 0 := by
          rw [hΛQγ w₁ hw₁pos]; beta_reduce
          exact mul_ne_zero hw₁τ0 (mul_ne_zero hγ₁.1 hQ₁ne)
        have hnormΛ₀ : ‖ΛQ w₀‖ = Real.sqrt (Nf (r, r')) * ‖ΛQ w₁‖ := by
          have h := L2_norm_axis ΛQ ΛQd ε (Nf (r, r')) (hNf0 _) hε hFE hconj t
          have e0 : (2 : ℂ) * ((t : ℂ) * Complex.I) = w₀ := by rw [hw₀, hs₀]
          have e1 : (1 : ℂ) + 2 * ((t : ℂ) * Complex.I) = w₁ := by rw [hw₁, hw₀, hs₀]; ring
          rwa [e0, e1] at h
        have hΛ₀ne : ΛQ w₀ ≠ 0 := by
          intro h0
          have : ‖ΛQ w₀‖ = 0 := by rw [h0, norm_zero]
          rw [hnormΛ₀] at this
          rcases mul_eq_zero.mp this with h | h
          · exact (Real.sqrt_pos.mpr (hNf0 _)).ne' h
          · exact hΛ₁ne (norm_eq_zero.mp h)

        have hsolve : ∀ k : adelicMaximalCompact K,
            cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀
              = (ΛQ w₀ / ΛQ w₁) / (u₀ - 1) *
                (((2 * logDeriv ΛQ w₀ - 2 * logDeriv ΛQ w₁) * (u₀ + 1) + 2 - 2 * (u₀ + 1) / (u₀ - 1)) * R s₀ k
                  + (u₀ + 1) * deriv (fun s => R s k) s₀) := by
          intro k
          have hNdiff : DifferentiableAt ℂ (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀ :=
            ((hNan (k : AdelicGL2 (𝓞 K) K)) s₀ hit).differentiableAt
          have hRdiff : DifferentiableAt ℂ (fun s : ℂ => R s k) s₀ :=
            ((hRan k) s₀ (by show -δ < s₀.re; rw [hs₀re]; linarith)).differentiableAt
          have hlin₁ : HasDerivAt (fun s : ℂ => 2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) 2 s₀ := by
            simpa using (((hasDerivAt_id s₀).const_mul (2 : ℂ)).add_const (((τ₀ : ℝ) : ℂ) * Complex.I)).sub_const (1 : ℂ)
          have hlin₂ : HasDerivAt (fun s : ℂ => 2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) 2 s₀ := by
            simpa using (((hasDerivAt_id s₀).const_mul (2 : ℂ)).add_const (((τ₀ : ℝ) : ℂ) * Complex.I)).add_const (1 : ℂ)
          have hMd : HasDerivAt (fun s : ℂ => (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * (cK * Nψ s (k : AdelicGL2 (𝓞 K) K)))
              (2 * (cK * Nψ s₀ (k : AdelicGL2 (𝓞 K) K)) + (u₀ - 1) * (cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀)) s₀ := by
            have := hlin₁.mul ((hNdiff.const_mul cK).hasDerivAt)
            rw [deriv_const_mul cK hNdiff] at this
            convert this using 2 <;> first | rfl | (rw [hu₀, hw₀]; ring)
          have hM'd : HasDerivAt (fun s : ℂ => (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * R s k)
              (2 * R s₀ k + (u₀ + 1) * deriv (fun s => R s k) s₀) s₀ := by
            have := hlin₂.mul hRdiff.hasDerivAt
            convert this using 2 <;> first | rfl | (rw [hu₀, hw₀]; ring)
          have hF := L5_hasDerivAt_comp_two_mul_add_one_mul ΛQ (fun s => (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * (cK * Nψ s (k : AdelicGL2 (𝓞 K) K))) s₀
            (hΛQd _) hMd.differentiableAt
          have hG := L5_hasDerivAt_comp_two_mul_mul ΛQ (fun s => (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * R s k) s₀ (hΛQd _) hM'd.differentiableAt
          have hFG : deriv (fun s => ΛQ (2 * s + 1) * ((2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * (cK * Nψ s (k : AdelicGL2 (𝓞 K) K)))) s₀
              = deriv (fun s => ΛQ (2 * s) * ((2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * R s k)) s₀ :=
            L5_deriv_congr _ _ U hUopen s₀ hs₀U (fun s hs => by have := hid s hs.1 hs.2 k; linear_combination this)
          rw [hF.deriv, hG.deriv, hMd.deriv, hM'd.deriv] at hFG
          beta_reduce at hFG
          have hC := hid s₀ hit (by rw [hs₀re]; linarith) k
          have e1 : (2 : ℂ) * s₀ + 1 = w₁ := by rw [hw₁, hw₀]
          have e0 : (2 : ℂ) * s₀ = w₀ := hw₀.symm
          have eu : w₀ + ((τ₀ : ℝ) : ℂ) * Complex.I = u₀ := hu₀.symm
          simp only [e1] at hFG hC
          simp only [e0] at hFG hC
          simp only [eu] at hFG hC

          have hC' : ΛQ w₁ * ((u₀ - 1) * (cK * Nψ s₀ (k : AdelicGL2 (𝓞 K) K))) = ΛQ w₀ * ((u₀ + 1) * R s₀ k) := by
            linear_combination hC
          rw [logDeriv_apply, logDeriv_apply]
          exact solve_case_two (ΛQ w₁) (ΛQ w₀) (deriv ΛQ w₁) (deriv ΛQ w₀) (cK * Nψ s₀ (k : AdelicGL2 (𝓞 K) K))
            (cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀) (R s₀ k) (deriv (fun s => R s k) s₀) u₀
            hΛ₁ne hΛ₀ne hum0 hFG hC'

        have hfac : ∀ (τ' : InfinitePlace K → ℝ) (m' : InfinitePlace K → ℤ) (z : ℂ) (v : InfinitePlace K),
            (1 / 2 : ℝ) ≤ (z + archShift K τ' m' v).re → ‖z + archShift K τ' m' v‖ ≤ 2 + D →
            ‖logDeriv (archFactor K v) (z + archShift K τ' m' v)‖ ≤ Cdg * (3 * X) := by
          intro τ' m' z v hre hn
          have hb : ‖logDeriv (archFactor K v) (z + archShift K τ' m' v)‖ ≤ Cdg * Real.log (2 + ‖z + archShift K τ' m' v‖) := by
            by_cases hv : v.IsReal
            · simp only [archFactor, if_pos hv]; exact (hdig _ hre).1
            · simp only [archFactor, if_neg hv]; exact (hdig _ hre).2
          refine hb.trans (mul_le_mul_of_nonneg_left ?_ hCdg.le)
          have hpos : 0 < 2 + ‖z + archShift K τ' m' v‖ := by positivity
          have := Real.log_le_sub_one_of_pos hpos
          rw [hX]; linarith

        have hshift₁ : ∀ v : InfinitePlace K,
            (1 / 2 : ℝ) ≤ (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re ∧
            ‖w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v‖ ≤ 2 + D := by
          intro v
          have hre : (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re
              = 1 + (archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re := by rw [Complex.add_re, hw₁re]
          have hsnn := archShift_re_nonneg K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v
          refine ⟨by rw [hre]; linarith, ?_⟩
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          have him : (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).im = (t + τμ v) + (t - τν v) := by
            rw [Complex.add_im, hw₁, hw₀, hs₀]
            by_cases hv : v.IsReal <;> simp [archShift, hv] <;> ring
          have hre' : |(w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re| ≤ 1 + ((|mμ v| : ℝ) + (|mν v| : ℝ)) := by
            rw [hre, abs_of_nonneg (by linarith)]
            have : (archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v).re ≤ |(((mμ v - mν v : ℤ)) : ℝ)| := by
              have hm : (((mμ v - mν v).natAbs : ℕ) : ℝ) = |(((mμ v - mν v : ℤ)) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
              by_cases hv : v.IsReal
              · simp only [archShift, if_pos hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.natCast_re, zero_add]
                rw [← hm]; exact_mod_cast Nat.mod_le _ _
              · simp only [archShift, if_neg hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, Complex.div_ofNat_re, Complex.natCast_re]
                rw [← hm]; linarith [show (0:ℝ) ≤ ((mμ v - mν v).natAbs : ℕ) from by positivity]
            have h2 : |(((mμ v - mν v : ℤ)) : ℝ)| ≤ (|mμ v| : ℝ) + (|mν v| : ℝ) := by push_cast; exact abs_sub _ _
            linarith
          rw [him]
          have := hDv v
          have h3 := abs_add_le (t + τμ v) (t - τν v)
          linarith
        have hshift₀ : ∀ v : InfinitePlace K,
            (1 / 2 : ℝ) ≤ ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re ∧
            ‖(1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v‖ ≤ 2 + D := by
          intro v
          have hre : ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re
              = 1 + (archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re := by rw [Complex.add_re, h1w₀re]
          have hsnn := archShift_re_nonneg K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v
          refine ⟨by rw [hre]; linarith, ?_⟩
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          have him : ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).im = -((t + τμ v) + (t - τν v)) := by
            rw [Complex.add_im, Complex.sub_im, hw₀, hs₀]
            by_cases hv : v.IsReal <;> simp [archShift, hv] <;> ring
          have hre' : |((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re| ≤ 1 + ((|mμ v| : ℝ) + (|mν v| : ℝ)) := by
            rw [hre, abs_of_nonneg (by linarith)]
            have : (archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v).re ≤ |(((mν v - mμ v : ℤ)) : ℝ)| := by
              have hm : (((mν v - mμ v).natAbs : ℕ) : ℝ) = |(((mν v - mμ v : ℤ)) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
              by_cases hv : v.IsReal
              · simp only [archShift, if_pos hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.natCast_re, zero_add]
                rw [← hm]; exact_mod_cast Nat.mod_le _ _
              · simp only [archShift, if_neg hv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, Complex.div_ofNat_re, Complex.natCast_re]
                rw [← hm]; linarith [show (0:ℝ) ≤ ((mν v - mμ v).natAbs : ℕ) from by positivity]
            have h2 : |(((mν v - mμ v : ℤ)) : ℝ)| ≤ (|mμ v| : ℝ) + (|mν v| : ℝ) := by push_cast; rw [abs_sub_comm]; exact abs_sub _ _
            linarith
          rw [him, abs_neg]
          have := hDv v
          have h3 := abs_add_le (t + τμ v) (t - τν v)
          linarith
        have hγ₁bd : ‖logDeriv (archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v)) w₁‖ ≤ ncard * Cdg * (3 * X) := by
          rw [hγ₁.2.2]
          refine (norm_sum_le _ _).trans ?_
          calc ∑ v : InfinitePlace K, ‖logDeriv (archFactor K v) (w₁ + archShift K (fun v => τμ v - τν v) (fun v => mμ v - mν v) v)‖
              ≤ ∑ v : InfinitePlace K, Cdg * (3 * X) := Finset.sum_le_sum fun v _ => hfac _ _ _ v (hshift₁ v).1 (hshift₁ v).2
            _ = ncard * Cdg * (3 * X) := by rw [Finset.sum_const, Finset.card_univ, hncard, nsmul_eq_mul]; ring
        have hγ₁'bd : ‖logDeriv (archGamma K (fun v => τν v - τμ v) (fun v => mν v - mμ v)) (1 - w₀)‖ ≤ ncard * Cdg * (3 * X) := by
          rw [hγ₁'.2.2]
          refine (norm_sum_le _ _).trans ?_
          calc ∑ v : InfinitePlace K, ‖logDeriv (archFactor K v) ((1 - w₀) + archShift K (fun v => τν v - τμ v) (fun v => mν v - mμ v) v)‖
              ≤ ∑ v : InfinitePlace K, Cdg * (3 * X) := Finset.sum_le_sum fun v _ => hfac _ _ _ v (hshift₀ v).1 (hshift₀ v).2
            _ = ncard * Cdg * (3 * X) := by rw [Finset.sum_const, Finset.card_univ, hncard, nsmul_eq_mul]; ring
        have hXpow : X ≤ X ^ (Azmax + 1) := le_self_pow₀ hX1 (Nat.succ_ne_zero _)
        have hXpow' : X ^ Azmax ≤ X ^ (Azmax + 1) := pow_le_pow_right₀ hX1 (Nat.le_succ _)
        have hTA : ∀ p : Fin n × Fin n, Cz p * (3 * X) ^ Az p ≤ Czmax * (3 : ℝ) ^ Azmax * X ^ (Azmax + 1) := by
          intro p
          have h3X : 1 ≤ 3 * X := by linarith
          have h1 : (3 * X) ^ Az p ≤ (3 : ℝ) ^ Azmax * X ^ Azmax := by
            rw [← mul_pow]; exact pow_le_pow_right₀ h3X (hAzmax p)
          have hCz0 := (hCz p).le
          have hCzmax0 : 0 ≤ Czmax := by linarith [hCzmax p]
          calc Cz p * (3 * X) ^ Az p ≤ Czmax * ((3 : ℝ) ^ Azmax * X ^ Azmax) := mul_le_mul (hCzmax p) h1 (by positivity) hCzmax0
            _ ≤ Czmax * ((3 : ℝ) ^ Azmax * X ^ (Azmax + 1)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXpow' (by positivity)) hCzmax0
            _ = _ := by ring
        have hEbd : ∀ p : Fin n × Fin n, ncard * Cdg * (3 * X) + Cz p * (3 * X) ^ Az p ≤ E * X ^ (Azmax + 1) := by
          intro p
          have h2 := hTA p
          have h3 : 3 * ncard * Cdg * X ≤ 3 * ncard * Cdg * X ^ (Azmax + 1) := mul_le_mul_of_nonneg_left hXpow (by positivity)
          rw [hE]; nlinarith

        have hlin₁ : logDeriv (fun s : ℂ => s + ((τ₀ : ℝ) : ℂ) * Complex.I) w₁ = 1 / (w₁ + ((τ₀ : ℝ) : ℂ) * Complex.I) := by
          rw [logDeriv_apply, deriv_add_const, deriv_id'']
        have hlin₀ : logDeriv (fun s : ℂ => s + (((-τ₀) : ℝ) : ℂ) * Complex.I) (1 - w₀) = 1 / ((1 - w₀) + (((-τ₀) : ℝ) : ℂ) * Complex.I) := by
          rw [logDeriv_apply, deriv_add_const, deriv_id'']
        have hℓ₁ : ‖logDeriv ΛQ w₁‖ ≤ 1 + E * X ^ (Azmax + 1) := by
          rw [L3_logDeriv_of_pos_re ΛQ (fun s => (s + ((τ₀ : ℝ) : ℂ) * Complex.I) * archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v) s) Q w₁ hw₁pos
            (fun z hz => by rw [hΛQγ z hz]; beta_reduce; simp only [archGamma]; ring) (mul_ne_zero hw₁τ0 hγ₁.1) hQ₁ne
            (((differentiableAt_id).add_const _).mul hγ₁.2.1) (hQd w₁)]
          rw [logDeriv_mul (f := fun s : ℂ => s + ((τ₀ : ℝ) : ℂ) * Complex.I) (g := archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v)) w₁ hw₁τ0 hγ₁.1 ((differentiableAt_id).add_const _) hγ₁.2.1, hlin₁]
          have h1 : ‖1 / (w₁ + ((τ₀ : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
            rw [norm_div, norm_one]; exact div_le_one_of_le₀ hw₁τ (norm_nonneg _)
          calc _ ≤ ‖1 / (w₁ + ((τ₀ : ℝ) : ℂ) * Complex.I) + logDeriv (archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v)) w₁‖ + ‖logDeriv Q w₁‖ := norm_add_le _ _
            _ ≤ (‖1 / (w₁ + ((τ₀ : ℝ) : ℂ) * Complex.I)‖ + ‖logDeriv (archGamma K (fun v => τμ v - τν v) (fun v => mμ v - mν v)) w₁‖) + ‖logDeriv Q w₁‖ := by
                gcongr; exact norm_add_le _ _
            _ ≤ (1 + ncard * Cdg * (3 * X)) + Cz (r, r') * (3 * X) ^ Az (r, r') := by gcongr
            _ ≤ 1 + E * X ^ (Azmax + 1) := by linarith [hEbd (r, r')]
        have hℓd : ‖logDeriv ΛQd (1 - w₀)‖ ≤ 1 + E * X ^ (Azmax + 1) := by
          rw [L3_logDeriv_of_pos_re ΛQd (fun s => (s + (((-τ₀) : ℝ) : ℂ) * Complex.I) * archGamma K (fun v => τν v - τμ v) (fun v => mν v - mμ v) s) Q' (1 - w₀) h1w₀pos
            (fun z hz => by rw [hΛQdγ z hz]; beta_reduce; simp only [archGamma]; ring) (mul_ne_zero h1w₀τ0 hγ₁'.1) hQ₁ne'
            (((differentiableAt_id).add_const _).mul hγ₁'.2.1) (hQ'd _)]
          rw [logDeriv_mul (f := fun s : ℂ => s + (((-τ₀) : ℝ) : ℂ) * Complex.I) (g := archGamma K (fun v => τν v - τμ v) (fun v => mν v - mμ v)) (1 - w₀) h1w₀τ0 hγ₁'.1 ((differentiableAt_id).add_const _) hγ₁'.2.1, hlin₀]
          have h1 : ‖1 / ((1 - w₀) + (((-τ₀) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
            rw [norm_div, norm_one]; exact div_le_one_of_le₀ h1w₀τ (norm_nonneg _)
          calc _ ≤ ‖1 / ((1 - w₀) + (((-τ₀) : ℝ) : ℂ) * Complex.I) + logDeriv (archGamma K (fun v => τν v - τμ v) (fun v => mν v - mμ v)) (1 - w₀)‖ + ‖logDeriv Q' (1 - w₀)‖ := norm_add_le _ _
            _ ≤ (‖1 / ((1 - w₀) + (((-τ₀) : ℝ) : ℂ) * Complex.I)‖ + ‖logDeriv (archGamma K (fun v => τν v - τμ v) (fun v => mν v - mμ v)) (1 - w₀)‖) + ‖logDeriv Q' (1 - w₀)‖ := by
                gcongr; exact norm_add_le _ _
            _ ≤ (1 + ncard * Cdg * (3 * X)) + Cz (r', r) * (3 * X) ^ Az (r', r) := by gcongr
            _ ≤ 1 + E * X ^ (Azmax + 1) := by linarith [hEbd (r', r)]
        have hℓ₀ : ‖logDeriv ΛQ w₀‖ ≤ 1 + E * X ^ (Azmax + 1) + Lmax := by
          rw [L4_logDeriv_via_FE ΛQ ΛQd ε (Nf (r, r')) (hNf0 _) hε hΛQd hΛQdd hFE w₀ hΛ₀ne]
          calc ‖-logDeriv ΛQd (1 - w₀) - (Real.log (Nf (r, r')) : ℂ)‖
              ≤ ‖-logDeriv ΛQd (1 - w₀)‖ + ‖(Real.log (Nf (r, r')) : ℂ)‖ := norm_sub_le _ _
            _ = ‖logDeriv ΛQd (1 - w₀)‖ + |Real.log (Nf (r, r'))| := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
            _ ≤ 1 + E * X ^ (Azmax + 1) + Lmax := add_le_add hℓd (hLmax (r, r'))
        set ℓ : ℂ := 2 * logDeriv ΛQ w₀ - 2 * logDeriv ΛQ w₁ with hℓ
        have hXp1' : 1 ≤ X ^ (Azmax + 1) := le_trans hX1 hXpow
        have hℓbd : ‖ℓ‖ ≤ 4 * E * X ^ (Azmax + 1) + 2 * Lmax + 4 := by
          rw [hℓ]
          calc ‖2 * logDeriv ΛQ w₀ - 2 * logDeriv ΛQ w₁‖ ≤ ‖2 * logDeriv ΛQ w₀‖ + ‖2 * logDeriv ΛQ w₁‖ := norm_sub_le _ _
            _ = 2 * ‖logDeriv ΛQ w₀‖ + 2 * ‖logDeriv ΛQ w₁‖ := by simp
            _ ≤ 2 * (1 + E * X ^ (Azmax + 1) + Lmax) + 2 * (1 + E * X ^ (Azmax + 1)) := by linarith
            _ = 4 * E * X ^ (Azmax + 1) + 2 * Lmax + 4 := by ring

        set bq : ℂ := (ΛQ w₀ / ΛQ w₁) / (u₀ - 1) * (u₀ + 1) with hbq
        set ℓq : ℂ := (ℓ * (u₀ + 1) + 2 - 2 * (u₀ + 1) / (u₀ - 1)) / (u₀ + 1) with hℓq
        have hsolve' : ∀ k : adelicMaximalCompact K,
            cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀ = bq * (ℓq * R s₀ k + deriv (fun s => R s k) s₀) := by
          intro k; rw [hsolve k, hbq, hℓq, hℓ]; field_simp
        have hbqn : ‖bq‖ = Real.sqrt (Nf (r, r')) := by
          rw [hbq, norm_mul, norm_div, norm_div, hnormΛ₀, hum, mul_div_assoc, div_self (norm_ne_zero_iff.mpr hΛ₁ne), mul_one,
            div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hup0)]
        have hb2 : ‖bq‖ ^ 2 ≤ Nfmax := by rw [hbqn, Real.sq_sqrt (hNf0 _).le]; exact hNfmax _
        have hℓqbd : ‖ℓq‖ ≤ (4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1) := by
          have hsplit : ℓq = ℓ + (2 - 2 * (u₀ + 1) / (u₀ - 1)) / (u₀ + 1) := by rw [hℓq]; field_simp; ring
          rw [hsplit]
          have hA : ‖(2 - 2 * (u₀ + 1) / (u₀ - 1)) / (u₀ + 1)‖ ≤ 4 := by
            rw [norm_div]
            have hn1 : 1 ≤ ‖u₀ + 1‖ := hum ▸ hu1
            have h2 : ‖2 - 2 * (u₀ + 1) / (u₀ - 1)‖ ≤ 4 := by
              calc ‖2 - 2 * (u₀ + 1) / (u₀ - 1)‖ ≤ ‖(2 : ℂ)‖ + ‖2 * (u₀ + 1) / (u₀ - 1)‖ := norm_sub_le _ _
                _ = 2 + 2 * (‖u₀ + 1‖ / ‖u₀ - 1‖) := by rw [norm_div, norm_mul]; simp; ring
                _ = 4 := by rw [hum, div_self (by linarith : ‖u₀ + 1‖ ≠ 0)]; ring
            calc ‖2 - 2 * (u₀ + 1) / (u₀ - 1)‖ / ‖u₀ + 1‖ ≤ ‖2 - 2 * (u₀ + 1) / (u₀ - 1)‖ / 1 :=
                  div_le_div_of_nonneg_left (norm_nonneg _) one_pos hn1
              _ ≤ 4 := by rw [div_one]; exact h2
          calc ‖ℓ + (2 - 2 * (u₀ + 1) / (u₀ - 1)) / (u₀ + 1)‖ ≤ ‖ℓ‖ + ‖(2 - 2 * (u₀ + 1) / (u₀ - 1)) / (u₀ + 1)‖ := norm_add_le _ _
            _ ≤ (4 * E * X ^ (Azmax + 1) + 2 * Lmax + 4) + 4 := add_le_add hℓbd hA
            _ ≤ (4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1) := by nlinarith [hLmax0, hXp1', hE0]

        haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := ⟨rfl⟩
        obtain ⟨hIh, hIg⟩ := L9_integrable_norm_sq_deriv (maximalCompactHaar K) R U hUopen s₀ hs₀U
          (fun k => (hRan k).differentiableOn.mono Set.inter_subset_right)
          (hRcont.mono (Set.prod_mono Set.inter_subset_right le_rfl))
        obtain ⟨hIR, hIR'⟩ := hRbd t
        set M : ℝ := (CR * (1 + D) ^ AR) ^ 2 with hM
        have hpt : ∀ k : adelicMaximalCompact K,
            ‖cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀‖ ^ 2
              ≤ 2 * ((‖bq‖ ^ 2 * ‖ℓq‖ ^ 2) * ‖R s₀ k‖ ^ 2 + ‖bq‖ ^ 2 * ‖deriv (fun s => R s k) s₀‖ ^ 2) := by
          intro k
          rw [hsolve' k, norm_mul, mul_pow]
          have h := L5_norm_sq_add_mul_le' ℓq 1 (R s₀ k) (deriv (fun s => R s k) s₀)
          rw [norm_one, one_pow, one_mul, one_mul] at h
          have hb0 : 0 ≤ ‖bq‖ ^ 2 := by positivity
          nlinarith
        have hint := L5_integral_le (maximalCompactHaar K)
          (fun k => ‖cK * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 K) K)) s₀‖ ^ 2)
          (fun k => ‖R s₀ k‖ ^ 2) (fun k => ‖deriv (fun s => R s k) s₀‖ ^ 2)
          (‖bq‖ ^ 2 * ‖ℓq‖ ^ 2) (‖bq‖ ^ 2)
          (fun k => by positivity) hIg hIh hpt
        refine hint.trans ?_
        have hIg' : (∫ k, ‖R s₀ k‖ ^ 2 ∂(maximalCompactHaar K)) ≤ M := by rw [hM, hs₀]; exact hIR
        have hIh' : (∫ k, ‖deriv (fun s => R s k) s₀‖ ^ 2 ∂(maximalCompactHaar K)) ≤ M := by rw [hM, hs₀]; exact hIR'
        have hM0 : 0 ≤ M := by rw [hM]; positivity
        have hXp1 : 1 ≤ (X ^ (Azmax + 1)) ^ 2 := one_le_pow₀ (le_trans hX1 hXpow)
        have hℓ2 : ‖ℓq‖ ^ 2 ≤ ((4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hℓqbd 2
        have key : ‖bq‖ ^ 2 * ‖ℓq‖ ^ 2 * M + ‖bq‖ ^ 2 * M
            ≤ Nfmax * (((4 * E + 2 * Lmax + 8) ^ 2 + 1) * (X ^ (Azmax + 1)) ^ 2) * M := by
          have h1 : ‖bq‖ ^ 2 * ‖ℓq‖ ^ 2 ≤ Nfmax * (((4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1)) ^ 2) :=
            mul_le_mul hb2 hℓ2 (by positivity) (by linarith [hNfmax (r, r'), (hNf0 (r, r')).le])
          have h2 : ‖bq‖ ^ 2 ≤ Nfmax * (X ^ (Azmax + 1)) ^ 2 := by
            calc ‖bq‖ ^ 2 ≤ Nfmax := hb2
              _ = Nfmax * 1 := (mul_one _).symm
              _ ≤ Nfmax * (X ^ (Azmax + 1)) ^ 2 := mul_le_mul_of_nonneg_left hXp1 (by linarith [hNfmax (r, r'), (hNf0 (r, r')).le])
          calc ‖bq‖ ^ 2 * ‖ℓq‖ ^ 2 * M + ‖bq‖ ^ 2 * M = (‖bq‖ ^ 2 * ‖ℓq‖ ^ 2 + ‖bq‖ ^ 2) * M := by ring
            _ ≤ (Nfmax * ((4 * E + 2 * Lmax + 8) * X ^ (Azmax + 1)) ^ 2 + Nfmax * (X ^ (Azmax + 1)) ^ 2) * M :=
                mul_le_mul_of_nonneg_right (add_le_add h1 h2) hM0
            _ = _ := by ring
        have hCfin2 : (Cfin * (1 + D) ^ (AR + Azmax + 1)) ^ 2 = 2 * (Nfmax * (((4 * E + 2 * Lmax + 8) ^ 2 + 1) * (X ^ (Azmax + 1)) ^ 2) * M) := by
          rw [hCfin, hM, ← hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          ring
        rw [hCfin2]
        have hA1 := mul_le_mul_of_nonneg_left hIg' (show 0 ≤ ‖bq‖ ^ 2 * ‖ℓq‖ ^ 2 by positivity)
        have hA2 := mul_le_mul_of_nonneg_left hIh' (show 0 ≤ ‖bq‖ ^ 2 by positivity)
        linarith [hA1, hA2, key]

end
end S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight (solution)
