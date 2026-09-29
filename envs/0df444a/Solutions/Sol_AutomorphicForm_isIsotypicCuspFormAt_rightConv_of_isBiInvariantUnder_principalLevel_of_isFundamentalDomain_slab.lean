-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b495ae43-422a-5a9d-85cc-b206acdb9ce7

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm

namespace P2mConvAssemblyK

private theorem _root_.P2mConvAssemblyK.exists_notMem_finset (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "P2mConvAssemblyK" "exists_notMem_finset"

theorem ne_bot_of_forall_dvd_mem (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨w, hw⟩ := exists_notMem_finset K S
  exact hw (hN w ⟨⊥, by rw [Ideal.mul_bot]⟩)

end P2mConvAssemblyK

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (N₁ N : Ideal (𝓞 L)) (hN₁ : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₁ → w ∈ S)
    (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S)
    (Ψ : HeckeEigensystem L ℂ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (v : AdelicGL2 (𝓞 L) L → ℂ)
    (hv : IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N₁ S Ψ v) :
    IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N S Ψ (rightConv L v φ) := by
  have hN0 : N ≠ ⊥ := P2mConvAssemblyK.ne_bot_of_forall_dvd_mem L S N hN
  obtain ⟨hA₁, hA₂, hA₃⟩ :=
    AutomorphicForm.isSmoothCuspAutomorphicFnAt_rightConv_principalLevel_of_isFundamentalDomain_slab L α β ΦL hΦs hΦ ξL N hN0
      φ hφ hφc (fun u hu g => (hbi u hu g).1) v hv.continuous hv.smoothCusp.1
  refine ⟨hA₁, hA₂, hA₃, fun w hwS => ?_, fun w hwS g => ?_⟩
  · exact AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd L N₁ N w
      (fun h => hwS (hN₁ w h)) (fun h => hwS (hN w h)) φ hφ hφc hbi v hv.continuous hv.level_invariant (Ψ.a w)
      (hv.hecke_eigen w hwS)
  · have hc := hv.central_eigen w hwS
    rw [rightConv_apply, rightConv_apply, ← integral_const_mul]
    congr 1
    funext x
    rw [mul_assoc, hc, mul_assoc]

end S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab (solution)
