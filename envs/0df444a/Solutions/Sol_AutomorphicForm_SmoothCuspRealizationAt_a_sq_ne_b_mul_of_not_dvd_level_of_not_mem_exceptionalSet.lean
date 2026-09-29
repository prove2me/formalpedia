-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6ddc362e-2ebb-5b51-9a2f-31b91453b2ce

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.Meromorphic.Order
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero
import Theorems.Thm_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS10G

theorem solution_aux
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R) :
    ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet →
      Θ.a v ^ 2 ≠ Θ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) := by
  intro v hvl hve

  obtain ⟨hICC, -, hcontImp⟩ := AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine K
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)
    Θ.toRawCentral R
  have hχc := hcontImp hR
  obtain ⟨s, hs⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K _ hICC hχc
  have hs' : ∀ x : (AdeleRing (𝓞 K) K)ˣ,
      ‖((R.centralChar ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K x ^ s := by
    intro x
    first | exact hs x | simpa using hs x

  obtain ⟨S, hSs, hSfd⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  obtain ⟨-, hne, hcross⟩ := AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain K c u d₁ d₂ T hd hcov Θ Θ R R hR s hs' 1 2 one_pos one_lt_two S hSs hSfd
  obtain ⟨-, P, hPcov, -, hPagree⟩ := hcross rfl

  have hRmem : R.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) :=
    Submodule.subset_span ⟨1, funext fun z => by simp⟩
  have hPcov' : ∀ g : AdelicGL2 (𝓞 K) K, ∀ x y : AdelicGL2 (𝓞 K) K → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y :=
    fun g x y hx hy => hPcov g x y (Submodule.mem_sup_left hx) hy
  have hPself : P R.toFun R.toFun ≠ 0 := by
    rw [hPagree R.toFun R.toFun (Submodule.mem_sup_left hRmem) hRmem]
    exact hne

  have hw := AutomorphicForm.a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ R P s hPcov' hPself

  set t : ℝ := (1 - s) / 2 with ht
  obtain ⟨R', hR', hexc, -⟩ := AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul K c u d₁ d₂ T hd₁ Θ R hR t
  have hb' : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).level → v ∉ R'.exceptionalSet →
      ‖(Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).b v‖ = 1 := by
    intro v hvl' hve'
    rw [hexc] at hve'
    have hvl0 : ¬ v.asIdeal ∣ Θ.level := hvl'
    have hbv : ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - s) := (hw v hve' hvl0).2
    have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      positivity
    simp only [HeckeEigensystem.twist_b, norm_mul, norm_pow, Complex.norm_real, hbv]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hN.le _), ← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      show ((Ideal.absNorm v.asIdeal : ℝ)) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) from rfl,
      ← Real.rpow_add hN, ht]
    norm_num

  have hve' : v ∉ R'.exceptionalSet := by rw [hexc]; exact hve
  have hvl' : ¬ v.asIdeal ∣ (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).level := hvl
  have hgen := (LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet K c u d₁ d₂ T hc hd₁ hd hcov
    (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))) R' hR' hb' v hvl' hve').1

  intro h
  apply hgen
  simp only [HeckeEigensystem.twist_a, HeckeEigensystem.twist_b]
  rw [mul_pow, h]
  ring

end RS10G

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R) :
    ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet →
      Θ.a v ^ 2 ≠ Θ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) :=
  RS10G.solution_aux K c u d₁ d₂ T hc hd₁ hd hcov Θ R hR

end
end S_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet (solution)
