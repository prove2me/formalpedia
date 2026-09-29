-- Prove2me | solution 1 for AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3ca25c5b-a714-53f9-b2b3-ae6f0d76677a

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u v

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv Divisor Divisor.degree Divisor.degree_single Divisor.IsPrincipal Divisor.mem_principal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.deg_eq_one_of_isAlgClosed exists_canonicalDivisor_genus_riemannRoch RROpens.exists_effective_sub_add_smul_single_mem_principal"
namespace FFRepGlue
p2m_open "AlgebraicCurve"

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_list_sum_single_eq (hdeg : ∀ v : Place K F, v.deg = 1) :
    ∀ E : Divisor K F, 0 ≤ E →
      ∃ l : List (Place K F), (l.map fun v => Finsupp.single v (1 : ℤ)).sum = E ∧ (l.length : ℤ) = Divisor.degree E := by
  classical
  intro E
  induction E using Finsupp.induction with
  | zero => intro _; exact ⟨[], by simp, by simp⟩
  | single_add v n E hv hn ih =>
      intro hE
      have hEv : ∀ w, 0 ≤ (Finsupp.single v n + E) w := fun w => hE w
      have hn0 : 0 ≤ n := by
        have := hEv v
        rw [Finsupp.add_apply, Finsupp.single_eq_same] at this
        have hEv0 : E v = 0 := by simpa [Finsupp.mem_support_iff] using hv
        omega
      have hE' : 0 ≤ E := by
        intro w
        rcases eq_or_ne w v with rfl | hw
        · have hEv0 : E w = 0 := by simpa [Finsupp.mem_support_iff] using hv
          simp [hEv0]
        · have := hEv w
          have hs : (Finsupp.single v n) w = 0 := Finsupp.single_eq_of_ne hw
          rw [Finsupp.add_apply, hs, zero_add] at this
          simpa using this
      obtain ⟨l, hl, hlen⟩ := ih hE'
      refine ⟨List.replicate n.toNat v ++ l, ?_, ?_⟩
      · rw [List.map_append, List.sum_append, hl, List.map_replicate, List.sum_replicate, ← Finsupp.smul_single_one v n]
        congr 1
        rw [← natCast_zsmul, Int.toNat_of_nonneg hn0]
      · rw [List.length_append, List.length_replicate, Nat.cast_add, hlen, map_add, Divisor.degree_single, hdeg, Nat.cast_one,
          mul_one, Int.toNat_of_nonneg hn0]

end AlgebraicCurve.FFRepGlue

open AlgebraicCurve.FFRepGlue in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (v₀ : Place K F) (D : Divisor K F) (hD : Divisor.degree D = 0) :
    ∃ l : List (Place K F),
      Divisor.IsPrincipal
        (D - ((l.map fun v => Finsupp.single v (1 : ℤ)).sum - (l.length : ℤ) • Finsupp.single v₀ 1)) := by
  classical
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨Kc, g, hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch K F

  obtain ⟨E, hE0, hE⟩ :=
    AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal g Kc hRR v₀ (hdeg1 v₀) D hD
  obtain ⟨f, hf, hfE⟩ := (Divisor.mem_principal.mp hE)
  obtain ⟨Pf, hPf, hPfdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf

  obtain ⟨l, hl, hlen⟩ := exists_list_sum_single_eq hdeg1 E (fun v => hE0 v)
  have hEeq : E = (D + (g : ℤ) • Finsupp.single v₀ 1) + Pf := by
    ext v
    have := hfE v
    rw [Finsupp.sub_apply] at this
    rw [Finsupp.add_apply, hPf v]
    linarith
  have hlen' : (l.length : ℤ) = g := by
    rw [hlen, hEeq, map_add, map_add, hD, hPfdeg, map_zsmul, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one,
      smul_eq_mul, mul_one, zero_add, add_zero]
  refine ⟨l, f⁻¹, inv_ne_zero hf, fun v => ?_⟩
  rw [hl, hlen', Place.ord_inv, ← hfE v]
  simp only [Finsupp.sub_apply, Finsupp.add_apply]
  ring

end S_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single
end P2MW
export P2MW.S_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single (solution)
