-- Prove2me | solution 1 for AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b024a1b9-bdc9-502f-9b10-c3f8817d4792

import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
import Theorems.Thm_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top
import Theorems.Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Pic0_exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent_correspondence
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.AnalyticCoord.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

namespace MtxTorus

open Submodule TateModule

variable {𝕜 : Type} [Field 𝕜] [CharZero 𝕜] {n r : ℕ}

private abbrev Q (Λ : Submodule ℤ (Fin n → 𝕜)) : Type := (Fin n → 𝕜) ⧸ Λ.toAddSubgroup

private theorem natCast_pow_ne_zero (p : ℕ) [Fact p.Prime] (k : ℕ) : ((p : 𝕜) ^ k) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

private theorem zsmul_pow_inv_smul (p : ℕ) [Fact p.Prime] (k : ℕ) (v : Fin n → 𝕜) :
    ((p ^ k : ℕ) : ℤ) • (((p : 𝕜) ^ k)⁻¹ • v) = v := by
  rw [← Int.cast_smul_eq_zsmul 𝕜, smul_smul, Int.cast_natCast, Nat.cast_pow,
    mul_inv_cancel₀ (natCast_pow_ne_zero p k), one_smul]

private theorem zsmul_pow_succ_inv_smul (p : ℕ) [Fact p.Prime] (k : ℕ) (v : Fin n → 𝕜) :
    ((p : ℕ) : ℤ) • (((p : 𝕜) ^ (k + 1))⁻¹ • v) = ((p : 𝕜) ^ k)⁻¹ • v := by
  rw [← Int.cast_smul_eq_zsmul 𝕜, smul_smul, Int.cast_natCast, pow_succ, mul_inv, ← mul_assoc,
    mul_comm (p : 𝕜), mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    mul_one]

private noncomputable def seq (Λ : Submodule ℤ (Fin n → 𝕜)) (p : ℕ) [Fact p.Prime]
    (e : Fin n → 𝕜) (he : e ∈ Λ) : TateModule p (Q Λ) :=
  ⟨fun k => QuotientAddGroup.mk (((p : 𝕜) ^ k)⁻¹ • e), fun k =>
    ⟨by
      rw [← QuotientAddGroup.mk_zsmul, zsmul_pow_inv_smul, QuotientAddGroup.eq_zero_iff]
      exact he,
     by rw [← QuotientAddGroup.mk_zsmul, zsmul_pow_succ_inv_smul]⟩⟩

private theorem seq_apply (Λ : Submodule ℤ (Fin n → 𝕜)) (p : ℕ) [Fact p.Prime]
    (e : Fin n → 𝕜) (he : e ∈ Λ) (k : ℕ) :
    ((seq Λ p e he : TateModule p (Q Λ)) : ℕ → Q Λ) k =
      QuotientAddGroup.mk' Λ.toAddSubgroup (((p : 𝕜) ^ k)⁻¹ • e) := rfl

variable (Λ : Submodule ℤ (Fin n → 𝕜)) (ε : Module.Basis (Fin r) ℤ ↥Λ) (p : ℕ) [Fact p.Prime]

private noncomputable def tuple (i : Fin r) : TateModule p (Q Λ) := seq Λ p ((ε i : Λ) : Fin n → 𝕜) (ε i).2

omit [CharZero 𝕜] in

private theorem linearIndependent_coe : LinearIndependent ℤ (fun i => ((ε i : Λ) : Fin n → 𝕜)) :=
  (ε.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))

omit [CharZero 𝕜] in

private theorem sum_zsmul_coe_eq (c : Fin r → ℤ) :
    ((∑ i, c i • ε i : Λ) : Fin n → 𝕜) = ∑ i, c i • ((ε i : Λ) : Fin n → 𝕜) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul_of_tower]

private theorem dvd_of_rel (k : ℕ) (a : Fin r → ℤ)
    (h : (∑ i, a i • ((tuple Λ ε p i : TateModule p (Q Λ)) : ℕ → Q Λ) k) = 0) :
    ∀ i, ((p ^ k : ℕ) : ℤ) ∣ a i := by

  have hmem : (∑ i, a i • (((p : 𝕜) ^ k)⁻¹ • ((ε i : Λ) : Fin n → 𝕜))) ∈ Λ := by
    have : QuotientAddGroup.mk' Λ.toAddSubgroup
        (∑ i, a i • (((p : 𝕜) ^ k)⁻¹ • ((ε i : Λ) : Fin n → 𝕜))) = 0 := by
      rw [← h, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]; rfl
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at this
    exact this

  set c : Fin r → ℤ := fun i => ε.repr ⟨_, hmem⟩ i with hc
  have hsum : (∑ i, a i • (((p : 𝕜) ^ k)⁻¹ • ((ε i : Λ) : Fin n → 𝕜))) =
      ∑ i, c i • ((ε i : Λ) : Fin n → 𝕜) := by
    have h1 := congrArg (fun x : Λ => (x : Fin n → 𝕜)) (ε.sum_repr ⟨_, hmem⟩)
    simp only at h1
    rw [sum_zsmul_coe_eq] at h1
    exact h1.symm
  have hrel : (∑ i, (a i - (p ^ k : ℕ) * c i) • ((ε i : Λ) : Fin n → 𝕜)) = 0 := by
    have h2 := congrArg (fun w => ((p ^ k : ℕ) : ℤ) • w) hsum
    beta_reduce at h2
    rw [Finset.smul_sum, Finset.smul_sum] at h2
    simp_rw [sub_smul, Finset.sum_sub_distrib, mul_smul, sub_eq_zero]
    calc ∑ i, a i • ((ε i : Λ) : Fin n → 𝕜)
        = ∑ i, ((p ^ k : ℕ) : ℤ) • (a i • (((p : 𝕜) ^ k)⁻¹ • ((ε i : Λ) : Fin n → 𝕜))) :=
          Finset.sum_congr rfl fun i _ => by rw [smul_comm ((p ^ k : ℕ) : ℤ) (a i), zsmul_pow_inv_smul]
      _ = _ := h2
  have hli := Fintype.linearIndependent_iff.mp (linearIndependent_coe Λ ε) _ hrel
  intro i
  exact ⟨c i, by have := hli i; omega⟩

private theorem exists_eq_level (k : ℕ) {m : Q Λ} (hm : m ∈ torsionBy ℤ (Q Λ) ((p ^ k : ℕ) : ℤ)) :
    ∃ a : Fin r → ℕ, (∑ i, (a i : ℤ) • ((tuple Λ ε p i : TateModule p (Q Λ)) : ℕ → Q Λ) k) = m := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective m
  rw [mem_torsionBy_iff] at hm
  have hv : ((p ^ k : ℕ) : ℤ) • v ∈ Λ := by
    rw [← Submodule.mem_toAddSubgroup, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul]
    exact hm
  set c : Fin r → ℤ := fun i => ε.repr ⟨_, hv⟩ i with hc
  have hsum : ((p ^ k : ℕ) : ℤ) • v = ∑ i, c i • ((ε i : Λ) : Fin n → 𝕜) := by
    have h1 := congrArg (fun x : Λ => (x : Fin n → 𝕜)) (ε.sum_repr ⟨_, hv⟩)
    simp only at h1
    rw [sum_zsmul_coe_eq] at h1
    exact h1.symm
  have hv' : v = ∑ i, c i • (((p : 𝕜) ^ k)⁻¹ • ((ε i : Λ) : Fin n → 𝕜)) := by
    have : v = ((p : 𝕜) ^ k)⁻¹ • (((p ^ k : ℕ) : ℤ) • v) := by
      rw [← Int.cast_smul_eq_zsmul 𝕜, smul_smul, Int.cast_natCast, Nat.cast_pow,
        inv_mul_cancel₀ (natCast_pow_ne_zero p k), one_smul]
    rw [this, hsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

  have hN : (0 : ℤ) < (p ^ k : ℕ) := by exact_mod_cast pow_pos (Fact.out : p.Prime).pos k
  refine ⟨fun i => (c i % (p ^ k : ℕ)).toNat, ?_⟩
  rw [hv']
  change _ = QuotientAddGroup.mk' Λ.toAddSubgroup (∑ i, c i • (((p : 𝕜) ^ k)⁻¹ • ((ε i : Λ) : Fin n → 𝕜)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have htor : ((p ^ k : ℕ) : ℤ) • ((tuple Λ ε p i : TateModule p (Q Λ)) : ℕ → Q Λ) k = 0 :=
    TateModule.torsion _ k
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne'), map_zsmul]
  change (c i % (p ^ k : ℕ)) • ((tuple Λ ε p i : TateModule p (Q Λ)) : ℕ → Q Λ) k =
    c i • ((tuple Λ ε p i : TateModule p (Q Λ)) : ℕ → Q Λ) k
  conv_rhs => rw [← Int.emod_add_mul_ediv (c i) ((p ^ k : ℕ) : ℤ), add_smul, mul_comm, mul_smul, htor,
    smul_zero, add_zero]

private theorem h1 : ∀ a : Fin r → ℤ,
    (∑ i, a i • ((tuple Λ ε p i : TateModule p (Q Λ)) : ℕ → Q Λ) 1) = 0 → ∀ i, (p : ℤ) ∣ a i := by
  intro a ha i
  have := dvd_of_rel Λ ε p 1 a ha i
  rwa [pow_one] at this

omit [CharZero 𝕜] [Fact p.Prime] in
private theorem coe_sum_apply (f : Fin r → TateModule p (Q Λ)) (k : ℕ) :
    ((∑ i, f i : TateModule p (Q Λ)) : ℕ → Q Λ) k = ∑ i, ((f i : TateModule p (Q Λ)) : ℕ → Q Λ) k := by
  rw [AddSubgroup.val_finsetSum]; exact Finset.sum_apply k Finset.univ _

private theorem linearIndependent_tuple : LinearIndependent ℤ_[p] (tuple Λ ε p) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hlev : ∀ k i, ((p ^ k : ℕ) : ℤ) ∣ ((g i).appr k : ℤ) := fun k =>
    dvd_of_rel Λ ε p k (fun i => ((g i).appr k : ℤ)) (by
      have hk : ((∑ i, g i • tuple Λ ε p i : TateModule p (Q Λ)) : ℕ → Q Λ) k = 0 := by
        rw [hg, TateModule.coe_zero, Pi.zero_apply]
      rw [coe_sum_apply] at hk
      simp only [TateModule.smul_apply] at hk
      exact hk)
  intro i
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [map_zero, toZModPow_eq_appr, ZMod.natCast_eq_zero_iff]
  exact Int.natCast_dvd_natCast.mp (hlev k i)

private theorem mem_span_tuple (z : TateModule p (Q Λ)) :
    ∃ s : Fin r → ℤ_[p], (∑ i, s i • tuple Λ ε p i) = z := by
  choose a ha using fun k => exists_eq_level Λ ε p k (proj_mem_torsionBy k z)
  have hcompat : ∀ k i, ((p ^ k : ℕ) : ℤ) ∣ (a (k + 1) i : ℤ) - a k i := fun k =>
    dvd_of_rel Λ ε p k (fun i => (a (k + 1) i : ℤ) - a k i) (by
      simp_rw [sub_smul, Finset.sum_sub_distrib, ha k, sub_eq_zero, proj_apply,
        ← compat z k, ← proj_apply (k + 1) z, ← ha (k + 1), Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, compat])
  have hci : ∀ (i : Fin r) (k : ℕ),
      (p : ℤ) ^ k ∣ (fun k => (a k i : ℤ)) (k + 1) - (fun k => (a k i : ℤ)) k :=
    fun i k => by rw [← Nat.cast_pow]; exact hcompat k i
  refine ⟨fun i => PadicInt.ofIntSeq (fun k => (a k i : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (hci i)), Subtype.ext (funext fun k => ?_)⟩
  rw [← proj_apply k z, ← ha k, coe_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TateModule.smul_apply]
  refine natCast_smul_eq_of_zmod_eq (TateModule.torsion (tuple Λ ε p i) k) ?_
  rw [← toZModPow_eq_appr,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a k i : ℤ)) p (hci i) k, Int.cast_natCast]

private noncomputable def basis : Module.Basis (Fin r) ℤ_[p] (TateModule p (Q Λ)) :=
  Module.Basis.mk (linearIndependent_tuple Λ ε p)
    (by rw [top_le_span_range_iff_forall_exists_fun]; exact mem_span_tuple Λ ε p)

private theorem basis_apply (i : Fin r) : basis Λ ε p i = tuple Λ ε p i := by
  rw [basis, Module.Basis.mk_apply]

private theorem intCast_smul_apply {M : Type} [AddCommGroup M] (z : ℤ) (x : TateModule p M) (k : ℕ) :
    (((z : ℤ_[p]) • x : TateModule p M) : ℕ → M) k = z • (x : ℕ → M) k := by
  induction z using Int.induction_on with
  | zero => rw [Int.cast_zero, zero_smul, zero_smul, TateModule.coe_zero, Pi.zero_apply]
  | succ m ih =>
    rw [Int.cast_add, Int.cast_one, add_smul, one_smul, TateModule.coe_add, Pi.add_apply, ih,
      add_smul, one_smul]
  | pred m ih =>
    rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul, TateModule.coe_sub, Pi.sub_apply, ih,
      sub_smul, one_smul]

private theorem mtx_torus (f : (Fin n → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) (hf : ∀ u ∈ Λ, f u ∈ Λ) :
    ∃ c : Module.Basis (Fin r) ℤ_[p] (TateModule p ((Fin n → 𝕜) ⧸ Λ.toAddSubgroup)),
      LinearMap.toMatrix c c
          (TateModule.rep p ((Fin n → 𝕜) ⧸ Λ.toAddSubgroup)
            (Module.End ℤ ((Fin n → 𝕜) ⧸ Λ.toAddSubgroup))
            (QuotientAddGroup.map Λ.toAddSubgroup Λ.toAddSubgroup f.toAddMonoidHom
              (fun u hu => hf u hu)).toIntLinearMap) =
        (LinearMap.toMatrix ε ε ((f.restrictScalars ℤ).restrict hf)).map (Int.castRingHom ℤ_[p]) := by
  set N := LinearMap.toMatrix ε ε ((f.restrictScalars ℤ).restrict hf) with hN
  refine ⟨basis Λ ε p, Matrix.ext fun i j => ?_⟩

  have himg : TateModule.rep p (Q Λ) (Module.End ℤ (Q Λ))
        (QuotientAddGroup.map Λ.toAddSubgroup Λ.toAddSubgroup f.toAddMonoidHom
          (fun u hu => hf u hu)).toIntLinearMap (basis Λ ε p j) =
      ∑ i, ((N i j : ℤ) : ℤ_[p]) • basis Λ ε p i := by
    refine Subtype.ext (funext fun k => ?_)
    rw [rep_apply, coe_sum_apply, basis_apply]
    simp_rw [intCast_smul_apply, basis_apply]
    change (QuotientAddGroup.map Λ.toAddSubgroup Λ.toAddSubgroup f.toAddMonoidHom
        (fun u hu => hf u hu)) (QuotientAddGroup.mk (((p : 𝕜) ^ k)⁻¹ • ((ε j : Λ) : Fin n → 𝕜))) =
      ∑ i, N i j • QuotientAddGroup.mk' Λ.toAddSubgroup (((p : 𝕜) ^ k)⁻¹ • ((ε i : Λ) : Fin n → 𝕜))
    rw [QuotientAddGroup.map_mk]
    change QuotientAddGroup.mk' Λ.toAddSubgroup (f (((p : 𝕜) ^ k)⁻¹ • ((ε j : Λ) : Fin n → 𝕜))) = _
    have hfj : f ((ε j : Λ) : Fin n → 𝕜) = ∑ i, N i j • ((ε i : Λ) : Fin n → 𝕜) := by
      have h1 := congrArg (fun x : Λ => (x : Fin n → 𝕜))
        (ε.sum_repr (((f.restrictScalars ℤ).restrict hf) (ε j)))
      have h3 : ((((f.restrictScalars ℤ).restrict hf) (ε j) : Λ) : Fin n → 𝕜) =
          f ((ε j : Λ) : Fin n → 𝕜) := rfl
      beta_reduce at h1
      rw [sum_zsmul_coe_eq, h3] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hN, LinearMap.toMatrix_apply]
    rw [map_smul, hfj, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, map_zsmul]
  rw [LinearMap.toMatrix_apply, himg, (basis Λ ε p).repr_sum_self]
  simp [Matrix.map_apply]

end MtxTorus

namespace TateTransfer

section Functor

variable {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (p : ℕ) [Fact p.Prime]

private def tateMapT (f : M →+ M') : TateModule p M →ₗ[ℤ_[p]] TateModule p M' where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f ((x : ℕ → M) n + (y : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    exact map_add f _ _)
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → M) n)
    exact map_zsmul f _ _)

variable {p}

private theorem tateMapT_injective (f : M →+ M') (hf : Function.Injective f) :
    Function.Injective (tateMapT p f) := fun _ _ h =>
  Subtype.ext (funext fun n => hf (congrArg (fun z : TateModule p M' => (z : ℕ → M') n) h))

private theorem tateMapT_surjective (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ n : ℕ, n ≠ 0 → ∀ z : M', (n : ℤ) • z = 0 → ∃ y, f y = z) :
    Function.Surjective (tateMapT p f) := by
  intro y
  choose x hx using fun n =>
    hsurj (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero) ((y : ℕ → M') n)
      (TateModule.torsion y n)
  refine ⟨⟨x, fun n => ⟨hf ?_, hf ?_⟩⟩, Subtype.ext (funext fun n => hx n)⟩
  · rw [map_zsmul, hx, map_zero, TateModule.torsion]
  · rw [map_zsmul, hx, hx, TateModule.compat]

private noncomputable def tateEquivT (u : M →+ M') (hu : Function.Injective u)
    (hsurj : ∀ n : ℕ, n ≠ 0 → ∀ z : M', (n : ℤ) • z = 0 → ∃ y, u y = z) :
    TateModule p M ≃ₗ[ℤ_[p]] TateModule p M' :=
  LinearEquiv.ofBijective (tateMapT p u) ⟨tateMapT_injective u hu, tateMapT_surjective u hu hsurj⟩

private theorem tateMapT_tateMapT_of_comm (u : M →+ M') (f : M →+ M) (g : M' →+ M')
    (h : ∀ m, u (f m) = g (u m)) (x : TateModule p M) :
    tateMapT p u (tateMapT p f x) = tateMapT p g (tateMapT p u x) :=
  Subtype.ext (funext fun _ => h _)

private theorem rep_eq_tateMapT (f : Module.End ℤ M) (x : TateModule p M) :
    TateModule.rep p M (Module.End ℤ M) f x = tateMapT p f.toAddMonoidHom x :=
  Subtype.ext (funext fun _ => rfl)

end Functor

end TateTransfer

private theorem mtx_tate_transfer {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (ι : A →+ B) (hinj : Function.Injective ι)
    (hsurj : ∀ n : ℕ, n ≠ 0 → ∀ z : B, (n : ℤ) • z = 0 → ∃ y, ι y = z)
    (f : Module.End ℤ A) (g : Module.End ℤ B) (hfg : ∀ y, ι (f y) = g (ι y))
    (p : ℕ) [Fact p.Prime] {r : ℕ} (c : Module.Basis (Fin r) ℤ_[p] (TateModule p B)) :
    ∃ c' : Module.Basis (Fin r) ℤ_[p] (TateModule p A),
      LinearMap.toMatrix c' c' (TateModule.rep p A (Module.End ℤ A) f) =
        LinearMap.toMatrix c c (TateModule.rep p B (Module.End ℤ B) g) := by
  let E : TateModule p A ≃ₗ[ℤ_[p]] TateModule p B := TateTransfer.tateEquivT ι hinj hsurj
  have hE : ∀ x, E (TateModule.rep p A (Module.End ℤ A) f x) =
      TateModule.rep p B (Module.End ℤ B) g (E x) := fun x => by
    show TateTransfer.tateMapT p ι (TateModule.rep p A (Module.End ℤ A) f x) =
      TateModule.rep p B (Module.End ℤ B) g (TateTransfer.tateMapT p ι x)
    rw [TateTransfer.rep_eq_tateMapT, TateTransfer.rep_eq_tateMapT]
    exact TateTransfer.tateMapT_tateMapT_of_comm ι f.toAddMonoidHom g.toAddMonoidHom (fun y => hfg y) x
  refine ⟨c.map E.symm, Matrix.ext fun i j => ?_⟩
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply,
    Module.Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply, hE,
    LinearEquiv.apply_symm_apply]

section MtxComplex

open AlgebraicCurve
open scoped Manifold ContDiff

private theorem finrank_real_fin_complex (g : ℕ) : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

private theorem mtx_complex
    {F : Type} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    {F' : Type} [Field F'] [Algebra ℂ F'] [IsCurveOver ℂ F']
    (φ ψ : F →ₐ[ℂ] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong ℂ ψ) (hFI : FundamentalIdentityAlong ℂ φ hφ)
    (hNψ : NormFormulaAlong ℂ ψ hψfin) :
    ∃ M : Matrix (Fin (2 * genusFF ℂ F)) (Fin (2 * genusFF ℂ F)) ℤ,
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ b : Module.Basis (Fin (2 * genusFF ℂ F)) ℤ_[p] (TateModule p (Pic0 ℂ F)),
          LinearMap.toMatrix b b (TateModule.rep p (Pic0 ℂ F) (Module.End ℤ (Pic0 ℂ F))
            (Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ).toIntLinearMap) =
            M.map (Int.castRingHom ℤ_[p]) := by
  classical

  obtain ⟨t, ht, hfd, -⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := ℂ) (F := F)
  have hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F := ⟨t, ht, hfd⟩
  haveI : HasCanonicalDivisor (K := ℂ) (F := F) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

  obtain ⟨tP, cP, hM, hC, hT2, hConn, hF⟩ :=
    AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex F hfg
  letI : TopologicalSpace (Place ℂ F) := tP
  letI : ChartedSpace ℂ (Place ℂ F) := cP
  haveI := hM
  haveI := hC
  haveI := hT2
  haveI := hConn
  obtain ⟨P₀⟩ := (ConnectedSpace.toNonempty : Nonempty (Place ℂ F))

  obtain ⟨hfin, hrk⟩ :=
    AlgebraicCurve.finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed (K := ℂ) (F := F)
  rw [AlgebraicCurve.regularDiffs_eq_regularDifferentials] at hfin hrk
  haveI := hfin
  set g : ℕ := genusFF ℂ F with hg
  let bΩ : Module.Basis (Fin g) ℂ ↥(regularDifferentials ℂ F) := Module.finBasisOfFinrankEq ℂ _ hrk

  have hmem : ∀ j : Fin g,
      Differential.correspondence φ ψ (bΩ j : Ω[F⁄ℂ]) ∈ regularDifferentials ℂ F := fun j =>
    AlgebraicCurve.Differential.correspondence_mem_regularDifferentials ℂ F F' hfg φ ψ hφ hψ hψfin
      (bΩ j).2
  let S : Matrix (Fin g) (Fin g) ℂ := fun k j => bΩ.repr ⟨_, hmem j⟩ k
  have hS : ∀ j : Fin g, Differential.correspondence φ ψ (bΩ j : Ω[F⁄ℂ]) =
      ∑ k : Fin g, S k j • (bΩ k : Ω[F⁄ℂ]) := fun j => by
    have h1 := congrArg (fun x : ↥(regularDifferentials ℂ F) => (x : Ω[F⁄ℂ])) (bΩ.sum_repr ⟨_, hmem j⟩)
    simp only at h1
    rw [← h1, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Submodule.coe_smul]

  obtain ⟨hΛ, hAJ⟩ :=
    AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice F hfg hF F' φ ψ hφ hψ
      hψfin bΩ P₀ S hS
  set Λ : Submodule ℤ (Fin g → ℂ) := pathPeriodLattice (fun i => (bΩ i : Ω[F⁄ℂ])) with hΛdef

  obtain ⟨hdisc, hspan⟩ :=
    AlgebraicCurve.discreteTopology_pathPeriodLattice_and_span_eq_top F hfg hF bΩ
  haveI : DiscreteTopology ↥Λ := hdisc
  haveI hZ : IsZLattice ℝ Λ := ⟨hspan⟩
  haveI : Module.Free ℤ ↥Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ ↥Λ := ZLattice.module_finite ℝ Λ
  have hrank : Module.finrank ℤ ↥Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, finrank_real_fin_complex]
  let ε : Module.Basis (Fin (2 * g)) ℤ ↥Λ := Module.finBasisOfFinrankEq ℤ _ hrank
  have hΛ' : ∀ u ∈ Λ, Matrix.vecMulLinear S u ∈ Λ := fun u hu => by
    rw [Matrix.vecMulLinear_apply]; exact hΛ u hu

  refine ⟨LinearMap.toMatrix ε ε (((Matrix.vecMulLinear S).restrictScalars ℤ).restrict hΛ'),
    fun p _ => ?_⟩

  obtain ⟨c, hc⟩ := MtxTorus.mtx_torus Λ ε p (Matrix.vecMulLinear S) hΛ'

  let AJ : Divisor ℂ F →+ (Fin g → ℂ) := abelJacobiDiv (fun i => (bΩ i : Ω[F⁄ℂ])) P₀
  let AJq : ↥(Divisor.degZero (K := ℂ) (F := F)) →+ (Fin g → ℂ) ⧸ Λ.toAddSubgroup :=
    (QuotientAddGroup.mk' Λ.toAddSubgroup).comp (AJ.comp (Divisor.degZero (K := ℂ) (F := F)).subtype)
  have hAJq : ∀ D : ↥(Divisor.degZero (K := ℂ) (F := F)),
      AJq D = QuotientAddGroup.mk' Λ.toAddSubgroup (AJ (D : Divisor ℂ F)) := fun D => rfl
  have hker : (Divisor.principal (K := ℂ) (F := F)).addSubgroupOf (Divisor.degZero (K := ℂ) (F := F)) ≤
      AJq.ker := by
    intro D hD
    rw [AddMonoidHom.mem_ker, hAJq, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact AlgebraicCurve.abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal F hfg hF (fun i => bΩ i) P₀
      (D : Divisor ℂ F) (AddSubgroup.mem_addSubgroupOf.mp hD)
  let ι : Pic0 ℂ F →+ (Fin g → ℂ) ⧸ Λ.toAddSubgroup := QuotientAddGroup.lift _ AJq hker
  have hι_mk : ∀ D : ↥(Divisor.degZero (K := ℂ) (F := F)),
      ι (Pic0.mk D) = QuotientAddGroup.mk' Λ.toAddSubgroup (AJ (D : Divisor ℂ F)) := fun D => rfl

  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr fun x hx => ?_
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [hι_mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hx
    have hpr : Divisor.IsPrincipal (D : Divisor ℂ F) :=
      AlgebraicCurve.Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice F hfg hF bΩ P₀ (D : Divisor ℂ F)
        (Divisor.mem_degZero.mp D.2) hx
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hpr)

  have hsurj : ∀ m : ℕ, m ≠ 0 → ∀ z : (Fin g → ℂ) ⧸ Λ.toAddSubgroup, (m : ℤ) • z = 0 → ∃ y, ι y = z := by
    intro m _ z _
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨D, hD0, hDu⟩ :=
      AlgebraicCurve.exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice F hfg hF bΩ P₀ u
    refine ⟨Pic0.mk ⟨D, Divisor.mem_degZero.mpr hD0⟩, ?_⟩
    rw [hι_mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
    exact hDu

  have heq : ∀ y, ι ((Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ).toIntLinearMap y) =
      (QuotientAddGroup.map Λ.toAddSubgroup Λ.toAddSubgroup (Matrix.vecMulLinear S).toAddMonoidHom
        (fun u hu => hΛ' u hu)).toIntLinearMap (ι y) := by
    intro y
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
    change ι (Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ (Pic0.mk D)) =
      QuotientAddGroup.map Λ.toAddSubgroup Λ.toAddSubgroup (Matrix.vecMulLinear S).toAddMonoidHom
        (fun u hu => hΛ' u hu) (ι (Pic0.mk D))
    rw [Pic0.correspondence_mk, hι_mk, hι_mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.map_mk, QuotientAddGroup.eq_iff_sub_mem]
    change AJ _ - Matrix.vecMulLinear S (AJ (D : Divisor ℂ F)) ∈ Λ.toAddSubgroup
    rw [Matrix.vecMulLinear_apply, Submodule.mem_toAddSubgroup, Pic0.coe_degZeroCorrespondence]
    exact hAJ (D : Divisor ℂ F) (Divisor.mem_degZero.mp D.2)

  obtain ⟨c', hc'⟩ := mtx_tate_transfer ι hinj hsurj _ _ heq p c
  exact ⟨c', hc'.trans hc⟩

end MtxComplex

open AlgebraicCurve
open scoped Manifold ContDiff TensorProduct

universe u v w x

section Glue

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem cfd_isIntegral_of_finiteAlong (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) :
    φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := hfin
  intro y
  exact Algebra.IsIntegral.isIntegral (R := F) y

private theorem cfd_hfg [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  obtain ⟨t, ht, hfd, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  exact ⟨t, ht, hfd⟩

private theorem cfd_essFiniteType
    (hfg : ∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨t, ht, hfd⟩ := hfg
  exact AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional ht hfd

end Glue

section Lift

variable {K₀ F₀ K₁ F₁ : Type*} [Field K₀] [Field F₀] [Field K₁] [Field F₁]
  [Algebra K₀ F₀] [Algebra K₁ F₁] [Algebra F₀ F₁]

private def cfdIsLift (L : Place K₀ F₀ → Place K₁ F₁) : Prop :=
  (∀ v : Place K₀ F₀, (L v).toValuationSubring.comap (algebraMap F₀ F₁) = v.toValuationSubring) ∧
  (∀ (v : Place K₀ F₀) (f : F₀), (L v).ord (algebraMap F₀ F₁ f) = v.ord f) ∧
  (∀ (v : Place K₀ F₀) (w : Place K₁ F₁),
    w.toValuationSubring.comap (algebraMap F₀ F₁) = v.toValuationSubring → w = L v)

private theorem cfd_exists_lift [Algebra K₀ K₁] [Algebra K₀ F₁] [IsScalarTower K₀ K₁ F₁] [IsScalarTower K₀ F₀ F₁]
    [IsAlgClosed K₀] [IsCurveOver K₀ F₀]
    (hfg₀ : ∃ t : F₀, Transcendental K₀ t ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({t} : Set F₀)) F₀)
    (hfg₁ : ∃ t : F₁, Transcendental K₁ t ∧
      FiniteDimensional (IntermediateField.adjoin K₁ ({t} : Set F₁)) F₁)
    (hgen : IntermediateField.adjoin K₁ (Set.range (algebraMap F₀ F₁)) = ⊤) :
    ∃ L : Place K₀ F₀ → Place K₁ F₁, cfdIsLift L := by
  choose L hL using fun v : Place K₀ F₀ =>
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
      K₀ F₀ K₁ F₁ hfg₀ hfg₁ hgen v
  exact ⟨L, fun v => (hL v).1, fun v f => (hL v).2.1 f, fun v w hw => (hL v).2.2 w hw⟩

variable {L : Place K₀ F₀ → Place K₁ F₁}

private theorem cfdIsLift.lift_injective (hL : cfdIsLift L) : Function.Injective L := by
  intro v v' h
  apply AlgebraicCurve.Place.ext
  rw [← hL.1 v, ← hL.1 v', h]

private theorem cfdIsLift.notMem_range (hL : cfdIsLift L) (w : Place K₁ F₁)
    (hw : ∀ v : Place K₀ F₀, w.toValuationSubring.comap (algebraMap F₀ F₁) ≠ v.toValuationSubring) :
    w ∉ Set.range L := by
  rintro ⟨v, rfl⟩
  exact hw v (hL.1 v)

private theorem cfdIsLift.mapDomain_apply_of_comap_eq (hL : cfdIsLift L) (D : Divisor K₀ F₀)
    (w : Place K₁ F₁) (v : Place K₀ F₀)
    (hw : w.toValuationSubring.comap (algebraMap F₀ F₁) = v.toValuationSubring) :
    Finsupp.mapDomain L D w = D v := by
  rw [hL.2.2 v w hw, Finsupp.mapDomain_apply hL.lift_injective]

private theorem cfdIsLift.mapDomain_apply_eq_zero (hL : cfdIsLift L) (D : Divisor K₀ F₀) (w : Place K₁ F₁)
    (hw : ∀ v : Place K₀ F₀, w.toValuationSubring.comap (algebraMap F₀ F₁) ≠ v.toValuationSubring) :
    Finsupp.mapDomain L D w = 0 :=
  Finsupp.mapDomain_notin_range _ _ (hL.notMem_range w hw)

end Lift

section Deg

private theorem cfd_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (v : Place K F) : v.deg = 1 := by
  refine AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed v ?_
  haveI : Module.Finite K v.ResidueField := (inferInstance : v.FiniteResidue).finite
  exact Module.finrank_pos.ne'

private theorem cfd_degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (D : Divisor K F) : Divisor.degree D = D.sum fun _ n => n := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, hD, hE, Finsupp.sum_add_index'] <;> simp
  | single v n => rw [Divisor.degree_single, cfd_deg_eq_one]; simp

private theorem cfd_degree_mapDomain {K₀ F₀ K₁ F₁ : Type*} [Field K₀] [Field F₀] [Field K₁] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₁ F₁] [IsAlgClosed K₀] [IsAlgClosed K₁] [IsCurveOver K₀ F₀] [IsCurveOver K₁ F₁]
    (L : Place K₀ F₀ → Place K₁ F₁) (D : Divisor K₀ F₀) :
    Divisor.degree (Finsupp.mapDomain L D) = Divisor.degree D := by
  rw [cfd_degree_eq_sum, cfd_degree_eq_sum, Finsupp.sum_mapDomain_index] <;> simp

private theorem cfd_mapDomain_mem_degZero {K₀ F₀ K₁ F₁ : Type*} [Field K₀] [Field F₀] [Field K₁] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₁ F₁] [IsAlgClosed K₀] [IsAlgClosed K₁] [IsCurveOver K₀ F₀] [IsCurveOver K₁ F₁]
    (L : Place K₀ F₀ → Place K₁ F₁) {D : Divisor K₀ F₀} (hD : D ∈ Divisor.degZero (K := K₀) (F := F₀)) :
    Finsupp.mapDomain L D ∈ Divisor.degZero (K := K₁) (F := F₁) := by
  rw [Divisor.mem_degZero, cfd_degree_mapDomain]
  exact Divisor.mem_degZero.mp hD

private theorem cfd_exists_div {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    {f : F} (hf : f ≠ 0) :
    ∃ E : Divisor K F, (∀ v : Place K F, E v = v.ord f) ∧ E ∈ Divisor.degZero (K := K) (F := F) ∧
      E ∈ Divisor.principal (K := K) (F := F) := by
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  exact ⟨E, hE, Divisor.mem_degZero.mpr hdeg, ⟨f, hf, hE⟩⟩

end Deg

private theorem cfd_torsion_mem_range
    (K₀ F₀ K₁ F₁ : Type*) [Field K₀] [Field F₀] [Field K₁] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₁ F₁] [Algebra K₀ K₁] [Algebra F₀ F₁] [Algebra K₀ F₁]
    [IsScalarTower K₀ K₁ F₁] [IsScalarTower K₀ F₀ F₁]
    [IsAlgClosed K₀] [CharZero K₀] [IsAlgClosed K₁] [IsCurveOver K₀ F₀] [IsCurveOver K₁ F₁]
    (hfg₀ : ∃ t : F₀, Transcendental K₀ t ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({t} : Set F₀)) F₀)
    (hfg₁ : ∃ t : F₁, Transcendental K₁ t ∧
      FiniteDimensional (IntermediateField.adjoin K₁ ({t} : Set F₁)) F₁)
    (hgen : IntermediateField.adjoin K₁ (Set.range (algebraMap F₀ F₁)) = ⊤)
    (ι : Pic0 K₀ F₀ →+ Pic0 K₁ F₁)
    (hι : ∀ (D : Divisor.degZero (K := K₀) (F := F₀)) (D' : Divisor.degZero (K := K₁) (F := F₁)),
      (∀ (v' : Place K₁ F₁) (v : Place K₀ F₀),
        v'.toValuationSubring.comap (algebraMap F₀ F₁) = v.toValuationSubring →
          (D' : Divisor K₁ F₁) v' = (D : Divisor K₀ F₀) v) →
      (∀ v' : Place K₁ F₁,
        (∀ v : Place K₀ F₀, v'.toValuationSubring.comap (algebraMap F₀ F₁) ≠ v.toValuationSubring) →
          (D' : Divisor K₁ F₁) v' = 0) →
      ι (Pic0.mk D) = Pic0.mk D')
    (n : ℕ) (hn : n ≠ 0) (z : Pic0 K₁ F₁) (hz : (n : ℤ) • z = 0) : ∃ y, ι y = z := by
  obtain ⟨D', rfl⟩ := Pic0.mk_surjective z

  have hprin : ((n : ℤ) • D' : Divisor.degZero (K := K₁) (F := F₁)) ∈
      (Divisor.principal (K := K₁) (F := F₁)).addSubgroupOf (Divisor.degZero (K := K₁) (F := F₁)) := by
    rw [← QuotientAddGroup.eq_zero_iff]
    exact hz
  rw [AddSubgroup.mem_addSubgroupOf] at hprin
  obtain ⟨g', hg'0, hg'⟩ := (Divisor.mem_principal.mp hprin : Divisor.IsPrincipal _)
  have hD' : ∃ g' : F₁, g' ≠ 0 ∧ ∀ v' : Place K₁ F₁, (n : ℤ) * (D' : Divisor K₁ F₁) v' = v'.ord g' := by
    refine ⟨g', hg'0, fun v' => ?_⟩
    have := hg' v'
    simpa using this
  obtain ⟨D, h', hh'0, ⟨g, hg0, hgD⟩, hagree, hvanish⟩ :=
    AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension K₀ F₀ K₁ F₁ hfg₀ hfg₁ hgen
      n hn (D' : Divisor K₁ F₁) hD'

  have hD0 : D ∈ Divisor.degZero (K := K₀) (F := F₀) := by
    obtain ⟨Eg, hEg, hEg0, -⟩ := cfd_exists_div (K := K₀) hg0
    have hnD : (n : ℤ) • D = Eg := by
      ext v
      rw [Finsupp.smul_apply, smul_eq_mul, hgD v, hEg v]
    rw [Divisor.mem_degZero]
    have h1 : Divisor.degree ((n : ℤ) • D) = 0 := by rw [hnD]; exact Divisor.mem_degZero.mp hEg0
    rw [map_zsmul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hn)

  obtain ⟨Eh, hEh, hEh0, hEhprin⟩ := cfd_exists_div (K := K₁) hh'0
  have hE'0 : (D' : Divisor K₁ F₁) - Eh ∈ Divisor.degZero (K := K₁) (F := F₁) := sub_mem D'.2 hEh0
  refine ⟨Pic0.mk ⟨D, hD0⟩, ?_⟩
  rw [hι ⟨D, hD0⟩ ⟨(D' : Divisor K₁ F₁) - Eh, hE'0⟩ ?_ ?_]
  ·
    show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    convert hEhprin using 1
    ext v
    simp [hEh v]
  · intro v' v hv
    simp only [Finsupp.sub_apply]
    rw [hagree v v' hv, hEh v']
    ring
  · intro v' hv'
    simp only [Finsupp.sub_apply]
    rw [hvanish v' hv', hEh v', sub_self]

section Roof

variable {K₀ F₀ R₀ K₁ F₁ R₁ : Type*}
  [Field K₀] [Field F₀] [Field R₀] [Field K₁] [Field F₁] [Field R₁]
  [Algebra K₀ F₀] [Algebra K₀ R₀] [Algebra K₁ F₁] [Algebra K₁ R₁] [Algebra F₀ F₁] [Algebra R₀ R₁]
  {LF : Place K₀ F₀ → Place K₁ F₁} {LR : Place K₀ R₀ → Place K₁ R₁}
  (hLF : cfdIsLift LF) (hLR : cfdIsLift LR)
  (θ₀ : F₀ →ₐ[K₀] R₀) (hθ₀ : θ₀.toRingHom.IsIntegral) (θ₁ : F₁ →ₐ[K₁] R₁) (hθ₁ : θ₁.toRingHom.IsIntegral)
  (hsq : ∀ f : F₀, θ₁ (algebraMap F₀ F₁ f) = algebraMap R₀ R₁ (θ₀ f))

include hLF hLR hsq in

private theorem cfd_restrictAlong_lift (w : Place K₀ R₀) :
    (LR w).restrictAlong θ₁ hθ₁ = LF (w.restrictAlong θ₀ hθ₀) := by
  apply hLF.2.2
  have h₁ : ((LR w).restrictAlong θ₁ hθ₁).toValuationSubring = (LR w).toValuationSubring.comap θ₁.toRingHom :=
    rfl
  have h₀ : (w.restrictAlong θ₀ hθ₀).toValuationSubring = w.toValuationSubring.comap θ₀.toRingHom := rfl
  rw [h₁, h₀, ValuationSubring.comap_comap, ← hLR.1 w, ValuationSubring.comap_comap]
  congr 1
  ext f
  simp [hsq f]

include hLF hLR hθ₀ hθ₁ hsq in

private theorem cfd_ramificationIndexAlong_lift (w : Place K₀ R₀) :
    (LR w).ramificationIndexAlong θ₁ = w.ramificationIndexAlong θ₀ := by

  obtain ⟨f, hf0, hf⟩ : ∃ f : F₀, f ≠ 0 ∧ w.ord (θ₀ f) = w.ramificationIndexAlong θ₀ := by
    letI := algebraAlong θ₀
    haveI := isScalarTower_along θ₀
    haveI := isIntegral_along θ₀ hθ₀
    exact w.exists_ord_eq_ramificationIndex (F := F₀)
  have hn : (w.restrictAlong θ₀ hθ₀).ord f ≠ 0 := by
    intro h0
    have := Place.ord_restrictAlong θ₀ hθ₀ w f
    rw [h0, mul_zero, hf] at this
    have h1 := AlgebraicCurve.Place.one_le_ramificationIndexAlong θ₀ hθ₀ w
    omega

  have hA : (LR w).ord (θ₁ (algebraMap F₀ F₁ f)) =
      ((LR w).ramificationIndexAlong θ₁ : ℤ) * (w.restrictAlong θ₀ hθ₀).ord f := by
    rw [Place.ord_restrictAlong θ₁ hθ₁, cfd_restrictAlong_lift hLF hLR θ₀ hθ₀ θ₁ hθ₁ hsq, hLF.2.1]
  have hB : (LR w).ord (θ₁ (algebraMap F₀ F₁ f)) =
      (w.ramificationIndexAlong θ₀ : ℤ) * (w.restrictAlong θ₀ hθ₀).ord f := by
    rw [hsq, hLR.2.1, Place.ord_restrictAlong θ₀ hθ₀]
  have := mul_right_cancel₀ hn (hA.symm.trans hB)
  exact_mod_cast this

private theorem cfd_inertiaDegAlong_eq_one {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
    [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K R] (θ : F →ₐ[K] R) (hθ : θ.toRingHom.IsIntegral)
    (w : Place K R) : w.inertiaDegAlong θ hθ = 1 := by
  have h : (w.restrictAlong θ hθ).deg * w.inertiaDegAlong θ hθ = w.deg := by
    letI := algebraAlong θ
    haveI := isScalarTower_along θ
    haveI := isIntegral_along θ hθ
    exact w.deg_restrict_mul_inertiaDeg (F := F)
  rwa [cfd_deg_eq_one, cfd_deg_eq_one, one_mul] at h

include hLF hLR hsq in

private theorem cfd_fiberAlong_lift [DecidableEq (Place K₁ R₁)] [IsAlgClosed K₀] [IsAlgClosed K₁]
    [IsCurveOver K₀ F₀] [IsCurveOver K₀ R₀] [IsCurveOver K₁ F₁] [IsCurveOver K₁ R₁]
    (hfin₀ : FiniteAlong K₀ θ₀) (hsep₀ : SeparableAlong K₀ θ₀)
    (hfin₁ : FiniteAlong K₁ θ₁) (hsep₁ : SeparableAlong K₁ θ₁)
    (hrk : finrankAlong K₁ θ₁ = finrankAlong K₀ θ₀) (u : Place K₀ F₀) :
    Place.fiberAlong θ₁ hθ₁ (LF u) = (Place.fiberAlong θ₀ hθ₀ u).image LR := by
  have hsub : (Place.fiberAlong θ₀ hθ₀ u).image LR ⊆ Place.fiberAlong θ₁ hθ₁ (LF u) := by
    intro W hW
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hW
    rw [Place.mem_fiberAlong] at hw ⊢
    rw [cfd_restrictAlong_lift hLF hLR θ₀ hθ₀ θ₁ hθ₁ hsq, hw]
  refine (Finset.Subset.antisymm ?_ hsub)
  by_contra hnot
  obtain ⟨W, hWmem, hWnot⟩ := Finset.not_subset.mp hnot

  have hS₁ := AlgebraicCurve.Place.sum_ramificationIndexAlong_mul_inertiaDegAlong θ₁ hθ₁ hfin₁ hsep₁ (LF u)
  have hS₀ := AlgebraicCurve.Place.sum_ramificationIndexAlong_mul_inertiaDegAlong θ₀ hθ₀ hfin₀ hsep₀ u

  have himg : ∑ W' ∈ (Place.fiberAlong θ₀ hθ₀ u).image LR,
      (W'.ramificationIndexAlong θ₁ : ℤ) * (W'.inertiaDegAlong θ₁ hθ₁ : ℤ) = (finrankAlong K₀ θ₀ : ℤ) := by
    rw [Finset.sum_image (fun a _ b _ h => hLR.lift_injective h), ← hS₀]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [cfd_ramificationIndexAlong_lift hLF hLR θ₀ hθ₀ θ₁ hθ₁ hsq, cfd_inertiaDegAlong_eq_one,
      cfd_inertiaDegAlong_eq_one]

  have hlt : ∑ W' ∈ (Place.fiberAlong θ₀ hθ₀ u).image LR,
        (W'.ramificationIndexAlong θ₁ : ℤ) * (W'.inertiaDegAlong θ₁ hθ₁ : ℤ) <
      ∑ W' ∈ Place.fiberAlong θ₁ hθ₁ (LF u),
        (W'.ramificationIndexAlong θ₁ : ℤ) * (W'.inertiaDegAlong θ₁ hθ₁ : ℤ) := by
    refine Finset.sum_lt_sum_of_subset hsub hWmem hWnot ?_ ?_
    · rw [cfd_inertiaDegAlong_eq_one]
      have := AlgebraicCurve.Place.one_le_ramificationIndexAlong θ₁ hθ₁ W
      push_cast
      omega
    · intro j _ _
      positivity
  rw [himg, hS₁, hrk] at hlt
  exact lt_irrefl _ hlt

include hLF hLR hsq in
private theorem cfd_pullbackAlong_lift [IsAlgClosed K₀] [IsAlgClosed K₁]
    [IsCurveOver K₀ F₀] [IsCurveOver K₀ R₀] [IsCurveOver K₁ F₁] [IsCurveOver K₁ R₁]
    (hfin₀ : FiniteAlong K₀ θ₀) (hsep₀ : SeparableAlong K₀ θ₀)
    (hfin₁ : FiniteAlong K₁ θ₁) (hsep₁ : SeparableAlong K₁ θ₁)
    (hrk : finrankAlong K₁ θ₁ = finrankAlong K₀ θ₀) (D : Divisor K₀ F₀) :
    Divisor.pullbackAlong θ₁ hθ₁ (Finsupp.mapDomain LF D) =
      Finsupp.mapDomain LR (Divisor.pullbackAlong θ₀ hθ₀ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [Finsupp.mapDomain_add, map_add, hD, hE, map_add, Finsupp.mapDomain_add]
  | single u n =>
    rw [Finsupp.mapDomain_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
      cfd_fiberAlong_lift hLF hLR θ₀ hθ₀ θ₁ hθ₁ hsq hfin₀ hsep₀ hfin₁ hsep₁ hrk,
      Finset.sum_image (fun a _ b _ h => hLR.lift_injective h), Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finsupp.mapDomain_single, cfd_ramificationIndexAlong_lift hLF hLR θ₀ hθ₀ θ₁ hθ₁ hsq]

include hLF hLR hsq in
private theorem cfd_pushforwardAlong_lift [IsAlgClosed K₀] [IsAlgClosed K₁]
    [IsCurveOver K₀ F₀] [IsCurveOver K₀ R₀] [IsCurveOver K₁ F₁] [IsCurveOver K₁ R₁] (E : Divisor K₀ R₀) :
    Divisor.pushforwardAlong θ₁ hθ₁ (Finsupp.mapDomain LR E) =
      Finsupp.mapDomain LF (Divisor.pushforwardAlong θ₀ hθ₀ E) := by
  induction E using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [Finsupp.mapDomain_add, map_add, hD, hE, map_add, Finsupp.mapDomain_add]
  | single w m =>
    rw [Finsupp.mapDomain_single, Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      Finsupp.mapDomain_single, cfd_restrictAlong_lift hLF hLR θ₀ hθ₀ θ₁ hθ₁ hsq,
      cfd_inertiaDegAlong_eq_one, cfd_inertiaDegAlong_eq_one]

end Roof

private theorem cfd_conorm_equivariant
    (K₀ F₀ R₀ K₁ F₁ R₁ : Type*)
    [Field K₀] [Field F₀] [Field R₀] [Field K₁] [Field F₁] [Field R₁]
    [Algebra K₀ F₀] [Algebra K₀ R₀] [Algebra K₁ F₁] [Algebra K₁ R₁]
    [Algebra K₀ K₁] [Algebra F₀ F₁] [Algebra K₀ F₁] [IsScalarTower K₀ K₁ F₁] [IsScalarTower K₀ F₀ F₁]
    [Algebra R₀ R₁] [Algebra K₀ R₁] [IsScalarTower K₀ K₁ R₁] [IsScalarTower K₀ R₀ R₁]
    [IsAlgClosed K₀] [CharZero K₀] [IsAlgClosed K₁]
    [IsCurveOver K₀ F₀] [IsCurveOver K₀ R₀] [IsCurveOver K₁ F₁] [IsCurveOver K₁ R₁]
    (hfg₀ : ∃ t : F₀, Transcendental K₀ t ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({t} : Set F₀)) F₀)
    (hfg₁ : ∃ t : F₁, Transcendental K₁ t ∧
      FiniteDimensional (IntermediateField.adjoin K₁ ({t} : Set F₁)) F₁)
    (hfgR₀ : ∃ t : R₀, Transcendental K₀ t ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({t} : Set R₀)) R₀)
    (hfgR₁ : ∃ t : R₁, Transcendental K₁ t ∧
      FiniteDimensional (IntermediateField.adjoin K₁ ({t} : Set R₁)) R₁)
    (hgen : IntermediateField.adjoin K₁ (Set.range (algebraMap F₀ F₁)) = ⊤)
    (hgenR : IntermediateField.adjoin K₁ (Set.range (algebraMap R₀ R₁)) = ⊤)
    (φ₀ ψ₀ : F₀ →ₐ[K₀] R₀) (hφ₀ : φ₀.toRingHom.IsIntegral) (hψ₀ : ψ₀.toRingHom.IsIntegral)
    (hFI₀ : FundamentalIdentityAlong K₀ φ₀ hφ₀) (hfin₀ : FiniteAlong K₀ ψ₀)
    (hN₀ : NormFormulaAlong K₀ ψ₀ hfin₀)
    (φ₁ ψ₁ : F₁ →ₐ[K₁] R₁) (hφ₁ : φ₁.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (hFI₁ : FundamentalIdentityAlong K₁ φ₁ hφ₁) (hfin₁ : FiniteAlong K₁ ψ₁)
    (hN₁ : NormFormulaAlong K₁ ψ₁ hfin₁)
    (hφsq : ∀ f : F₀, φ₁ (algebraMap F₀ F₁ f) = algebraMap R₀ R₁ (φ₀ f))
    (hψsq : ∀ f : F₀, ψ₁ (algebraMap F₀ F₁ f) = algebraMap R₀ R₁ (ψ₀ f))
    (ι : Pic0 K₀ F₀ →+ Pic0 K₁ F₁)
    (hι : ∀ (D : Divisor.degZero (K := K₀) (F := F₀)) (D' : Divisor.degZero (K := K₁) (F := F₁)),
      (∀ (v' : Place K₁ F₁) (v : Place K₀ F₀),
        v'.toValuationSubring.comap (algebraMap F₀ F₁) = v.toValuationSubring →
          (D' : Divisor K₁ F₁) v' = (D : Divisor K₀ F₀) v) →
      (∀ v' : Place K₁ F₁,
        (∀ v : Place K₀ F₀, v'.toValuationSubring.comap (algebraMap F₀ F₁) ≠ v.toValuationSubring) →
          (D' : Divisor K₁ F₁) v' = 0) →
      ι (Pic0.mk D) = Pic0.mk D')
    (y : Pic0 K₀ F₀) :
    ι (Pic0.correspondence φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfin₀ hN₀ y) =
      Pic0.correspondence φ₁ ψ₁ hφ₁ hψ₁ hFI₁ hfin₁ hN₁ (ι y) := by
  haveI : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap K₀ K₁).injective
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap K₀ F₀).injective
  haveI : CharZero F₁ := charZero_of_injective_algebraMap (algebraMap K₁ F₁).injective

  obtain ⟨LF, hLF⟩ := cfd_exists_lift (K₀ := K₀) (F₀ := F₀) (K₁ := K₁) (F₁ := F₁) hfg₀ hfg₁ hgen
  obtain ⟨LR, hLR⟩ := cfd_exists_lift (K₀ := K₀) (F₀ := R₀) (K₁ := K₁) (F₁ := R₁) hfgR₀ hfgR₁ hgenR

  obtain ⟨hφfin₀, hφfin₁, hrk, -⟩ :=
    AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension K₀ F₀ hfg₀ R₀ hfgR₀ φ₀ hφ₀
      K₁ F₁ hfg₁ hgen R₁ hfgR₁ hgenR φ₁ hφsq hφ₁
  have hφsep₀ : SeparableAlong K₀ φ₀ := by
    unfold SeparableAlong
    letI := algebraAlong φ₀
    haveI : Module.Finite F₀ R₀ := hφfin₀
    exact Algebra.IsSeparable.of_integral F₀ R₀
  have hφsep₁ : SeparableAlong K₁ φ₁ := by
    unfold SeparableAlong
    letI := algebraAlong φ₁
    haveI : Module.Finite F₁ R₁ := hφfin₁
    exact Algebra.IsSeparable.of_integral F₁ R₁

  have hdiv : ∀ D : Divisor K₀ F₀,
      Divisor.correspondence φ₁ ψ₁ hφ₁ hψ₁ (Finsupp.mapDomain LF D) =
        Finsupp.mapDomain LF (Divisor.correspondence φ₀ ψ₀ hφ₀ hψ₀ D) := by
    intro D
    rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
      cfd_pullbackAlong_lift hLF hLR φ₀ hφ₀ φ₁ hφ₁ hφsq hφfin₀ hφsep₀ hφfin₁ hφsep₁ hrk,
      cfd_pushforwardAlong_lift hLF hLR ψ₀ hψ₀ ψ₁ hψ₁ hψsq]

  have hιmk : ∀ D : Divisor.degZero (K := K₀) (F := F₀),
      ι (Pic0.mk D) = Pic0.mk ⟨Finsupp.mapDomain LF (D : Divisor K₀ F₀), cfd_mapDomain_mem_degZero LF D.2⟩ :=
    fun D => hι D _ (fun v' v hv => hLF.mapDomain_apply_of_comap_eq _ v' v hv)
      (fun v' hv' => hLF.mapDomain_apply_eq_zero _ v' hv')
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  rw [Pic0.correspondence_mk, hιmk, hιmk, Pic0.correspondence_mk]
  congr 1
  apply Subtype.ext
  simp only [Pic0.coe_degZeroCorrespondence]
  exact (hdiv (D : Divisor K₀ F₀)).symm

private theorem cfd_exists_conorm
    (K₀ F₀ R₀ K₁ F₁ R₁ : Type*)
    [Field K₀] [Field F₀] [Field R₀] [Field K₁] [Field F₁] [Field R₁]
    [Algebra K₀ F₀] [Algebra K₀ R₀] [Algebra K₁ F₁] [Algebra K₁ R₁]
    [Algebra K₀ K₁] [Algebra F₀ F₁] [Algebra K₀ F₁] [IsScalarTower K₀ K₁ F₁] [IsScalarTower K₀ F₀ F₁]
    [Algebra R₀ R₁] [Algebra K₀ R₁] [IsScalarTower K₀ K₁ R₁] [IsScalarTower K₀ R₀ R₁]
    [IsAlgClosed K₀] [CharZero K₀] [IsAlgClosed K₁]
    [IsCurveOver K₀ F₀] [IsCurveOver K₀ R₀] [IsCurveOver K₁ F₁] [IsCurveOver K₁ R₁]
    (hfg₀ : ∃ t : F₀, Transcendental K₀ t ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({t} : Set F₀)) F₀)
    (hfg₁ : ∃ t : F₁, Transcendental K₁ t ∧
      FiniteDimensional (IntermediateField.adjoin K₁ ({t} : Set F₁)) F₁)
    (hfgR₀ : ∃ t : R₀, Transcendental K₀ t ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({t} : Set R₀)) R₀)
    (hfgR₁ : ∃ t : R₁, Transcendental K₁ t ∧
      FiniteDimensional (IntermediateField.adjoin K₁ ({t} : Set R₁)) R₁)
    (hgen : IntermediateField.adjoin K₁ (Set.range (algebraMap F₀ F₁)) = ⊤)
    (hgenR : IntermediateField.adjoin K₁ (Set.range (algebraMap R₀ R₁)) = ⊤)
    (φ₀ ψ₀ : F₀ →ₐ[K₀] R₀) (hφ₀ : φ₀.toRingHom.IsIntegral) (hψ₀ : ψ₀.toRingHom.IsIntegral)
    (hFI₀ : FundamentalIdentityAlong K₀ φ₀ hφ₀) (hfin₀ : FiniteAlong K₀ ψ₀)
    (hN₀ : NormFormulaAlong K₀ ψ₀ hfin₀)
    (φ₁ ψ₁ : F₁ →ₐ[K₁] R₁) (hφ₁ : φ₁.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (hFI₁ : FundamentalIdentityAlong K₁ φ₁ hφ₁) (hfin₁ : FiniteAlong K₁ ψ₁)
    (hN₁ : NormFormulaAlong K₁ ψ₁ hfin₁)
    (hφsq : ∀ f : F₀, φ₁ (algebraMap F₀ F₁ f) = algebraMap R₀ R₁ (φ₀ f))
    (hψsq : ∀ f : F₀, ψ₁ (algebraMap F₀ F₁ f) = algebraMap R₀ R₁ (ψ₀ f)) :
    ∃ ι : Pic0 K₀ F₀ →+ Pic0 K₁ F₁, Function.Injective ι ∧
      (∀ n : ℕ, n ≠ 0 → ∀ z : Pic0 K₁ F₁, (n : ℤ) • z = 0 → ∃ y, ι y = z) ∧
      ∀ y, ι (Pic0.correspondence φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfin₀ hN₀ y) =
        Pic0.correspondence φ₁ ψ₁ hφ₁ hψ₁ hFI₁ hfin₁ hN₁ (ι y) := by
  obtain ⟨ι, hinj, hι⟩ :=
    AlgebraicCurve.Pic0.exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
      K₀ F₀ K₁ F₁ hfg₀ hfg₁ hgen
  exact ⟨ι, hinj,
    fun n hn z hz => cfd_torsion_mem_range K₀ F₀ K₁ F₁ hfg₀ hfg₁ hgen ι hι n hn z hz,
    fun y => cfd_conorm_equivariant K₀ F₀ R₀ K₁ F₁ R₁ hfg₀ hfg₁ hfgR₀ hfgR₁ hgen hgenR φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfin₀ hN₀
      φ₁ ψ₁ hφ₁ hψ₁ hFI₁ hfin₁ hN₁ hφsq hψsq ι hι y⟩

section TateTransfer

variable {p : ℕ} [Fact p.Prime] {A B : Type} [AddCommGroup A] [AddCommGroup B]

private noncomputable def cfdTate (ι : A →+ B) : TateModule p A →ₗ[ℤ_[p]] TateModule p B where
  toFun x := ⟨fun n => ι ((x : ℕ → A) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero], by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show ι (((x + y : TateModule p A) : ℕ → A) n) = ι ((x : ℕ → A) n) + ι ((y : ℕ → A) n)
    rw [AddSubgroup.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show ι (((a • x : TateModule p A) : ℕ → A) n) = ((a • _ : TateModule p B) : ℕ → B) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

private theorem cfdTate_apply (ι : A →+ B) (x : TateModule p A) (n : ℕ) :
    ((cfdTate (p := p) ι x : TateModule p B) : ℕ → B) n = ι ((x : ℕ → A) n) := rfl

private theorem cfdTate_injective (ι : A →+ B) (hinj : Function.Injective ι) :
    Function.Injective (cfdTate (p := p) ι) := by
  intro x y hxy
  refine Subtype.ext (funext fun n => hinj ?_)
  have h := congrArg (fun z : TateModule p B => (z : ℕ → B) n) hxy
  simpa only [cfdTate_apply] using h

private theorem cfdTate_surjective (ι : A →+ B) (hinj : Function.Injective ι)
    (hsurj : ∀ n : ℕ, n ≠ 0 → ∀ z : B, (n : ℤ) • z = 0 → ∃ y, ι y = z) :
    Function.Surjective (cfdTate (p := p) ι) := by
  intro z
  have hex : ∀ n : ℕ, ∃ y : A, ι y = (z : ℕ → B) n := fun n =>
    hsurj (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero) _ (TateModule.torsion z n)
  choose y hy using hex
  refine ⟨⟨y, fun n => ⟨hinj ?_, hinj ?_⟩⟩, Subtype.ext (funext fun n => ?_)⟩
  · rw [map_zsmul, hy, TateModule.torsion, map_zero]
  · rw [map_zsmul, hy, hy, TateModule.compat]
  · exact hy n

private noncomputable def cfdTateEquiv (ι : A →+ B) (hinj : Function.Injective ι)
    (hsurj : ∀ n : ℕ, n ≠ 0 → ∀ z : B, (n : ℤ) • z = 0 → ∃ y, ι y = z) :
    TateModule p A ≃ₗ[ℤ_[p]] TateModule p B :=
  LinearEquiv.ofBijective (cfdTate ι) ⟨cfdTate_injective ι hinj, cfdTate_surjective ι hinj hsurj⟩

private theorem cfdTateEquiv_apply (ι : A →+ B) (hinj : Function.Injective ι)
    (hsurj : ∀ n : ℕ, n ≠ 0 → ∀ z : B, (n : ℤ) • z = 0 → ∃ y, ι y = z) (x : TateModule p A) :
    cfdTateEquiv (p := p) ι hinj hsurj x = cfdTate ι x := rfl

private theorem cfdTate_rep (ι : A →+ B) (f : Module.End ℤ A) (g : Module.End ℤ B)
    (hfg : ∀ y, ι (f y) = g (ι y)) (x : TateModule p A) :
    cfdTate (p := p) ι (TateModule.rep p A (Module.End ℤ A) f x) =
      TateModule.rep p B (Module.End ℤ B) g (cfdTate ι x) := by
  refine Subtype.ext (funext fun n => ?_)
  rw [cfdTate_apply, TateModule.rep_apply, TateModule.rep_apply, cfdTate_apply]
  exact hfg _

private theorem cfd_toMatrix_map_eq {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n R V) (e : V ≃ₗ[R] W) (f : V →ₗ[R] V) (g : W →ₗ[R] W)
    (hcomm : ∀ v, e (f v) = g (e v)) :
    LinearMap.toMatrix (b.map e) (b.map e) g = LinearMap.toMatrix b b f := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply, ← hcomm,
    Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

private theorem cfd_tate_transfer (ι : A →+ B) (hinj : Function.Injective ι)
    (hsurj : ∀ n : ℕ, n ≠ 0 → ∀ z : B, (n : ℤ) • z = 0 → ∃ y, ι y = z)
    (f : Module.End ℤ A) (g : Module.End ℤ B) (hfg : ∀ y, ι (f y) = g (ι y))
    {r : Type*} [Fintype r] [DecidableEq r] :
    (∀ c : Module.Basis r ℤ_[p] (TateModule p A),
      LinearMap.toMatrix (c.map (cfdTateEquiv ι hinj hsurj)) (c.map (cfdTateEquiv ι hinj hsurj))
          (TateModule.rep p B (Module.End ℤ B) g) =
        LinearMap.toMatrix c c (TateModule.rep p A (Module.End ℤ A) f)) ∧
    (∀ c : Module.Basis r ℤ_[p] (TateModule p B),
      LinearMap.toMatrix (c.map (cfdTateEquiv ι hinj hsurj).symm) (c.map (cfdTateEquiv ι hinj hsurj).symm)
          (TateModule.rep p A (Module.End ℤ A) f) =
        LinearMap.toMatrix c c (TateModule.rep p B (Module.End ℤ B) g)) := by
  have hcomm : ∀ x, cfdTateEquiv (p := p) ι hinj hsurj (TateModule.rep p A (Module.End ℤ A) f x) =
      TateModule.rep p B (Module.End ℤ B) g (cfdTateEquiv ι hinj hsurj x) := fun x => by
    rw [cfdTateEquiv_apply, cfdTateEquiv_apply, cfdTate_rep ι f g hfg]
  refine ⟨fun c => cfd_toMatrix_map_eq c _ _ _ hcomm, fun c => cfd_toMatrix_map_eq c _ _ _ fun y => ?_⟩
  rw [LinearEquiv.symm_apply_eq, hcomm, LinearEquiv.apply_symm_apply]

end TateTransfer

private theorem cfd_matrix_transport
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    {F' : Type} [Field F'] [Algebra K F'] [IsCurveOver K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ) (hFI : FundamentalIdentityAlong K φ hφ)
    (hNψ : NormFormulaAlong K ψ hψfin)
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (K₀ : Type) [Field K₀] [Algebra K₀ K] [Algebra K₀ ℂ] [IsAlgClosed K₀] [CharZero K₀]
    (F₀ : Type) (R₀ : Type) [Field F₀] [Field R₀] [Algebra K₀ F₀] [Algebra F₀ F] [Algebra K₀ F]
    [IsScalarTower K₀ K F] [IsScalarTower K₀ F₀ F] [IsCurveOver K₀ F₀] [Algebra K₀ R₀]
    [Algebra R₀ F'] [Algebra K₀ F'] [IsScalarTower K₀ K F'] [IsScalarTower K₀ R₀ F']
    [IsCurveOver K₀ R₀] (φ₀ ψ₀ : F₀ →ₐ[K₀] R₀)
    (hφ₀ : φ₀.toRingHom.IsIntegral) (hψ₀ : ψ₀.toRingHom.IsIntegral)
    (hFI₀ : FundamentalIdentityAlong K₀ φ₀ hφ₀) (hfin₀ : FiniteAlong K₀ ψ₀) (hN₀ : NormFormulaAlong K₀ ψ₀ hfin₀)
    (hfg₀ : ∃ x : F₀, Transcendental K₀ x ∧ FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
    (hgenK : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hfgR₀ : ∃ x : R₀, Transcendental K₀ x ∧ FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set R₀)) R₀)
    (hgenRK : IntermediateField.adjoin K (Set.range (algebraMap R₀ F')) = ⊤)
    (hφsqK : ∀ f : F₀, φ (algebraMap F₀ F f) = algebraMap R₀ F' (φ₀ f))
    (hψsqK : ∀ f : F₀, ψ (algebraMap F₀ F f) = algebraMap R₀ F' (ψ₀ f))
    (FC : Type) (RC : Type) [Field FC] [Field RC] [Algebra ℂ FC] [Algebra F₀ FC] [Algebra K₀ FC]
    [IsScalarTower K₀ ℂ FC] [IsScalarTower K₀ F₀ FC] [IsCurveOver ℂ FC] [Algebra ℂ RC] [Algebra R₀ RC]
    [Algebra K₀ RC] [IsScalarTower K₀ ℂ RC] [IsScalarTower K₀ R₀ RC] [IsCurveOver ℂ RC]
    (φC ψC : FC →ₐ[ℂ] RC) (hφC : φC.toRingHom.IsIntegral) (hψC : ψC.toRingHom.IsIntegral)
    (hFIC : FundamentalIdentityAlong ℂ φC hφC) (hfinC : FiniteAlong ℂ ψC) (hNC : NormFormulaAlong ℂ ψC hfinC)
    (hfgC : ∃ x : FC, Transcendental ℂ x ∧ FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set FC)) FC)
    (hgenC : IntermediateField.adjoin ℂ (Set.range (algebraMap F₀ FC)) = ⊤)
    (hfgRC : ∃ x : RC, Transcendental ℂ x ∧ FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set RC)) RC)
    (hgenRC : IntermediateField.adjoin ℂ (Set.range (algebraMap R₀ RC)) = ⊤)
    (hφsqC : ∀ f : F₀, φC (algebraMap F₀ FC f) = algebraMap R₀ RC (φ₀ f))
    (hψsqC : ∀ f : F₀, ψC (algebraMap F₀ FC f) = algebraMap R₀ RC (ψ₀ f))
    (hC : ∃ M : Matrix (Fin (2 * genusFF ℂ FC)) (Fin (2 * genusFF ℂ FC)) ℤ,
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ b : Module.Basis (Fin (2 * genusFF ℂ FC)) ℤ_[p] (TateModule p (Pic0 ℂ FC)),
          LinearMap.toMatrix b b (TateModule.rep p (Pic0 ℂ FC) (Module.End ℤ (Pic0 ℂ FC))
            (Pic0.correspondence φC ψC hφC hψC hFIC hfinC hNC).toIntLinearMap) =
            M.map (Int.castRingHom ℤ_[p])) :
    ∃ M : Matrix (Fin (2 * genusFF K F)) (Fin (2 * genusFF K F)) ℤ,
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ b : Module.Basis (Fin (2 * genusFF K F)) ℤ_[p] (TateModule p (Pic0 K F)),
          LinearMap.toMatrix b b (TateModule.rep p (Pic0 K F) (Module.End ℤ (Pic0 K F))
            (Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ).toIntLinearMap) =
            M.map (Int.castRingHom ℤ_[p]) := by

  obtain ⟨ιK, hιKinj, hιKtor, hιKeq⟩ := cfd_exists_conorm K₀ F₀ R₀ K F F' hfg₀ hfg hfgR₀ hfg' hgenK hgenRK
    φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfin₀ hN₀ φ ψ hφ hψ hFI hψfin hNψ hφsqK hψsqK
  obtain ⟨ιC, hιCinj, hιCtor, hιCeq⟩ := cfd_exists_conorm K₀ F₀ R₀ ℂ FC RC hfg₀ hfgC hfgR₀ hfgRC hgenC hgenRC
    φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfin₀ hN₀ φC ψC hφC hψC hFIC hfinC hNC hφsqC hψsqC

  have hgK : genusFF K F = genusFF K₀ F₀ :=
    AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed K₀ F₀ K F hfg₀ hfg hgenK
  have hgC : genusFF ℂ FC = genusFF K₀ F₀ :=
    AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed K₀ F₀ ℂ FC hfg₀ hfgC hgenC
  rw [hgC] at hC
  rw [hgK]
  obtain ⟨M, hM⟩ := hC
  refine ⟨M, fun p _ => ?_⟩
  obtain ⟨bC, hbC⟩ := hM p

  have hfg₀eq : ∀ y, ιC ((Pic0.correspondence φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfin₀ hN₀).toIntLinearMap y) =
      (Pic0.correspondence φC ψC hφC hψC hFIC hfinC hNC).toIntLinearMap (ιC y) := fun y => hιCeq y
  have hfgKeq : ∀ y, ιK ((Pic0.correspondence φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfin₀ hN₀).toIntLinearMap y) =
      (Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ).toIntLinearMap (ιK y) := fun y => hιKeq y
  obtain ⟨-, hdown⟩ := cfd_tate_transfer (p := p) ιC hιCinj hιCtor _ _ hfg₀eq (r := Fin (2 * genusFF K₀ F₀))
  obtain ⟨hup, -⟩ := cfd_tate_transfer (p := p) ιK hιKinj hιKtor _ _ hfgKeq (r := Fin (2 * genusFF K₀ F₀))
  refine ⟨(bC.map (cfdTateEquiv ιC hιCinj hιCtor).symm).map (cfdTateEquiv ιK hιKinj hιKtor), ?_⟩
  rw [hup, hdown, hbC]

theorem solution
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    {F' : Type} [Field F'] [Algebra K F'] [IsCurveOver K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ) (hFI : FundamentalIdentityAlong K φ hφ)
    (hNψ : NormFormulaAlong K ψ hψfin) :
    ∃ M : Matrix (Fin (2 * genusFF K F)) (Fin (2 * genusFF K F)) ℤ,
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ b : Module.Basis (Fin (2 * genusFF K F)) ℤ_[p] (TateModule p (Pic0 K F)),
          LinearMap.toMatrix b b (TateModule.rep p (Pic0 K F) (Module.End ℤ (Pic0 K F))
            (Pic0.correspondence φ ψ hφ hψ hFI hψfin hNψ).toIntLinearMap) =
            M.map (Int.castRingHom ℤ_[p]) := by

  haveI : Algebra.EssFiniteType K F' := by
    letI : Algebra F F' := algebraAlong ψ
    haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (ψ.commutes k).symm
    haveI : Module.Finite F F' := hψfin
    exact Algebra.EssFiniteType.comp K F F'

  have hfg : ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := cfd_hfg
  have hfg' : ∃ t : F', Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F')) F' := cfd_hfg

  obtain ⟨K₀, F₀, R₀, iFK₀, iFF₀, iFR₀, iAK₀K, iAK₀C, iACl, iCnt, iAK₀F₀, iAF₀F, iAK₀F,
      iTKF, iTF₀F, iCrvF₀, iAK₀R, iARF', iAK₀F', iTKF', iTRF', iCrvR, φ₀, ψ₀, hfg₀, hgenK,
      hfgR₀, hgenRK, hφsqK, hψsqK, hφ₀fin, hψ₀fin⟩ :=
    AlgebraicCurve.exists_constantFieldDescent_correspondence K F hfg (fun _ : Unit => F')
      (fun _ => φ) (fun _ => ψ) (fun _ => hφ) (fun _ => hψfin)
  letI : Algebra K₀ F' := iAK₀F' ()
  letI : Algebra (R₀ ()) F' := iARF' ()
  haveI : IsScalarTower K₀ K F' := iTKF' ()
  haveI : IsScalarTower K₀ (R₀ ()) F' := iTRF' ()
  haveI : CharZero K₀ := (algebraMap K₀ K).charZero
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap K₀ F₀).injective

  have hφ₀ : (φ₀ ()).toRingHom.IsIntegral := cfd_isIntegral_of_finiteAlong _ (hφ₀fin ())
  have hψ₀ : (ψ₀ ()).toRingHom.IsIntegral := cfd_isIntegral_of_finiteAlong _ (hψ₀fin ())
  have hFI₀ : FundamentalIdentityAlong K₀ (φ₀ ()) hφ₀ :=
    AlgebraicCurve.fundamentalIdentityAlong (φ₀ ()) hφ₀ (hφ₀fin ())
      (AlgebraicCurve.separableAlong_of_charZero (φ₀ ()) hφ₀)
  have hN₀ : NormFormulaAlong K₀ (ψ₀ ()) (hψ₀fin ()) :=
    AlgebraicCurve.normFormulaAlong (ψ₀ ()) (hψ₀fin ()) (AlgebraicCurve.separableAlong_of_charZero (ψ₀ ()) hψ₀)

  haveI : HasCanonicalDivisor (K := K₀) (F := F₀) := by
    haveI := cfd_essFiniteType hfg₀
    exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  obtain ⟨FC, _, _, _, _, _, _, _, _, hfgC, hgenC⟩ :=
    AlgebraicCurve.exists_constantFieldExtension K₀ F₀ ℂ hfg₀
  obtain ⟨RC, _, _, _, _, _, _, _, φC, ψC, hφC, hψC, hFIC, hfinC, hNC, hfgRC, hgenRC, hφsqC, hψsqC, -, -, -⟩ :=
    AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension K₀ F₀ hfg₀ (R₀ ())
      (φ₀ ()) (ψ₀ ()) hφ₀ hψ₀ hFI₀ (hψ₀fin ()) hN₀ ℂ FC hfgC hgenC
  letI : Algebra K₀ (R₀ ()) := iAK₀R ()
  haveI : IsCurveOver K₀ (R₀ ()) := iCrvR ()

  haveI : Algebra.EssFiniteType ℂ FC := cfd_essFiniteType hfgC
  have hC := mtx_complex φC ψC hφC hψC hfinC hFIC hNC

  exact cfd_matrix_transport φ ψ hφ hψ hψfin hFI hNψ hfg hfg' K₀ F₀ (R₀ ()) (φ₀ ()) (ψ₀ ()) hφ₀ hψ₀ hFI₀
    (hψ₀fin ()) hN₀ hfg₀ hgenK (hfgR₀ ()) (hgenRK ()) (hφsqK ()) (hψsqK ()) FC RC φC ψC hφC hψC hFIC hfinC hNC
    hfgC hgenC hfgRC hgenRC hφsqC hψsqC hC

end S_AlgebraicCurve_exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
end P2MW
export P2MW.S_AlgebraicCurve_exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map (solution)
