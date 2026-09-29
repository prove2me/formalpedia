-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/995ea5a4-9c0b-5ea5-987c-52b9251cf2de

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_of_decomposition
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

namespace Ws45
namespace PullPushGal

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem isIntegral_id : (AlgHom.id K F').toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ Function.surjective_id

theorem isIntegral_algEquiv (σ : F' ≃ₐ[K] F') : ((σ : F' →ₐ[K] F') : F' →ₐ[K] F').toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ σ.surjective

theorem finiteAlong_algEquiv (σ : F' ≃ₐ[K] F') : FiniteAlong K (σ : F' →ₐ[K] F') :=
  RingHom.Finite.of_surjective ((σ : F' →ₐ[K] F') : F' →ₐ[K] F').toRingHom σ.surjective

theorem finiteAlong_id : FiniteAlong K (AlgHom.id K F') :=
  RingHom.Finite.of_surjective (AlgHom.id K F').toRingHom Function.surjective_id

theorem finrankAlong_algEquiv (σ : F' ≃ₐ[K] F') : finrankAlong K (σ : F' →ₐ[K] F') = 1 := by
  have h := AlgebraicCurve.finrankAlong_comp (σ : F' →ₐ[K] F') (σ.symm : F' →ₐ[K] F')
  rw [show ((σ.symm : F' →ₐ[K] F')).comp (σ : F' →ₐ[K] F') = AlgHom.id K F' from AlgEquiv.symm_comp σ,
    AlgebraicCurve.finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

theorem restrictAlong_id (h : (AlgHom.id K F').toRingHom.IsIntegral) (w : Place K F') :
    w.restrictAlong (AlgHom.id K F') h = w := by
  apply Place.ext
  ext x
  exact Iff.rfl

theorem inertiaDegAlong_id (h : (AlgHom.id K F').toRingHom.IsIntegral) (w : Place K F') :
    Place.inertiaDegAlong (AlgHom.id K F') h w = 1 := by
  letI := AlgebraicCurve.algebraAlong (AlgHom.id K F')
  haveI := AlgebraicCurve.isScalarTower_along (AlgHom.id K F')
  haveI : Algebra.IsIntegral F' F' := AlgebraicCurve.isIntegral_along _ h
  show Module.finrank (w.restrict F').ResidueField w.ResidueField = 1
  have hsurj : Function.Surjective (algebraMap (w.restrict F').ResidueField w.ResidueField) := by
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    refine ⟨IsLocalRing.residue _ ⟨(a : F'), a.2⟩, ?_⟩
    rw [Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue]
    rfl
  have e := LinearEquiv.ofBijective (Algebra.linearMap (w.restrict F').ResidueField w.ResidueField)
    ⟨(algebraMap (w.restrict F').ResidueField w.ResidueField).injective, hsurj⟩
  rw [← e.finrank_eq, Module.finrank_self]

theorem pushforwardAlong_id [HasPrincipalDivisors K F'] (h : (AlgHom.id K F').toRingHom.IsIntegral)
    (D : Divisor K F') :
    Divisor.pushforwardAlong (AlgHom.id K F') h D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
    rw [map_add, ih, Divisor.pushforwardAlong_single, restrictAlong_id, inertiaDegAlong_id,
      Nat.cast_one, mul_one]

end Ws45.PullPushGal

open Ws45.PullPushGal in
theorem solution
    {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [CharZero K]
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong K φ)
    (n : ℕ) (hn : AlgebraicCurve.finrankAlong K φ = n)
    (σ : Fin n → (F' ≃ₐ[K] F')) (hσ : ∀ i, ((σ i : F' ≃ₐ[K] F') : F' →ₐ[K] F').comp φ = φ)
    (hinj : Function.Injective σ)
    (D : AlgebraicCurve.Divisor K F') :
    AlgebraicCurve.Divisor.pullbackAlong φ hφ (AlgebraicCurve.Divisor.pushforwardAlong φ hφ D) =
      ∑ i, AlgebraicCurve.SemilinearAut.ofAlgAut (σ i) • D := by
  classical

  have hσφ : ∀ (i : Fin n) (x : F), σ i (φ x) = φ x := fun i x => by
    have := congrArg (fun f : F →ₐ[K] F' => f x) (hσ i); simpa using this
  have key := AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_of_decomposition
    (K := K) (F := F) (F₁ := F') (F₂ := F') φ φ hφ hφ hfin hfin n (fun _ => F')
    (fun _ => AlgHom.id K F') (fun i => (σ i : F' →ₐ[K] F'))
    (fun i => by rw [AlgHom.id_comp, hσ i])
    (fun _ => isIntegral_id) (fun i => isIntegral_algEquiv (σ i))
    (fun _ => finiteAlong_id) (fun i => finiteAlong_algEquiv (σ i))
    (fun i => eq_top_iff.2 fun x _ => IntermediateField.subset_adjoin _ _ (Or.inl ⟨x, rfl⟩))
    (by rw [hn, Finset.sum_congr rfl fun i _ => finrankAlong_algEquiv (σ i)]; simp)
    (by
      intro i j hij
      have hne : σ i ≠ σ j := fun h => hij (hinj h)
      obtain ⟨b, hb⟩ : ∃ b : F', σ i b ≠ σ j b := by
        by_contra h
        push Not at h
        exact hne (AlgEquiv.ext h)
      refine ⟨σ i b ⊗ₜ[K] 1 - 1 ⊗ₜ[K] b, ?_, ?_⟩
      · simp [Algebra.TensorProduct.productMap_apply_tmul]
      · simp [Algebra.TensorProduct.productMap_apply_tmul, sub_eq_zero, hb])
    D
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pushforwardAlong_id, AlgebraicCurve.Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul]

end S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq (solution)
