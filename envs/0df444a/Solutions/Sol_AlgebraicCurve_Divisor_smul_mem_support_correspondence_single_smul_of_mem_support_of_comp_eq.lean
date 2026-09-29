-- Prove2me | solution 1 for AlgebraicCurve.Divisor.smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/57c1450e-e66d-5e62-9add-0e2538d40566

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
import Theorems.Thm_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ)
    (W : F' ≃ₐ[K] F') (τ₁ τ₂ : F ≃ₐ[K] F)
    (hWφ : ∀ x : F, W (φ x) = ψ (τ₁ x)) (hWψ : ∀ x : F, W (ψ x) = φ (τ₂ x))
    (P Q : AlgebraicCurve.Place K F)
    (hQ : Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support) :
    SemilinearAut.ofAlgAut τ₁ • P ∈
      (Divisor.correspondence φ ψ hφ hψ (Finsupp.single (SemilinearAut.ofAlgAut τ₂ • Q) 1)).support := by

  obtain ⟨-, hsymm⟩ :=
    AlgebraicCurve.Divisor.mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
      φ ψ hφ hψ hfφ hfψ P Q
  have hP : P ∈ (Divisor.correspondence ψ φ hψ hφ (Finsupp.single Q 1)).support := hsymm.mp hQ

  have hx := AlgebraicCurve.Divisor.ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
    ψ φ hψ hφ W τ₁ τ₂ (AlgHom.ext fun x => hWφ x) (AlgHom.ext fun x => hWψ x) (Finsupp.single Q 1)
  rw [smul_single] at hx
  rw [← hx, Finsupp.mem_support_iff, divisor_smul_apply, inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hP

end S_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq (solution)
