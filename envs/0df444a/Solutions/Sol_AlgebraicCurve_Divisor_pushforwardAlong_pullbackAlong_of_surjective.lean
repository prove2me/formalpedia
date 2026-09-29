-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/425fd0a8-161d-5a22-be07-ca56df895e60

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_AlgebraicCurve_finiteAlong_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective.AlgebraicCurve"

section Helpers

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem separableAlong_of_surjective_aux (φ : F →ₐ[K] F') (hs : Function.Surjective φ) :
    SeparableAlong K φ := by
  letI := algebraAlong φ
  exact ⟨fun x => by
    obtain ⟨a, rfl⟩ := hs x
    exact isSeparable_algebraMap (K := F') a⟩

private theorem finrankAlong_eq_one_of_surjective_aux (φ : F →ₐ[K] F') (hs : Function.Surjective φ) :
    finrankAlong K φ = 1 := by
  letI := algebraAlong φ
  show Module.finrank F F' = 1
  have e : F ≃ₗ[F] F' :=
    LinearEquiv.ofBijective (Algebra.linearMap F F') ⟨(algebraMap F F').injective, hs⟩
  rw [← e.finrank_eq, Module.finrank_self]

end Helpers

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "algebraAlong finrankAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.pushforwardAlong_single Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single SeparableAlong Place Divisor HasPrincipalDivisors Place.sum_ramificationIndexAlong_mul_inertiaDegAlong finiteAlong_of_surjective" namespace Divisor p2m_export "AlgebraicCurve.Divisor" "pullbackAlong pushforwardAlong pushforwardAlong_single pullbackAlong_single pushforward pullback degree" end AlgebraicCurve.Divisor
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in
private theorem AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hs : Function.Surjective φ) (D : AlgebraicCurve.Divisor K F) : AlgebraicCurve.Divisor.pushforwardAlong φ hφ (AlgebraicCurve.Divisor.pullbackAlong φ hφ D) = D := by
  have hsum := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ (finiteAlong_of_surjective φ hs)
    (separableAlong_of_surjective_aux φ hs)
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add D₁ D₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single v n =>
    rw [Divisor.pullbackAlong_single, map_sum]
    have hv := hsum v
    rw [finrankAlong_eq_one_of_surjective_aux φ hs, Nat.cast_one] at hv
    calc ∑ W ∈ Place.fiberAlong φ hφ v,
          Divisor.pushforwardAlong φ hφ (Finsupp.single W (n * (W.ramificationIndexAlong φ : ℤ)))
        = ∑ W ∈ Place.fiberAlong φ hφ v,
            Finsupp.single v (n * ((W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong φ hφ : ℤ))) := by
          refine Finset.sum_congr rfl fun W hW => ?_
          rw [Divisor.pushforwardAlong_single, Place.mem_fiberAlong.mp hW, mul_assoc]
      _ = Finsupp.single v n := by
          rw [← Finsupp.single_finsetSum, ← Finset.mul_sum, hv, mul_one]

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hs : Function.Surjective φ) (D : AlgebraicCurve.Divisor K F) : AlgebraicCurve.Divisor.pushforwardAlong φ hφ (AlgebraicCurve.Divisor.pullbackAlong φ hφ D) = D :=
  AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective φ hφ hs D

#print axioms solution

end S_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective (solution)
