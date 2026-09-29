-- Prove2me | solution 1 for AlgebraicCurve.Place.ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8782ab03-f7bc-5383-a6e3-895e52a6c0f4

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [AlgebraicCurve.HasPrincipalDivisors k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong k φ) (hsep : AlgebraicCurve.SeparableAlong k φ)
    (n : ℕ) (hdeg : AlgebraicCurve.finrankAlong k φ = n)
    (c : F') (u : F) (hu : φ u = c ^ n)
    (P : AlgebraicCurve.Place k F')
    (hcop : IsCoprime ((P.restrictAlong φ hφ).ord u) (n : ℤ)) :
    P.ramificationIndexAlong φ = n := by
  classical

  letI alg : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.IsIntegral F F' := ⟨hφ⟩
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  have hdeg' : Module.finrank F F' = n := hdeg
  show P.ramificationIndex F = n
  set v : Place k F := P.restrict F with hvdef
  have hv : P.restrictAlong φ hφ = v := rfl
  rw [hv] at hcop
  set e : ℕ := P.ramificationIndex F with hedef
  have hepos : 0 < e := P.ramificationIndex_pos (F := F)

  have hord : P.ord (algebraMap F F' u) = e * v.ord u := P.ord_restrict u
  have hord' : P.ord (algebraMap F F' u) = n * P.ord c := by
    rw [show algebraMap F F' u = c ^ n from hu, ← zpow_natCast, P.ord_zpow]
  have hdvdZ : (n : ℤ) ∣ (e : ℤ) := by
    apply hcop.symm.dvd_of_dvd_mul_right
    rw [← hord, hord']
    exact dvd_mul_right _ _
  have hdvd : n ∣ e := Int.natCast_dvd_natCast.mp hdvdZ

  have hsum := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg (K := k) (F := F) (F' := F') v
  have hmem : P ∈ v.fiber F' := P.restrict_mem_fiber (F := F)
  have hfpos : 0 < P.inertiaDeg F := AlgebraicCurve.Place.inertiaDeg_pos (K := k) (F := F) P
  have hle : (e : ℤ) * (P.inertiaDeg F : ℤ) ≤ (Module.finrank F F' : ℤ) := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun w : Place k F' => (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ))
      (fun w _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) hmem
  have hlen : e ≤ n := by
    have h1 : (e : ℤ) ≤ (e : ℤ) * (P.inertiaDeg F : ℤ) := by
      have : (1 : ℤ) ≤ (P.inertiaDeg F : ℤ) := by exact_mod_cast hfpos
      nlinarith
    have h2 : (e : ℤ) ≤ (n : ℤ) := by rw [← hdeg']; exact h1.trans hle
    exact_mod_cast h2

  obtain ⟨m, hm⟩ := hdvd
  have hn0 : 0 < n := by
    rw [← hdeg']; exact Module.finrank_pos
  have hm1 : m = 1 := by
    have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hm; omega)
    have : n * m ≤ n * 1 := by rw [mul_one, ← hm]; exact hlen
    have := Nat.le_of_mul_le_mul_left this hn0
    omega
  rw [hm, hm1, mul_one]

end S_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
end P2MW
export P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord (solution)
