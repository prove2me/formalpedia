-- Prove2me | solution 1 for Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c9594c01-6d14-587b-909a-e6477a5f1436

import Mathlib
import Theorems.Thm_Algebra_norm_algebraMap_sub_eq_minpoly_eval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open Polynomial

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) (c : K) :
    Algebra.norm K (algebraMap K L c - x)
      = ((minpoly K x).eval c) ^ (Module.finrank K L / (minpoly K x).natDegree) := by
  have hx : IsIntegral K x := .of_finite K x
  have hmin : minpoly K (IntermediateField.AdjoinSimple.gen K x) = minpoly K x :=
    IntermediateField.minpoly_gen K x
  have hfinE : Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) = (minpoly K x).natDegree :=
    IntermediateField.adjoin.finrank hx
  have hdeg : (minpoly K (IntermediateField.AdjoinSimple.gen K x)).natDegree
      = Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) := by
    rw [hmin, hfinE]
  have h1 : Algebra.norm K (algebraMap K (IntermediateField.adjoin K ({x} : Set L)) c
      - IntermediateField.AdjoinSimple.gen K x) = (minpoly K x).eval c := by
    rw [Algebra.norm_algebraMap_sub_eq_minpoly_eval _ hdeg c, hmin]
  have h2 : algebraMap (IntermediateField.adjoin K ({x} : Set L)) L
      (algebraMap K (IntermediateField.adjoin K ({x} : Set L)) c
        - IntermediateField.AdjoinSimple.gen K x) = algebraMap K L c - x := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hn : Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L
      = Module.finrank K L / (minpoly K x).natDegree := by
    have hmul := Module.finrank_mul_finrank K (IntermediateField.adjoin K ({x} : Set L)) L
    rw [hfinE] at hmul
    rw [← hmul, Nat.mul_div_cancel_left _ (minpoly.natDegree_pos hx)]
  rw [← h2, ← Algebra.norm_norm (S := IntermediateField.adjoin K ({x} : Set L)),
    Algebra.norm_algebraMap, map_pow, h1, hn]

#print axioms solution

end S_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
end P2MW
export P2MW.S_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow (solution)
