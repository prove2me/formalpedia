-- Prove2me | solution 1 for AlgebraicCurve.Place.derivation_apply_eq_diffCoeff_D_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bc375bc9-a942-543b-abe6-26e3eb37a3e7

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_derivation_apply_eq_diffCoeff_D_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve KaehlerDifferential

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (δ : Derivation K F F) (f : F) :
    δ f = Place.diffCoeff t (KaehlerDifferential.D K F f) * δ t :=
  calc δ f = δ.liftKaehlerDifferential (KaehlerDifferential.D K F f) :=
        (Derivation.liftKaehlerDifferential_comp_D δ f).symm
    _ = δ.liftKaehlerDifferential
          (Place.diffCoeff t (KaehlerDifferential.D K F f) • KaehlerDifferential.D K F t) := by
        rw [Place.diffCoeff_smul_D_of_ord_eq_one x v ht]
    _ = Place.diffCoeff t (KaehlerDifferential.D K F f) * δ t := by
        rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul]

end S_AlgebraicCurve_Place_derivation_apply_eq_diffCoeff_D_mul
end P2MW
export P2MW.S_AlgebraicCurve_Place_derivation_apply_eq_diffCoeff_D_mul (solution)
