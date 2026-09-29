-- Prove2me | solution 1 for AlgebraicCurve.Place.ordDiff_zero_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/83c6e7ce-4800-55e0-812e-8472c32effd0

import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

noncomputable section

open AlgebraicCurve

private theorem ordDiff_smul_D_uniformizer {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) (g : F) :
    v.ordDiff (g • KaehlerDifferential.D K F v.uniformizer_alt) = v.ord g := by
  have h1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  haveI := Place.isSeparable_adjoin_of_ord_eq_one x v h1
  have hD : KaehlerDifferential.D K F v.uniformizer_alt ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K v.uniformizer_alt
      (v.transcendental_of_ord_ne_zero (h1 ▸ one_ne_zero))
  rw [Place.ordDiff_def, smul_left_injective F hD (Place.diffCoeff_smul_D ⟨g, rfl⟩)]

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by
  simpa using ordDiff_smul_D_uniformizer x v 0

end

end S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField
end P2MW
export P2MW.S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField (solution)
