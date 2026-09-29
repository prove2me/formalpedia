-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d6da2bbe-9380-5d22-b236-3e44846a3835

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_isPrincipal
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] {D : Divisor K (RatFunc K)} (hD : D.IsPrincipal) : Divisor.degree D = 0 := by
  obtain ⟨f, -, hDf⟩ := hD
  exact AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord D hDf

end S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_isPrincipal
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_isPrincipal (solution)
