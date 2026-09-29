-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cf4ddbf8-4379-5686-aa89-08922551151c

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  ⟨fun f hf =>
    ⟨Finsupp.ofSupportFinite (fun v : Place K (RatFunc K) => v.ord f)
        (AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero hf),
      fun _ => rfl,
      AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord _ fun _ => rfl⟩⟩

end S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors (solution)
