-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d0c6e3bd-3cd7-5b5b-9098-77408598336a

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

open AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] {q : Polynomial K} (hq : q ≠ 0) : (placeInfty K).ord (algebraMap (Polynomial K) (RatFunc K) q) = -(q.natDegree : ℤ) := by
  rw [AlgebraicCurve.RationalFunctionField.ord_placeInfty (RatFunc.algebraMap_ne_zero hq), RatFunc.intDegree_polynomial]

end S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap (solution)
