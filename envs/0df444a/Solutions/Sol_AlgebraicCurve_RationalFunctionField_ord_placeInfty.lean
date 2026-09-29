-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.ord_placeInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/74ae96fc-9bfe-59aa-954f-25e3933b067d

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] {f : RatFunc K} (hf : f ≠ 0) : (placeInfty K).ord f = -f.intDegree :=
  AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum (placeInfty K)
    (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K) hf

end S_AlgebraicCurve_RationalFunctionField_ord_placeInfty
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty (solution)
