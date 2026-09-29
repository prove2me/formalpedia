-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1a0a4486-f528-5d32-9478-0270db9fe56b

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_adicValuation_valuationSubring
import Theorems.Thm_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete
import Theorems.Thm_AlgebraicCurve_Place_adicValuation_isTrivialOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by
  haveI := v.adicValuation_isRankOneDiscrete
  haveI := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact absurd (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))) (hv w)

end S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum (solution)
