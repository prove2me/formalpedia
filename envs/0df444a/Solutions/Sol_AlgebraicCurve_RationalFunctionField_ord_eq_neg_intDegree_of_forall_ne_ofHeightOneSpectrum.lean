-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/230abd3e-62a3-58f3-a54f-d8134c83ba01

import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) {f : RatFunc K} (hf : f ≠ 0) : v.ord f = -f.intDegree := by
  classical
  have hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1 : ℤ) := by
    rw [map_inv₀, RatFunc.inftyValuation.X]
    exact (exp_neg (1 : ℤ)).symm
  rw [v.ord_eq_neg_log_of_valuationSubring_eq (RatFunc.inftyValuation K)
      (AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
        v hv).symm hπ hf,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]

end S_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum (solution)
