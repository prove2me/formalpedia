-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b7b39db5-4b47-5f92-aa17-01d45c4af7a5

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] {f : RatFunc K} (D : Divisor K (RatFunc K)) (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) : Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · have hden : f.denom ≠ 0 := f.denom_ne_zero
    have hdenF : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden

    set Dden : Divisor K (RatFunc K) :=
      Finsupp.ofSupportFinite
        (fun v : Place K (RatFunc K) => v.ord (algebraMap K[X] (RatFunc K) f.denom))
        (AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero hdenF) with hDden_def
    have hDden : ∀ v : Place K (RatFunc K),
        Dden v = v.ord (algebraMap K[X] (RatFunc K) f.denom) := fun v => rfl
    have hsplit : ∀ v : Place K (RatFunc K),
        (D + Dden) v = v.ord (algebraMap K[X] (RatFunc K) f.num) := by
      intro v
      rw [Finsupp.add_apply, hD v, hDden v]
      have hmul : f * algebraMap K[X] (RatFunc K) f.denom
          = algebraMap K[X] (RatFunc K) f.num :=
        ((div_eq_iff hdenF).mp f.num_div_denom).symm
      have h2 := v.ord_mul hf hdenF
      rw [hmul] at h2
      exact h2.symm
    have h1 := AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
      f.num (D + Dden) hsplit
    have h2 := AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
      f.denom Dden hDden
    rw [map_add, h2, add_zero] at h1
    exact h1

end S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord (solution)
