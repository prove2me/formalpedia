-- Prove2me | solution 1 for Algebra.FiniteType.prime_quotient_dimension_formula
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T01:33:53.132038+00:00
-- url     : https://prove2.me/submissions/43b3d9cf-a95e-4858-ba71-5bbb623b3721

import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType

set_option autoImplicit false

theorem solution
(K A : Type*) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (q : Ideal A) (hq : q.IsPrime) :
    ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A  := by
  letI : q.IsPrime := hq
  rw [add_comm]
  exact Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType K q
