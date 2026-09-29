-- Prove2me | solution 1 for AlgebraicGeometry.functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/85aa2a64-72b2-56aa-a84a-e1ea0c038aab

import Mathlib
import Theorems.Thm_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isDomain_functionField_tensorProduct_of_isIntegral_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) [IsIntegral X] (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hC : IsIntegral (CategoryTheory.Limits.pullback πX sC)) :
    ∃ hchar : CharZero X.functionField, haveI := hchar;
      ∀ x : X.functionField, IsAlgebraic ℚ x → x ∈ Set.range (algebraMap ℚ X.functionField) := by
  obtain ⟨hchar, hdom⟩ := AlgebraicGeometry.isDomain_functionField_tensorProduct_of_isIntegral_pullback M X πX C sC hC
  refine ⟨hchar, ?_⟩
  intro x hx
  exact IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed X.functionField C hdom x hx

end S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback (solution)
