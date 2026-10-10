-- Prove2me | solution 1 for ActuarialValuation.wholeLifeCompleteInnovation_pathwiseXXIII
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T22:59:50.519088+00:00
-- url     : https://prove2.me/submissions/c82a1de4-16e2-4eef-b3c9-74817b962178

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass
import Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_at
import Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_survivor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (w rho : ℕ → ℝ) (k : ℕ) :
  wholeLifeCompleteInnovation w rho k =
    -(∑ t ∈ Finset.range k, rho t * (w t / wholeLifeTailMass w t)) +
      rho k * (1 - w k / wholeLifeTailMass w k) := by
  classical
  unfold wholeLifeCompleteInnovation wholeLifeFiniteInnovation
  rw [Finset.sum_range_succ]
  have hprefix :
      (∑ t ∈ Finset.range k, rho t * wholeLifeYearInnovation w t k) =
      -(∑ t ∈ Finset.range k, rho t * (w t / wholeLifeTailMass w t)) := by
    calc
      _ = ∑ t ∈ Finset.range k,
          -(rho t * (w t / wholeLifeTailMass w t)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [wholeLifeYearInnovation_survivor w t k (Finset.mem_range.mp ht)]
            ring
      _ = _ := by simp
  rw [hprefix, wholeLifeYearInnovation_at]


