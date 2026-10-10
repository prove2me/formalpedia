-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonPanjer_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:11:13.080459+00:00
-- url     : https://prove2.me/submissions/75067c61-b5e6-4f4f-84a4-392a2dd8c736

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonPanjerStep
import Theorems.Thm_ActuarialValuation_compoundPoissonAggregatePMF_zero
import Theorems.Thm_ActuarialValuation_compoundPoissonAggregatePMF_panjer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (rate : ℝ) (f g : ℕ → ℝ) (hf0 : f 0 = 0)
    (h0 : g 0 = Real.exp (-rate))
    (hstep : ∀ s : ℕ,
      g (s + 1) = compoundPoissonPanjerStep rate f g (s + 1)) :
    ∀ s : ℕ, g s = compoundPoissonAggregatePMF rate f s := by
  intro s
  induction s using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [h0]
          exact (compoundPoissonAggregatePMF_zero rate f hf0).symm
      | succ k =>
          rw [hstep k, compoundPoissonAggregatePMF_panjer rate f k hf0]
          unfold compoundPoissonPanjerStep
          apply congrArg
            (fun x : ℝ => rate / (((k + 1 : ℕ) : ℝ)) * x)
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hj0 : j = 0
          · subst j
            simp
          · have hbound : j ≤ k + 1 := by
              have := Finset.mem_range.mp hj
              omega
            have hsmaller : k + 1 - j < k + 1 := by omega
            rw [ih (k + 1 - j) hsmaller]
