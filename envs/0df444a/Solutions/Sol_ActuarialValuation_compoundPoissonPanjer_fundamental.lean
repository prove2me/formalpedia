-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonPanjer_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:11:54.653284+00:00
-- url     : https://prove2.me/submissions/c887ca7b-b85e-42f9-bed8-a0af4dc305a7

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
    (rate : ℝ) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    (compoundPoissonAggregatePMF rate f 0 = Real.exp (-rate)) ∧
    (∀ s : ℕ, compoundPoissonAggregatePMF rate f (s + 1) =
      compoundPoissonPanjerStep rate f
        (compoundPoissonAggregatePMF rate f) (s + 1)) ∧
    (∀ g : ℕ → ℝ, g 0 = Real.exp (-rate) →
      (∀ s : ℕ, g (s + 1) = compoundPoissonPanjerStep rate f g (s + 1)) →
      ∀ s : ℕ, g s = compoundPoissonAggregatePMF rate f s) := by
  refine ⟨compoundPoissonAggregatePMF_zero rate f hf0,
    (fun s => compoundPoissonAggregatePMF_panjer rate f s hf0), ?_⟩
  intro g h0 hstep s
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
