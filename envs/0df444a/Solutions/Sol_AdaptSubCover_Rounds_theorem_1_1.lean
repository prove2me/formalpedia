-- Prove2me | solution 1 for AdaptSubCover.Rounds.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:01:39.581718+00:00
-- url     : https://prove2.me/submissions/dcdf41d3-ec88-44b3-9359-8e8a4d6a48ce

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Model
import Theorems.Thm_AdaptSubCover_Rounds_theorem_3_2

open AdaptSubCover.Rounds

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → (∃ π : AdaptivePolicy m U, I.Feasible π) → ∀ r : ℕ, 1 ≤ r →
          ∃ σ : RoundPolicy m U, I.FeasibleR r σ ∧
            ∀ π : AdaptivePolicy m U, I.Feasible π →
              I.expCostR r σ ≤
                C * (I.Q : ℝ) ^ ((1 : ℝ) / r) * (1 + Real.log I.Q) * I.expCost π := by
  obtain ⟨C, hC, h⟩ := theorem_3_2
  refine ⟨C, hC, ?_⟩
  intro U _ _ m I hI hfeas r hr
  obtain ⟨⟨σ, hσ⟩, hall⟩ := h U m I hI hfeas r hr
  exact ⟨σ, (hall σ hσ).1, (hall σ hσ).2⟩
