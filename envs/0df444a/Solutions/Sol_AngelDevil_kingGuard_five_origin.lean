-- Prove2me | solution 1 for AngelDevil.kingGuard_five_origin
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:22:32.134576+00:00
-- url     : https://prove2.me/submissions/b58425d6-1269-41e7-8006-d17a4ec64324

import Definitions.Def_AngelDevil_KingGuard
import Definitions.Def_AngelDevil_FiniteGame
import Mathlib.Tactic.FinCases

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AngelDevil

theorem kingGuard_five_origin : KingGuard 4 0 ∅ := by
  unfold KingGuard
  refine ⟨⟨5, by decide⟩, ?_⟩
  intro j
  fin_cases j
  · refine ⟨⟨5, by decide⟩, ?_⟩
    intro j
    fin_cases j
    · refine ⟨⟨4, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨4, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
    · refine ⟨⟨4, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨4, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
    · refine ⟨⟨6, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨4, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
  · refine ⟨⟨4, by decide⟩, ?_⟩
    intro j
    fin_cases j
    · refine ⟨⟨4, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨4, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
    · refine ⟨⟨6, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨4, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
    · refine ⟨⟨6, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
  · refine ⟨⟨5, by decide⟩, ?_⟩
    intro j
    fin_cases j
    · refine ⟨⟨4, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨4, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
    · refine ⟨⟨6, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨4, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
    · refine ⟨⟨6, by decide⟩, ?_⟩
      intro j
      fin_cases j
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨5, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
      · refine ⟨⟨6, by decide⟩, ?_⟩
        intro j
        fin_cases j
        · refine ⟨⟨5, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨4, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide
        · refine ⟨⟨6, by decide⟩, ?_⟩
          intro j
          fin_cases j <;> decide

end AngelDevil

theorem solution : AngelDevil.KingGuard 4 0 ∅ := AngelDevil.kingGuard_five_origin
