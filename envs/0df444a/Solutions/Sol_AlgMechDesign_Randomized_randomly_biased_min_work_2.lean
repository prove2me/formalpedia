-- Prove2me | solution 2 for AlgMechDesign.Randomized.randomly_biased_min_work
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:29.769021+00:00
-- url     : https://prove2.me/submissions/79b24076-2b9f-4654-8548-80bd1dff0d67

import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork
import Theorems.Thm_AlgMechDesign_Randomized_rbmw_strongly_truthful
import Theorems.Thm_AlgMechDesign_Randomized_rbmw_approx

-- carved verbatim out of submission c8fec28c-875b-4d79-9713-84d20f80b38f, lines 272-277

section
open AlgMechDesign.Randomized

theorem solution {k : ℕ} :
    IsUniversallyStronglyTruthful (n := 2) (k := k) (R := Fin k → Fin 2) rbmwAlloc rbmwPay ∧
      ∀ t : Fin 2 → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin 2,
        expMakespan t ≤ 7 / 4 * makespan t y := by
  exact ⟨AlgMechDesign.Randomized.rbmw_strongly_truthful, fun t ht y => AlgMechDesign.Randomized.rbmw_approx t ht y⟩

end
