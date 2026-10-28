-- Prove2me | Definitions.Def_fd03_admissible
-- name    : fd03_admissible
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:55:20.212009+00:00
-- url     : https://prove2.me/theorems/65014e02-3619-476d-adb5-84ca3b37b159
-- title:
--   Eligibility of a finite nonanticipating stopping policy
-- statement:
--   A stopping policy is admissible if it may stop before maturity only at nodes explicitly marked as exercise-permitted, and, whenever it continues, both successor policies are admissible. Forced maturity settlement is always admissible. This ensures Bermudan and European schedules are respected.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191, equation (10.17). Original explicit eligibility predicate for nonanticipating American/Bermudan stopping.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_ExerciseTree
import Definitions.Def_fd03_StoppingPolicy

namespace FinancialDerivatives.FD03

/-- A finite stopping policy respects exercise permissions at each node. -/
def admissible : {n : ℕ} → ExerciseTree n → StoppingPolicy n → Prop
  | 0, .maturity _, .maturity => True
  | _ + 1, .node allowed _ _ _, .stop => allowed = true
  | _ + 1, .node _ _ up down, .continue pUp pDown =>
      admissible up pUp ∧ admissible down pDown

end FinancialDerivatives.FD03


