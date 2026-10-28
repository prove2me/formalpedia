-- Prove2me | Definitions.Def_fd03_ExerciseTree
-- name    : fd03_ExerciseTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:54:13.171488+00:00
-- url     : https://prove2.me/theorems/9d06849b-1f1b-4262-85eb-e45ba6392085
-- title:
--   Finite binary exercise-eligibility and payoff tree
-- statement:
--   An exercise tree of depth N records the maturity payment at every leaf. At each earlier node it records whether exercise is permitted, a signed immediate-exercise reward, and the up/down successor subtrees. American contracts permit exercise everywhere; European contracts permit it at maturity only; Bermudan contracts permit it on a specified schedule.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191, Figure 10.7 and equation (10.17). Original type for finite exercise permissions.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD03

/-- Exercise availability and signed cash reward at each finite node. -/
inductive ExerciseTree : ℕ → Type where
  | maturity : ℝ → ExerciseTree 0
  | node {n : ℕ} : Bool → ℝ → ExerciseTree n → ExerciseTree n →
      ExerciseTree (n + 1)

end FinancialDerivatives.FD03


