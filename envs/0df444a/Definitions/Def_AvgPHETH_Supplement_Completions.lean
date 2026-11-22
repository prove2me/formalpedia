-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Completions
-- name    : AvgPHETH_Supplement_Completions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:42:38.185917+00:00
-- url     : https://prove2.me/theorems/fb745d44-df4b-450b-b84b-1634b884aeab
-- title:
--   Total assignments consistent with a partial assignment
-- statement:
--   For a partial assignment $\rho$ to the construction variables, these are the total assignments that agree with $\rho$ on every assigned variable and give every variable a value of its alphabet.
--
--   They are the assignments to the unset construction variables over which the function $f_q$ of step 2(a) is evaluated.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, steps 2(a) and 3(b), p.41 (PDF 43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar_IsValid
import Definitions.Def_AvgPHETH_Supplement_CVar_valLen

namespace AvgPHETH.Supplement

/-- The total assignments to the construction variables that extend the partial assignment `ρ`: every
assigned variable keeps its value and every variable gets a value of its alphabet. These are the
assignments to "the unset construction variables" over which the function `f_q` of step 2(a) ranges
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.41 (PDF 43)). -/
def Completions (ε : ℕ → ℝ) (ρ : CVar → Option (List Bool)) : Set (CVar → List Bool) :=
  {τ | ∀ v : CVar, (∀ b, ρ v = some b → τ v = b) ∧ (v.IsValid ε → (τ v).length = v.valLen ε)}

end AvgPHETH.Supplement


