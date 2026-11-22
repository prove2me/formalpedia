-- Prove2me | Definitions.Def_AvgPHETH_Supplement_rawRestr
-- name    : AvgPHETH_Supplement_rawRestr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:56:00.907955+00:00
-- url     : https://prove2.me/theorems/20700b1c-c21f-4ab4-9e7c-efe5dba91eb9
-- title:
--   The assignment after $i$ restriction rounds
-- statement:
--   The partial assignment to the construction variables obtained by $i$ restriction rounds alone, with no completion step. For a group that has not been completed, this is its state after the restriction round of stage $i$; the event $E_{k,n}$ is defined from it.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_restrictRound

namespace AvgPHETH.Supplement

/-- The partial assignment to the construction variables after `i` restriction rounds and no
completion step (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.40 (PDF 42): "Let `E_{k,n}` be the event that after
`J_k(n)` such restrictions …"). For a group that has not been completed this is its state in the
construction after the restriction round of stage `i`.

**Formalization Note** `U i v c` are the same seeds as in `OracleData.build`. -/
noncomputable def rawRestr (ε : ℕ → ℝ) (U : ℕ → CVar → ℕ → ℝ) : ℕ → CVar → Option (List Bool)
  | 0 => fun _ => none
  | i + 1 => restrictRound ε (U (i + 1)) (fun _ _ => True) (rawRestr ε U i)

end AvgPHETH.Supplement


