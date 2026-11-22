-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Formula_eval
-- name    : AvgPHETH_Supplement_Formula_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:28:28.740507+00:00
-- url     : https://prove2.me/theorems/62bfd1a8-b8b5-49b5-a96f-20da071f37e0
-- title:
--   Value of a formula
-- statement:
--   Under an assignment $\alpha$, a leaf takes the value of its label, an AND gate takes value $1$ iff all its children do, and an OR gate takes value $1$ iff some child does.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Formula
import Definitions.Def_AvgPHETH_Supplement_Lit_eval

namespace AvgPHETH.Supplement

/-- The value of a formula under an assignment `α` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)). -/
def Formula.eval {V : Type} (α : V → Bool) : Formula V → Bool
  | .leaf l => l.eval α
  | .gate true _ ch => decide (∀ i, (ch i).eval α = true)
  | .gate false _ ch => decide (∃ i, (ch i).eval α = true)

end AvgPHETH.Supplement


