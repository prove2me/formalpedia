-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Lit_eval
-- name    : AvgPHETH_Supplement_Lit_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:20.849979+00:00
-- url     : https://prove2.me/theorems/82527fa0-a1ff-4ce7-a8c7-744ed517f357
-- title:
--   Value of a literal
-- statement:
--   Under an assignment $\alpha:V\to\{0,1\}$, the literal $x$ has value $\alpha(x)$, the literal $\neg x$ has value $1-\alpha(x)$, and a constant has its own value.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Lit

namespace AvgPHETH.Supplement

/-- The value of a literal or constant under an assignment `α` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)). -/
def Lit.eval {V : Type} (α : V → Bool) : Lit V → Bool
  | .var v true => α v
  | .var v false => !α v
  | .const b => b

end AvgPHETH.Supplement


