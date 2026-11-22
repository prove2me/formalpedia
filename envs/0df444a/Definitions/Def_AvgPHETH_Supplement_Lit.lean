-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Lit
-- name    : AvgPHETH_Supplement_Lit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:52.511563+00:00
-- url     : https://prove2.me/theorems/34054986-f36d-4186-956c-d658b5da75fa
-- title:
--   Literals and constants
-- statement:
--   A **leaf label** over a set $V$ of Boolean variables is either a literal, $x$ or $\neg x$ for $x\in V$, or a constant $0$ or $1$. Leaves of alternating formulas and input vertices of alternating circuits carry such labels.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)

import Mathlib

namespace AvgPHETH.Supplement

/-- A leaf label of an alternating formula or an input vertex of an alternating circuit: a literal
(`var x true` is `x`, `var x false` is `¬x`) or a constant (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18): "leaves are
labelled by literals or constants"; "Input vertices are labeled by literals or constants"). -/
inductive Lit (V : Type) where
  | var : V → Bool → Lit V
  | const : Bool → Lit V

end AvgPHETH.Supplement


