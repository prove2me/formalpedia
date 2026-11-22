-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Formula
-- name    : AvgPHETH_Supplement_Formula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:49.090954+00:00
-- url     : https://prove2.me/theorems/3c5ee78a-f25a-4892-ba84-806fcaff5496
-- title:
--   AND-OR formulas
-- statement:
--   An **AND-OR formula** over variables $V$ is a finite tree whose leaves are labelled by literals or constants and whose internal nodes are AND gates or OR gates, each with a finite ordered list of children. The alternation and layering conditions of §4.3 are imposed separately (`Formula.IsLayeredAlt`).
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Lit

namespace AvgPHETH.Supplement

/-- An AND-OR formula: a tree whose internal nodes are AND gates (`gate true m ch`) or OR gates
(`gate false m ch`) with `m` children `ch 0, …, ch (m-1)`, and whose leaves are labelled by literals
or constants (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)). Alternation and layering are the separate predicate
`Formula.IsLayeredAlt`. -/
inductive Formula (V : Type) where
  | leaf : Lit V → Formula V
  | gate : Bool → (m : ℕ) → (Fin m → Formula V) → Formula V

end AvgPHETH.Supplement


