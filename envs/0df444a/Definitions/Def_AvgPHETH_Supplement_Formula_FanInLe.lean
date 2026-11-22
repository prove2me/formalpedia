-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Formula_FanInLe
-- name    : AvgPHETH_Supplement_Formula_FanInLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:29:41.172153+00:00
-- url     : https://prove2.me/theorems/573e7929-311e-4775-9721-27acd36b7640
-- title:
--   Internal fan-in bound
-- statement:
--   A formula has **all internal fan-ins at most $B$** if every gate has at most $B$ children.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 7.1, p.30 (PDF 32)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Formula

namespace AvgPHETH.Supplement

/-- `F.FanInLe B`: every internal fan-in (number of children of a gate) of `F` is at most `B`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 7.1, p.30 (PDF 32)). -/
def Formula.FanInLe {V : Type} : Formula V → ℕ → Prop
  | .leaf _, _ => True
  | .gate _ m ch, B => m ≤ B ∧ ∀ i, (ch i).FanInLe B

end AvgPHETH.Supplement


