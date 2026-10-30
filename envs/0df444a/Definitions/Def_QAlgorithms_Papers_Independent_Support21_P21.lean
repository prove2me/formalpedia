-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P21
-- name    : QAlgorithms_Papers_Independent_Support21_P21
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:28:12.157313+00:00
-- url     : https://prove2.me/theorems/720ed333-45e1-4206-a110-1117b276d126
-- title:
--   prove2quantum library: Papers.Independent.Support21.P21
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Papers.Independent.Support21.P21`), reused by its paper formalizations.
--
--   - `closedStrip`: The closed complex interpolation strip S, arXiv:1609.08462v4, PDF p. 7, equation (9) preamble; also Appendix B, PDF p. 22.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Papers.Independent.Support21.P21

import Mathlib

/-!
Draft artifacts for arXiv:1609.08462v4, Rényi relative entropies and
noncommutative Lp-spaces. All 33 result nodes are explicitly deferred in this
unit's HARD.md and GAPS.json. No matrix specialization or abstract structure
assuming a target conclusion substitutes for the missing operator-algebra
constructions. The definition below is only the source's interpolation strip;
it does not construct a Calderon class or any noncommutative Lp space.
Compilation and independent moderation are pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Support21.P21

/-- The closed complex interpolation strip S, arXiv:1609.08462v4,
PDF p. 7, equation (9) preamble; also Appendix B, PDF p. 22. -/
def closedStrip : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1}

example : (0 : ℂ) ∈ closedStrip := by
  norm_num [closedStrip]

example : (1 : ℂ) ∈ closedStrip := by
  norm_num [closedStrip]

example : Complex.I ∈ closedStrip := by
  norm_num [closedStrip]

end QAlgorithms.Papers.Independent.Support21.P21


