-- Prove2me | Definitions.Def_LearnManip_effEta
-- name    : LearnManip_effEta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:45.587848+00:00
-- url     : https://prove2.me/theorems/f06ac655-1bf7-4eaf-a755-d28c4ec5efa5
-- title:
--   Effective cost growth $\bar\eta=\min(\eta,1)$
-- statement:
--   The effective growth factor
--   $$\bar\eta=\min(\eta,1).$$
--   For $\eta>1$ Theorem 1 says that the solution reduces to the case $\eta=1$, so the closed forms of the mission are written with $\bar\eta$.
--
--   **Formalization Note.** Only the closed forms use $\bar\eta$. The cost rate itself keeps moving by $c\mapsto c\eta$ with the true $\eta$.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Theorem 1, p.15

import Mathlib
import Definitions.Def_LearnManip_Params

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The effective cost growth factor `η̄ = min(η, 1)`: Theorem 1, p.15 of Keppo, Kim, Zhang (SSRN
3465030, 2021-09-04), says that for `η > 1` "the solution reduces to the degenerate case of `η = 1`.
That is, `q*`, `s_TH` and `G` are equivalent to those of the case `η = 1`."

**Formalization Note.** Only the closed forms use `η̄`. The cost rate itself still moves by
`c ↦ c η` with the true `η`. -/
def effEta (P : Params) : ℝ≥0 := min P.η 1

end LearnManip


