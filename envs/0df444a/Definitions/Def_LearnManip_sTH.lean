-- Prove2me | Definitions.Def_LearnManip_sTH
-- name    : LearnManip_sTH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:52.041783+00:00
-- url     : https://prove2.me/theorems/d67b37e9-5ae1-4468-a4e8-d4c54479e607
-- title:
--   Dissemination threshold $s_{TH}(c)$
-- statement:
--   The threshold of Theorem 1,
--   $$s_{TH}(c)=\sqrt{2\gamma c(1-\alpha)(1-\alpha\bar\eta)},\qquad\bar\eta=\min(\eta,1).$$
--   The firm disseminates at cost rate $c$ exactly when the variance exceeds it, and then brings the variance down to it.
--
--   **Formalization Note.** For $\eta\le1$ this is the printed formula; for $\eta>1$ it is the formula at $\eta=1$, by the last sentence of Theorem 1. The radicand is nonnegative.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Theorem 1, p.15

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_effEta

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The threshold `s_TH(c) = √(2γc(1−α)(1−αη̄))` of Theorem 1, p.15, of Keppo, Kim, Zhang (SSRN
3465030, 2021-09-04), with `η̄ = min(η, 1)`, which is `η` when `η ≤ 1` and `1` when `η > 1` (the
"degenerate case of `η = 1`"). The radicand is nonnegative, since `α < 1` and `η̄ ≤ 1`, so the real
square root is genuine. -/
noncomputable def sTH (P : Params) (c : ℝ≥0) : ℝ≥0 :=
  ⟨Real.sqrt (2 * (P.γ : ℝ) * (c : ℝ) * (1 - (P.α : ℝ)) * (1 - (P.α : ℝ) * (effEta P : ℝ))),
    Real.sqrt_nonneg _⟩

end LearnManip


