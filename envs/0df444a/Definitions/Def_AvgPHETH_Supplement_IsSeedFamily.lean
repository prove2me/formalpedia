-- Prove2me | Definitions.Def_AvgPHETH_Supplement_IsSeedFamily
-- name    : AvgPHETH_Supplement_IsSeedFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:58:00.34483+00:00
-- url     : https://prove2.me/theorems/d9432aaf-25cc-40d1-acd8-237bc138aa3f
-- title:
--   Independent uniform seeds for the restriction rounds
-- statement:
--   The randomness of the oracle construction is modelled by a family of independent random variables, each uniform on $[0,1]$, one for every stage, construction variable and channel. A restriction round is a deterministic function of the seeds of its stage and of the current partial assignment, so the random restrictions of different families, groups and stages are independent, as the construction requires.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 1, pp.40–41 (PDF 42–43); Definition 4.4, p.17 (PDF 19)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar

namespace AvgPHETH.Supplement

/-- The randomness of the oracle construction: a family of independent random variables `U (i, v, c)`,
each uniform on `[0, 1]`, one for every stage `i`, construction variable `v` and channel `c`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 1, pp.40–41 (PDF 42–43): "Independently for each `(k, n)` …
apply a `p_j`-random restriction"; Definition 4.4, p.17 (PDF 19)).

**Formalization Note** `restrictRound` turns the seeds of a stage into its restriction round. Such
families exist on a probability space (e.g. a countable product of copies of `[0,1]`). -/
def IsSeedFamily {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (U : ℕ × CVar × ℕ → Ω → ℝ) : Prop :=
  (∀ a, Measurable (U a)) ∧ ProbabilityTheory.iIndepFun U μ ∧
    ∀ a, μ.map (U a) = MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

end AvgPHETH.Supplement


