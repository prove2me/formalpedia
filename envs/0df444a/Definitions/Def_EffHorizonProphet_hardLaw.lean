-- Prove2me | Definitions.Def_EffHorizonProphet_hardLaw
-- name    : EffHorizonProphet_hardLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:12.085035+00:00
-- url     : https://prove2.me/theorems/3fb002e8-6959-4515-81bc-8a52ceb73bf7
-- title:
--   The two-point hard instance
-- statement:
--   The **hard instance** is the two-point law with $Y=n$ with probability $1/n^2$ and $Y=y$ with probability $1-1/n^2$.
--
--   It is the single distribution from which the upper bound of Theorem 1 is derived, with $y$ fixed as $n\to\infty$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Appendix A.2, p.19

import Mathlib

open MeasureTheory

namespace EffHorizonProphet

/-- The **two-point hard instance** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Appendix A.2, p.19): `Y = n` with probability `1/n²` and
`Y = y` with probability `1 - 1/n²`.

**Formalization Note** It is a probability measure for `1 ≤ n`, and admissible for `0 ≤ y` (see the
sanity file). The page takes `y ∈ [0, n)`. -/
noncomputable def hardLaw (n : ℕ) (y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (n : ℝ) ^ 2) • Measure.dirac (n : ℝ) +
    ENNReal.ofReal (1 - 1 / (n : ℝ) ^ 2) • Measure.dirac y

end EffHorizonProphet


