-- Prove2me | Definitions.Def_QuerySampleRev_IsPAC
-- name    : QuerySampleRev_IsPAC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:34.593618+00:00
-- url     : https://prove2.me/theorems/54f9aebe-4451-460d-9d93-1aa9f82e4789
-- title:
--   $(\varepsilon,\delta)$-PAC learner for quasi-MHR distributions
-- statement:
--   A learner is **$(\varepsilon,\delta)$-PAC for the quasi-MHR family** if for every distribution $F$ in the family,
--   $$
--   \mathbb P_{F}\big[\tau<\infty\ \text{and}\ R_{\mathrm{pr}}(p^A)\ge(1-\varepsilon)\,r^*\big]\ \ge\ 1-\delta ,
--   $$
--   where the probability is over the value draws and the learner's internal randomness. The learner must stop and output a price whose revenue is within a factor $1-\varepsilon$ of the optimum, with probability at least $1-\delta$.
--
--   **Formalization Note** A run that never stops has no output and counts as a failure. Revenue and $r^*$ are in $[0,\infty]$. The parameter ranges $\varepsilon\in(0,1)$, $\delta\in(0,1)$ are imposed by the theorems that use the predicate.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF p.15), definition of (ε, δ)-PAC

import Mathlib
import Definitions.Def_QuerySampleRev_InFamily
import Definitions.Def_QuerySampleRev_transcript
import Definitions.Def_QuerySampleRev_lawP

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **(ε, δ)-PAC learner for the quasi-MHR family.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for
Revenue Maximization* (manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF 15): "For an accuracy parameter
`ε ∈ (0, 1)` and a failure probability `δ ∈ (0, 1)`, we call the algorithm `(ε, δ)`-PAC if, for every
distribution in the specified family, its output satisfies `P_{F,A}[R_pr(p^A) ≥ (1 − ε) r∗] ≥ 1 − δ`."

`IsPAC L ε δ`: for every quasi-MHR value distribution `μ` (`InFamily μ`), with probability at least
`1 − δ` under `lawP μ` the learner stops and its output price `p^A` has revenue at least `(1 − ε) r∗`.

**Formalization Note.** "At termination, the algorithm outputs a price `p^A`" (§2.2): a run that never
stops has no output and counts as a failure. Revenue and `r∗` are in `ℝ≥0∞`. -/
def IsPAC (L : Learner) (ε δ : ℝ) : Prop :=
  ∀ μ : Measure ℝ, InFamily μ →
    ENNReal.ofReal (1 - δ) ≤
      lawP μ {ω | stopTime L ω < ⊤ ∧ ENNReal.ofReal (1 - ε) * rStar μ ≤ revenue μ (output L ω)}

end QuerySampleRev


