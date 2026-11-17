-- Prove2me | Definitions.Def_QuerySampleRev_Supplement_IsPACFor
-- name    : QuerySampleRev_Supplement_IsPACFor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:17:50.107847+00:00
-- url     : https://prove2.me/theorems/b347be8c-fbef-4bce-b012-def3c2a87f0d
-- title:
--   Distribution families and $(\varepsilon,\delta)$-PAC learners for a family
-- statement:
--   Let $\mathcal P$ be a condition on value distributions (regular, MHR, quasi-regular, quasi-MHR). The **family** of $\mathcal P$ consists of the probability measures $\mu$ on $\mathbb R$ with no mass on $(-\infty,0)$, satisfying $\mathcal P$, with finite optimal revenue $r^*=\sup_{p\ge0}pQ(p)$.
--
--   A learner $A$ is **$(\varepsilon,\delta)$-PAC for $\mathcal P$** if for every distribution $F$ of the family,
--   $$
--   \mathbb P_{F,A}\big[A\text{ stops and }R_{\mathrm{pr}}(p^A)\ge(1-\varepsilon)\,r^*\big]\ \ge\ 1-\delta .
--   $$
--   For $\mathcal P$ = quasi-MHR these are the published family and PAC predicate of the mission; the parameter lets the regular, MHR and quasi-regular theorems use the same notion.
--
--   **Formalization Note** A run that never stops has no output and counts as a failure. Revenue and $r^*$ take values in $[0,\infty]$. The ranges $\varepsilon,\delta\in(0,1)$ are hypotheses of the theorems that use the predicate.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF p.13); §2.2, p.13 (PDF p.15), definition of (ε, δ)-PAC

import Mathlib
import Definitions.Def_QuerySampleRev_rStar
import Definitions.Def_QuerySampleRev_transcript
import Definitions.Def_QuerySampleRev_lawP

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **The value distributions of a family.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF 13): "We consider value distributions
supported on `[0, ∞)`"; §2.2, p.13 (PDF 15): "We consider distributions with finite optimal revenue."

`InFamilyOf P μ`: `μ` is a probability measure on `ℝ` with no mass on `(−∞, 0)`, it satisfies the family
condition `P`, and its optimal revenue `r∗` is finite. With `P = IsQuasiMHR` this is the published
`QuerySampleRev.InFamily`. -/
def InFamilyOf (P : Measure ℝ → Prop) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ P μ ∧ rStar μ ≠ ⊤

/-- **(ε, δ)-PAC learner for a family.** Same source, §2.2, p.13 (PDF 15): "For an accuracy parameter
`ε ∈ (0, 1)` and a failure probability `δ ∈ (0, 1)`, we call the algorithm `(ε, δ)`-PAC if, for every
distribution in the specified family, its output satisfies `P_{F,A}[R_pr(p^A) ≥ (1 − ε) r∗] ≥ 1 − δ`."

`IsPACFor P L ε δ`: for every value distribution `μ` of the family `P` (`InFamilyOf P μ`), with probability
at least `1 − δ` under `lawP μ` the learner stops and its output price has revenue at least `(1 − ε) r∗`.
The body is that of the published `QuerySampleRev.IsPAC`, with the family as a parameter.

**Formalization Note.** A run that never stops has no output and counts as a failure. The ranges of `ε`
and `δ` are hypotheses of the theorems that use the predicate. -/
def IsPACFor (P : Measure ℝ → Prop) (L : Learner) (ε δ : ℝ) : Prop :=
  ∀ μ : Measure ℝ, InFamilyOf P μ →
    ENNReal.ofReal (1 - δ) ≤
      lawP μ {ω | stopTime L ω < ⊤ ∧ ENNReal.ofReal (1 - ε) * rStar μ ≤ revenue μ (output L ω)}

end QuerySampleRev.Supplement


