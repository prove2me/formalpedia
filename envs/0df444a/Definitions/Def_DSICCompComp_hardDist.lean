-- Prove2me | Definitions.Def_DSICCompComp_hardDist
-- name    : DSICCompComp_hardDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:56.759807+00:00
-- url     : https://prove2.me/theorems/7da7e991-6f14-43f8-b54e-345811762b2d
-- title:
--   The hard distribution $D$: law of $a\min\{bZ,1\}+(bZ-1)_+$, $Z\sim\mathcal{ER}$
-- statement:
--   For parameters $a$ and $b$, let $Z \sim \mathcal{ER}$ and let $D$ be the distribution of
--   $$
--   X = a\cdot\min\{bZ, 1\} + (bZ - 1)_+ , \qquad (y)_+ = \max\{y, 0\}.
--   $$
--   In the paper $a \ge 1$ and $b \in (0,1)$. Then $X$ is $abZ \in [ab, a]$ when $bZ \le 1$, and $a + bZ - 1 > a$ otherwise; conditioned on $X \ge a$, $X - (a-1)$ is again distributed as $\mathcal{ER}$. Section 3 uses $D^m$ (all $m$ items iid from $D$) as the distribution that requires many additional bidders.
--
--   **Formalization Note** $D$ is the pushforward of $\mathcal{ER}$ under $z \mapsto a\min\{bz,1\} + \max\{bz-1, 0\}$, read in $\mathbb R_{\ge 0}$; it is defined for all real $a, b$, and the paper's range of $a, b$ enters as hypotheses of the statements.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.2, p.11 (pdf p.12)

import Mathlib
import Definitions.Def_DSICCompComp_erLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DSICCompComp

/-- The hard distribution `D` of §3.2 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of
Additive Buyers over Independent Items*, STOC 2027 submission, manuscript of Nov. 3, 2026,
sha256 bf61bfdb…, §3.2, p.11 (pdf p.12)): the law of the random variable
`a · min{bZ, 1} + (bZ − 1)₊` with `Z ∼ ℰℛ`.

**Formalization Note** It is the pushforward of `erLaw` under
`z ↦ a · min{bz, 1} + max{bz − 1, 0}`, read in `ℝ≥0` through `Real.toNNReal` (the value is
`≥ ab > 0` on the support of `ℰℛ` whenever `a, b > 0`). It is defined for all real `a, b`; the
paper's range `a ≥ 1`, `b ∈ (0, 1)` enters as hypotheses of the statements. It is bundled as a
`ProbabilityMeasure` (the pushforward of a probability measure under a measurable map). -/
noncomputable def hardDist (a b : ℝ) : ProbabilityMeasure ℝ≥0 :=
  ⟨erLaw.map (fun z : ℝ => Real.toNNReal (a * min (b * z) 1 + max (b * z - 1) 0)),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

end DSICCompComp


