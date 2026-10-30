-- Prove2me | Definitions.Def_ThompsonTutorial_InfoRatio_entropy
-- name    : ThompsonTutorial_InfoRatio_entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:09:01.945633+00:00
-- url     : https://prove2.me/theorems/96013b0e-fd11-4c41-b638-c3abc0d960ed
-- title:
--   Shannon entropy $H(U)$ of a random element
-- statement:
--   Let $U:\Omega\to A$ be a random element on a probability space. Its **entropy** is the mutual information of $U$ with itself,
--   $$
--   H(U)\;=\;I(U;U)\;\in[0,\infty].
--   $$
--   If the law of $U$ is purely atomic with atoms $p_a=\mathbb P(U=a)$, this is the Shannon entropy $H(U)=-\sum_a p_a\log p_a$ in nats. If the law of $U$ has a non-atomic part, $H(U)=+\infty$, in line with the tutorial's remark that "the entropy $H(x^*)$ can become infinite when there are an infinite number of actions". The entropy $H(x^*)$ of the optimal action measures the agent's initial uncertainty about which action is optimal and appears in the regret bound (8.8).
--
--   **Formalization Note** Defined through `mutualInfo`, so no finiteness of the alphabet or counting measure is assumed; values in `ℝ≥0∞`, nats.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), (8.8) "the entropy H(x∗)"; p. 77 (PDF p. 80)

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
open MeasureTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **Shannon entropy `H(U)` of a random element.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), (8.8): "the entropy H(x∗)"; p. 77 (PDF p. 80):
"the entropy H(x∗) can become infinite when there are an infinite number of actions".

`entropy P U = I(U; U)`, the self-information of `U`. For a law with atoms `p_a = P{U = a}` and no
continuous part this is `∑_a −p_a log p_a` (the usual Shannon entropy, in nats); when the law of
`U` has a non-atomic part the joint law of `(U, U)` lives on the diagonal, which the product of
the marginals does not charge, and the value is `⊤` — the paper's infinite entropy.

**Formalization Note.** In `ℝ≥0∞`, nats. Defined through `mutualInfo` so that it is meaningful for
any action set, finite or infinite (no counting measure or finiteness is assumed). The identity
with `∑ −p log p` for a finite alphabet is recorded as a sanity statement outside the mission. -/
noncomputable def entropy {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) (U : Ω → A) : ℝ≥0∞ :=
  mutualInfo P U U

end ThompsonTutorial.InfoRatio


