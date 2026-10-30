-- Prove2me | Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
-- name    : ThompsonTutorial_InfoRatio_mutualInfo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:08:22.117543+00:00
-- url     : https://prove2.me/theorems/abae437b-f1a2-4ff2-94ac-35a580d7552f
-- title:
--   Mutual information $I(U;V)$ of two random elements
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let $U:\Omega\to A$ and $V:\Omega\to B$ be random elements with values in measurable spaces $A$ and $B$. Write $P_{(U,V)}$ for the joint law of $(U,V)$ and $P_U$, $P_V$ for the marginal laws. The **mutual information** of $U$ and $V$ is the Kullback–Leibler divergence of the joint law from the product of the marginals,
--   $$
--   I(U;V) \;=\; D\big(P_{(U,V)} \,\big\|\, P_U\otimes P_V\big)\;\in[0,\infty].
--   $$
--   It vanishes exactly when $U$ and $V$ are independent and measures, in nats, how much observing $V$ tells about $U$. It is the information quantity in which the tutorial's regret bound (8.8) is expressed.
--
--   **Formalization Note** The value is in $[0,\infty]$ (`ℝ≥0∞`) and uses the natural logarithm (Mathlib's `klDiv`); it equals $+\infty$ when the joint law is not absolutely continuous with respect to the product of the marginals or the log-likelihood ratio is not integrable.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 75 (PDF p. 78), the mutual information I(·;·) used in (8.7) and p. 76 (PDF p. 79)

import Mathlib
open MeasureTheory InformationTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **Mutual information `I(U; V)` of two random elements.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 75 (PDF p. 78), the quantity `I(·;·)` used in (8.7) and on p. 76
(PDF p. 79); the tutorial uses the standard information-theoretic notion without restating it.

`mutualInfo P U V` is the Kullback–Leibler divergence of the joint law of `(U, V)` under `P` from
the product of the marginal laws:
`I(U; V) = D(P_{(U,V)} ‖ P_U ⊗ P_V)`.

**Formalization Note.** The value is in `ℝ≥0∞` and in nats (natural logarithm, Mathlib's
`InformationTheory.klDiv`); it is `⊤` when the joint law is not absolutely continuous with respect
to the product of the marginals or the log-likelihood ratio is not integrable. It is meant for a
probability measure `P` and measurable `U`, `V` (for a non-measurable map, `Measure.map` is `0`);
every theorem using it carries those hypotheses. -/
noncomputable def mutualInfo {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] (P : Measure Ω) (U : Ω → A) (V : Ω → B) : ℝ≥0∞ :=
  klDiv (P.map (fun ω => (U ω, V ω))) ((P.map U).prod (P.map V))

end ThompsonTutorial.InfoRatio


