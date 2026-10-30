-- Prove2me | Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
-- name    : ThompsonTutorial_InfoRatio_condMutualInfo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:08:37.280596+00:00
-- url     : https://prove2.me/theorems/c2e76d09-988a-4358-a5d0-24532a16fd96
-- title:
--   Conditional mutual information $I(U;V\mid Z)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, let $U:\Omega\to A$ and $V:\Omega\to B$ be random elements with values in standard Borel spaces, and let $Z:\Omega\to C$ be a random element with values in any measurable space. Let $P_Z$ be the law of $Z$ and $P_{U\mid Z}$, $P_{V\mid Z}$ the regular conditional distributions of $U$ and of $V$ given $Z$. The **conditional mutual information** of $U$ and $V$ given $Z$ is
--   $$
--   I(U;V\mid Z)\;=\;D\Big(P_{(Z,(U,V))}\,\Big\|\,P_Z\otimes\big(P_{U\mid Z}\otimes P_{V\mid Z}\big)\Big)\;\in[0,\infty],
--   $$
--   the divergence of the true joint law of $(Z,(U,V))$ from the law under which $U$ and $V$ keep their conditional distributions given $Z$ but are conditionally independent. Equivalently, it is the average over $Z$ of the mutual information between $U$ and $V$ under their conditional law given $Z$.
--
--   In the tutorial, $I(x^*;(x_t,y_t)\mid H_{t-1})$ is the expected information about the optimal action $x^*$ gained from the observation of period $t$, and it is the denominator of the information ratio (8.7).
--
--   **Formalization Note** Values in `ℝ≥0∞`, natural logarithm. Conditional laws are Mathlib's `condDistrib`, which requires standard Borel nonempty targets; that is why $A$ and $B$ are standard Borel. The quantity is defined directly, not as a difference of mutual informations.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 75 (PDF p. 78), (8.7): "the conditional mutual information I(x∗; (xt, yt)|Ht−1)"

import Mathlib
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **Conditional mutual information `I(U; V | Z)`.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 75 (PDF p. 78), (8.7): "the conditional mutual information
I(x∗; (xt, yt)|Ht−1) between the uncertain optimal action x∗ and the impending observation
(xt, yt)". The tutorial uses the standard notion without restating it.

`condMutualInfo P U V Z` is the Kullback–Leibler divergence of the joint law of `(Z, (U, V))`
from the measure `P_Z ⊗ (P_{U|Z} × P_{V|Z})`, in which `U` and `V` are made conditionally
independent given `Z` with their true conditional laws:
`I(U; V | Z) = D(P_{(Z,(U,V))} ‖ P_Z ⊗ (P_{U|Z} ⊗ P_{V|Z}))`,
which equals `E_Z[ D(P_{(U,V)|Z} ‖ P_{U|Z} ⊗ P_{V|Z}) ]`, the average over `Z` of the mutual
information of `U` and `V` under the conditional law given `Z`. It is not defined as a difference
of mutual informations.

**Formalization Note.** In `ℝ≥0∞`, in nats (Mathlib's `klDiv`). The conditional laws are Mathlib's
regular conditional distributions `condDistrib`, which exist for standard Borel nonempty targets;
hence `A` and `B` are standard Borel and nonempty, while the conditioning variable `Z` may take
values in any measurable space. Meant for a probability measure `P` and measurable `U`, `V`, `Z`;
every theorem using it carries those hypotheses. -/
noncomputable def condMutualInfo {Ω A B C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C]
    (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → A) (V : Ω → B) (Z : Ω → C) : ℝ≥0∞ :=
  klDiv (P.map (fun ω => (Z ω, (U ω, V ω))))
    ((P.map Z) ⊗ₘ (condDistrib U Z P ×ₖ condDistrib V Z P))

end ThompsonTutorial.InfoRatio


